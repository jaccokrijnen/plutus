{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
module Language.PlutusTx.Plugin (plugin, plc) where

import           Data.Bifunctor
import           Language.PlutusTx.Code
import           Language.PlutusTx.Compiler.Builtins
import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Expr
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import           Language.PlutusTx.PIRTypes
import           Language.PlutusTx.PLCTypes
import           Language.PlutusTx.Plugin.Utils

import qualified GhcPlugins                             as GHC
import qualified Panic                                  as GHC

import qualified Language.PlutusCore                    as PLC
import           Language.PlutusCore.Pretty             as PLC
import           Language.PlutusCore.Quote

import qualified Language.UntypedPlutusCore             as UPLC

import qualified Language.PlutusIR                      as PIR
import qualified Language.PlutusIR.Compiler             as PIR
import qualified Language.PlutusIR.Compiler.Definitions as PIR

import           Language.Haskell.TH.Syntax             as TH hiding (lift)

import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Flat                                   (flat)

import qualified Data.ByteString                        as BS
import qualified Data.ByteString.Unsafe                 as BSUnsafe
import           Data.List                              as List
import           Data.List.NonEmpty                     as NonEmpty
import qualified Data.Map                               as Map
import           Data.Proxy
import qualified Data.Text                              as T
import qualified Data.Text.Prettyprint.Doc              as PP
import           Data.Traversable
import           ErrorCode
import qualified FamInstEnv                             as GHC

import           System.IO.Unsafe                       (unsafePerformIO)

data PluginOptions = PluginOptions {
    poDoTypecheck    :: Bool
    , poDeferErrors  :: Bool
    , poContextLevel :: Int
    , poDumpPir      :: Bool
    , poDumpPlc      :: Bool
    , poOptimize     :: Bool
    }

data PluginCtx = PluginCtx
    { pcOpts       :: PluginOptions
    , pcFamEnvs    :: GHC.FamInstEnvs
    , pcMarkerName :: GHC.Name
    }

{- Note [Making sure unfoldings are present]
Our plugin runs at the start of the Core pipeline. If we look around us, we will find
that as expected, we have unfoldings for some bindings from other modules or packages
depending on whether GHC thinks they're good to inline/are marked INLINEABLE.

But there will be no unfoldings for local bindings!

It turns out that these are added by the simplifier, of all things. To avoid relying too
much on the shape of the subsequent passes, we add a single, very gentle, simplifier
pass before we run, turning off everything that we can and running only once.

This means that we need to be robust to the transformations that the simplifier performs
unconditionally which we pretty much are.

See https://gitlab.haskell.org/ghc/ghc/issues/16615 for upstream discussion.
-}

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.pluginRecompile = GHC.flagRecompile
                           , GHC.installCoreToDos = install
                           }
    where
      install :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
      install args rest = do
          -- create simplifier pass to be placed at the front
          simplPass <- mkSimplPass <$> GHC.getDynFlags
          -- instantiate our plugin pass
          pluginPass <- mkPluginPass <$> parsePluginArgs args
          -- return the pipeline
          pure $
             simplPass
             : pluginPass
             : rest

-- | A simplifier pass, implemented by GHC
mkSimplPass :: GHC.DynFlags -> GHC.CoreToDo
mkSimplPass flags =
  -- See Note [Making sure unfoldings are present]
  GHC.CoreDoSimplify 1 $ GHC.SimplMode {
              GHC.sm_names = ["Ensure unfoldings are present"]
            , GHC.sm_phase = GHC.InitialPhase
            , GHC.sm_dflags = flags
            , GHC.sm_rules = False
            -- You might think you would need this, but apparently not
            , GHC.sm_inline = False
            , GHC.sm_case_case = False
            , GHC.sm_eta_expand = False
            }

-- | Parses the arguments that were given to ghc at commandline as "-fplugin-optLanguage.PlutusTx.Plugin:arg1"
parsePluginArgs :: [GHC.CommandLineOption] -> GHC.CoreM PluginOptions
parsePluginArgs args = do
    let opts = PluginOptions {
            poDoTypecheck = notElem "dont-typecheck" args
            , poDeferErrors = elem "defer-errors" args
            , poContextLevel = if elem "no-context" args then 0 else if elem "debug-context" args then 3 else 1
            , poDumpPir = elem "dump-pir" args
            , poDumpPlc = elem "dump-plc" args
            , poOptimize = notElem "dont-optimize" args
            }
    -- TODO: better parsing with failures
    pure opts

{- Note [Marker resolution]
We use TH's 'foo exact syntax for resolving the 'plc marker's ghc name, as
explained in: <http://hackage.haskell.org/package/ghc-8.10.1/docs/GhcPlugins.html#v:thNameToGhcName>

The GHC haddock suggests that the "exact syntax" will always succeed because it is statically resolved here (inside this Plugin module);

If this is the case, then it means that our plugin will always traverse each module's binds searching for plc markers
even in the case that the `plc` name is not in scope locally in the module under compilation.

The alternative is to use the "dynamic syntax" (`TH.mkName "plc"`), which implies that
the "plc" name will be resolved dynamically during module's compilation. In case "plc" is not locally in scope,
the plugin would finish faster by completely skipping the module under compilation. This dynamic approach
comes with its own downsides however, because the user may have imported "plc" qualified or aliased it, which will fail to resolve.
-}


-- | Our plugin works at haskell-module level granularity; the plugin
-- looks at the module's top-level bindings for plc markers and compiles their right-hand-side core expressions.
mkPluginPass :: PluginOptions -> GHC.CoreToDo
mkPluginPass opts = GHC.CoreDoPluginPass "Core to PLC" $ \ guts -> do
    -- Family env code borrowed from SimplCore
    p_fam_env <- GHC.getPackageFamInstEnv
    -- See Note [Marker resolution]
    maybeMarkerName <- GHC.thNameToGhcName 'plc
    case maybeMarkerName of
        -- TODO: test that this branch can happen using TH's 'plc exact syntax. See Note [Marker resolution]
        Nothing -> pure guts
        Just markerName ->
            let pctx = PluginCtx { pcOpts = opts
                                 , pcFamEnvs = (p_fam_env, GHC.mg_fam_inst_env guts)
                                 , pcMarkerName = markerName
                                 }
                -- start looking for plc calls from the top-level binds
            in GHC.bindsOnlyPass (runPluginM pctx . traverse compileBind) guts

-- | The monad where the plugin runs in for each module.
-- It is a core->core compiler monad, called PluginM, augmented with pure errors.
type PluginM uni fun = ReaderT PluginCtx (ExceptT (CompileError uni fun) GHC.CoreM)

-- | Runs the plugin monad in a given context; throws a Ghc.Exception when compilation fails.
runPluginM :: (PLC.GShow uni, PLC.Closed uni, PLC.Everywhere uni PLC.PrettyConst, PP.Pretty fun)
           => PluginCtx -> PluginM uni fun a -> GHC.CoreM a
runPluginM pctx act = do
    res <- runExceptT $ runReaderT act pctx
    case res of
        Right x -> pure x
        Left err ->
            let errInGhc = GHC.ProgramError $ "GHC Core to PLC plugin: " ++ show (PP.pretty (errorCode err) <> ":" <> PP.pretty err)
            in liftIO $ GHC.throwGhcExceptionIO errInGhc

-- | Compiles all the marked expressions in the given binder into PLC literals.
compileBind :: GHC.CoreBind -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreBind
compileBind = \case
    GHC.NonRec b rhs -> GHC.NonRec b <$> compileMarkedExprs rhs
    GHC.Rec bindsRhses -> GHC.Rec <$> (for bindsRhses $ \(b, rhs) -> do
                                             rhs' <- compileMarkedExprs rhs
                                             pure (b, rhs'))

{- Note [Hooking in the plugin]
Working out what to process and where to put it is tricky. We are going to turn the result in
to a 'CompiledCode', not the Haskell expression we started with!

Currently we look for calls to the @plc :: a -> CompiledCode a@ function, and we replace the whole application with the
generated code object, which will still be well-typed.
-}

{- Note [Polymorphic values and Any]
If you try and use the plugin on a polymorphic expression, then GHC will replace the quantified types
with 'Any' and remove the type lambdas. This is pretty annoying, and I don't entirely understand
why it happens, despite poking around in GHC a fair bit.

Possibly it has to do with the type that is given to 'plc' being unconstrained, resulting in GHC
putting 'Any' there, and that then propagating into the type of the quote. It's tricky to experiment
with this, since you can't really specify a polymorphic type in a type application or in the resulting
'CompiledCode' because that's impredicative polymorphism.
-}

-- | Compiles all the core-expressions surrounded by plc in the given expression into PLC literals.
compileMarkedExprs :: GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprs expr = do
    markerName <- asks pcMarkerName
    case expr of
      GHC.App (GHC.App (GHC.App (GHC.App
                          -- function id
                          -- sometimes GHCi sticks ticks around this for some reason
                          (stripTicks -> (GHC.Var fid))
                          -- first type argument, must be a string literal type
                          (GHC.Type (GHC.isStrLitTy -> Just fs_locStr)))
                     -- second type argument
                     (GHC.Type codeTy))
            _)
            -- value argument
            inner
          | markerName == GHC.idName fid -> compileMarkedExprOrDefer (show fs_locStr) codeTy inner
      e@(GHC.Var fid) | markerName == GHC.idName fid -> throwError . NoContext . InvalidMarkerError . GHC.showSDocUnsafe $ GHC.ppr e
      GHC.App e a -> GHC.App <$> compileMarkedExprs e <*> compileMarkedExprs a
      GHC.Lam b e -> GHC.Lam b <$> compileMarkedExprs e
      GHC.Let bnd e -> GHC.Let <$> compileBind bnd <*> compileMarkedExprs e
      GHC.Case e b t alts -> do
            e' <- compileMarkedExprs e
            let expAlt (a, bs, rhs) = (,,) a bs <$> compileMarkedExprs rhs
            alts' <- mapM expAlt alts
            pure $ GHC.Case e' b t alts'
      GHC.Cast e c -> flip GHC.Cast c <$> compileMarkedExprs e
      GHC.Tick t e -> GHC.Tick t <$> compileMarkedExprs e
      e@(GHC.Coercion _) -> pure e
      e@(GHC.Lit _) -> pure e
      e@(GHC.Var _) -> pure e
      e@(GHC.Type _) -> pure e

-- | Behaves the same as 'compileMarkedExpr', unless a compilation error occurs ;
-- if a compilation error happens and the 'defer-errors' option is turned on,
-- the compilation error is supressed and the original hs expression is replaced with a
-- haskell runtime-error expression.
compileMarkedExprOrDefer :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExprOrDefer locStr codeTy origE = do
    opts <- asks pcOpts
    let compileAct = compileMarkedExpr locStr codeTy origE
    if poDeferErrors opts
      -- TODO: we could perhaps move this catchError to the "runExceptT" module-level, but
      -- it leads to uglier code and difficulty of handling other pure errors
      then compileAct `catchError` emitRuntimeError codeTy
      else compileAct

-- | Given an expected Haskell type 'a', it generates Haskell code which throws a GHC runtime error "as" 'CompiledCode a'.
emitRuntimeError :: (PLC.GShow uni, PLC.Closed uni, PP.Pretty fun, PLC.Everywhere uni PLC.PrettyConst)
                 => GHC.Type -> CompileError uni fun -> PluginM uni fun GHC.CoreExpr
emitRuntimeError codeTy e = do
    opts <- asks pcOpts
    let shown = show $ PP.pretty (pruneContext (poContextLevel opts) e)
    tcName <- thNameToGhcNameOrFail ''CompiledCode
    tc <- lift . lift $ GHC.lookupTyCon tcName
    pure $ GHC.mkRuntimeErrorApp GHC.rUNTIME_ERROR_ID (GHC.mkTyConApp tc [codeTy]) shown

-- | Compile the core expression that is surrounded by a 'plc' marker,
-- and return a core expression which evaluates to the compiled plc AST as a serialized bytestring,
-- to be injected back to the Haskell program.
compileMarkedExpr :: String -> GHC.Type -> GHC.CoreExpr -> PluginM PLC.DefaultUni PLC.DefaultFun GHC.CoreExpr
compileMarkedExpr locStr codeTy origE = do
    flags <- GHC.getDynFlags
    famEnvs <- asks pcFamEnvs
    opts <- asks pcOpts
    -- We need to do this out here, since it has to run in CoreM
    nameInfo <- makePrimitiveNameInfo builtinNames
    let ctx = CompileContext {
            ccOpts = CompileOptions {},
            ccFlags = flags,
            ccFamInstEnvs = famEnvs,
            ccBuiltinNameInfo = nameInfo,
            ccScopes = initialScopeStack,
            ccBlackholed = mempty
            }

    (pirP,uplcP) <- runQuoteT . flip runReaderT ctx $ withContextM 1 (sdToTxt $ "Compiling expr at" GHC.<+> GHC.text locStr) $ runCompiler opts origE

    -- serialize the PIR and PLC outputs into a bytestring.
    bsPir <- makeByteStringLiteral $ flat pirP
    bsPlc <- makeByteStringLiteral $ flat uplcP

    builder <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'mkCompiledCode

    -- inject the two bytestrings back as Haskell code.
    pure $
        GHC.Var builder
        `GHC.App` GHC.Type codeTy
        `GHC.App` bsPlc
        `GHC.App` bsPir

-- | The GHC.Core to PIR to PLC compiler pipeline. Returns both the PIR and PLC output.
-- It invokes the whole compiler chain:  Core expr -> PIR expr -> PLC expr -> UPLC expr.
runCompiler
    :: forall uni fun m . (uni ~ PLC.DefaultUni, fun ~ PLC.DefaultFun, MonadReader (CompileContext uni fun) m, MonadQuote m, MonadError (CompileError uni fun) m, MonadIO m)
    => PluginOptions
    -> GHC.CoreExpr
    -> m (PIRProgram uni fun, UPLCProgram uni fun)
runCompiler opts expr = do
    -- Plc configuration
    plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance

    -- Pir configuration
    let pirTcConfig = if poDoTypecheck opts
                      -- pir's tc-config is based on plc tcconfig
                      then Just $ PIR.PirTCConfig plcTcConfig PIR.YesEscape
                      else Nothing
        pirCtx = PIR.toDefaultCompilationCtx plcTcConfig
                 & set (PIR.ccOpts . PIR.coOptimize) (poOptimize opts)
                 & set PIR.ccTypeCheckConfig pirTcConfig

    let phase name = "\n" ++ replicate 20 '=' ++ " " ++ name ++ replicate 20 '=' ++ "\n"
    -- let dumpPLC name ast = liftIO . putStrLn $ phase name ++ (show (PP.pretty ast))
    -- let dumpPIR name ast = liftIO . putStrLn $ phase name ++ (show ast)
    let dumpPIR' name ast = liftIO . putStrLn $ phase name ++ toCoq ast

    -- GHC.Core -> Pir translation.
    pirT <- PIR.runDefT () $ compileExprWithDefs expr
    when (poDumpPir opts) $ dumpPIR' "PIR" pirT

    -- Pir -> (Simplified) Pir pass. We can then dump/store a more legible PIR program.
    (spirT, PIR.CompilationTrace t_0 passes) <- flip runReaderT pirCtx $ PIR.compileToReadable' pirT
    let spirP = PIR.Program () . void $ spirT

    -- (Simplified) Pir -> Plc translation.
    (plcT, passes') <- flip runReaderT pirCtx $ PIR.compileReadableToPlc' spirT

    let writeTrace toString file =
          liftIO . writeFile file . toString $ PIR.CompilationTrace t_0 (passes ++ passes')

    when (poDumpPir opts) $ do
      writeTrace toCoq "compilation-trace"
      writeTrace dumpTracePretty "compilation-trace-readable"

    let plcP = PLC.Program () (PLC.defaultVersion ()) $ void plcT
    -- when (poDumpPlc opts) $ dumpPLC "PLC (Program)" plcP

    -- We do this after dumping the programs so that if we fail typechecking we still get the dump.
    when (poDoTypecheck opts) . void $
        liftExcept $ PLC.typecheckPipeline plcTcConfig plcP

    uplcP <- liftExcept $ UPLC.deBruijnProgram $ UPLC.eraseProgram plcP
    pure (spirP, uplcP)

  where
      -- ugly trick to take out the concrete plc.error and in case of error, map it / rethrow it using our 'CompileError'
      liftExcept :: ExceptT (PLC.Error PLC.DefaultUni PLC.DefaultFun ()) m b -> m b
      liftExcept act = do
        plcTcError <- runExceptT act
        -- also wrap the PLC Error annotations into Original provenances, to match our expected 'CompileError'
        liftEither $ first (view (re PIR._PLCError) . fmap PIR.Original) plcTcError

class ToCoq a where
  toCoq :: a -> String

apps :: String -> [String] -> String
apps f xs = List.intercalate " " (f : fmap parens xs)
  where parens x = "(" ++ x ++ ")"

-- TODO: Write these instances with generics
instance
  ( ToCoq name
  , ToCoq tyname
  , ToCoq fun
  , forall b. ToCoq (uni b)
  , PLC.Closed uni
  , PLC.Everywhere uni ToCoq
  ) =>
  ToCoq (PIR.Term name tyname uni fun a) where
  toCoq = \case
    PIR.Let _ rec bindings t  -> apps "Let"    [toCoq rec, toCoq bindings, toCoq t]
    PIR.Var _ name            -> apps "Var"    [toCoq name]
    PIR.TyAbs _ tyname kind t -> apps "TyAbs"  [toCoq tyname, toCoq kind, toCoq t]
    PIR.LamAbs _ name ty t    -> apps "LamAbs" [toCoq name, toCoq ty, toCoq t]
    PIR.Apply _ t1 t2         -> apps "Apply"  [toCoq t1, toCoq t2]
    PIR.Constant _ val        -> apps "Constant" [toCoq val]
    PIR.Builtin _ fun         -> apps "Builtin" [toCoq fun]
    PIR.TyInst _ term ty      -> apps "TyInst" [toCoq term, toCoq ty]
    PIR.Error _ ty            -> apps "Error" [toCoq ty]
    PIR.IWrap _ ty1 ty2 t     -> apps "IWrap" [toCoq ty1, toCoq ty2, toCoq t]
    PIR.Unwrap _ t            -> apps "Unwrap" [toCoq t]

instance (forall a. ToCoq (f a)) => ToCoq (PLC.Some f) where
  toCoq (PLC.Some x) = apps "Some" [toCoq x]
instance (ToCoq (uni a), PLC.Closed uni, PLC.Everywhere uni ToCoq) => ToCoq (PLC.ValueOf uni a) where
  toCoq (PLC.ValueOf uni x) = PLC.bring (Proxy @ToCoq) uni $ apps "ValueOf" [toCoq uni, toCoq x] -- (PLC.ValueOf ev x) = apps "ValueOf" [toCoq ev, toCoq x]

instance ToCoq (PLC.DefaultUni a) where
  toCoq PLC.DefaultUniInteger    = "DefaultUniInteger"
  toCoq PLC.DefaultUniByteString = "DefaultUniByteString"
  toCoq PLC.DefaultUniString     = "DefaultUniString"
  toCoq PLC.DefaultUniChar       = "DefaultUniChar"
  toCoq PLC.DefaultUniUnit       = "DefaultUniUnit"
  toCoq PLC.DefaultUniBool       = "DefaultUniBool"

instance ToCoq Bool where
  toCoq True  = "true"
  toCoq False = "false"

instance ToCoq () where toCoq () = "tt"
instance ToCoq T.Text where toCoq = show
instance ToCoq String where toCoq = show
instance ToCoq Int where toCoq = show
instance ToCoq Integer where toCoq = show
instance ToCoq Char where toCoq = show
instance ToCoq BS.ByteString where toCoq = show

instance (ToCoq tyname, ToCoq name, ToCoq fun, PLC.Closed uni, PLC.Everywhere uni ToCoq, forall b. ToCoq (uni b)) =>
  ToCoq (PIR.Binding tyname name uni fun a) where
  toCoq (PIR.TermBind _ strictness vdecl t) = apps "TermBind"     [toCoq strictness, toCoq vdecl, toCoq t]
  toCoq (PIR.TypeBind _ tvdecl ty)          = apps "TypeBind"     [toCoq tvdecl, toCoq ty]
  toCoq (PIR.DatatypeBind _ dt)             = apps "DatatypeBind" [toCoq dt]
instance (ToCoq name, ToCoq tyname, PLC.Closed uni, PLC.Everywhere uni ToCoq, forall b. ToCoq (uni b)) => ToCoq (PIR.VarDecl tyname name uni fun a) where
  toCoq (PIR.VarDecl _ name ty) = apps "VarDecl" [toCoq name, toCoq ty]
instance (ToCoq tyname) => ToCoq (PIR.TyVarDecl tyname a) where
  toCoq (PIR.TyVarDecl _ name kind) = apps "TyVarDecl" [toCoq name, toCoq kind]

-- Awful newtype workaround to expose the arity of constructors
-- (need this to verify Scott encoding)
newtype Constructor tyname name uni fun a = Constructor (PIR.VarDecl tyname name uni fun a)

instance (ToCoq tyname, ToCoq name, PLC.Everywhere uni ToCoq, PLC.Closed uni, forall b. ToCoq (uni b)) => ToCoq (Constructor tyname name uni fun a) where
  toCoq (Constructor vd@(PIR.VarDecl _ name ty)) = apps "Constructor" [toCoq vd, toCoq (arity ty)]
    where
      arity :: PIR.Type tyname uni a -> Int
      arity (PIR.TyFun _ _a b) = 1 + arity b
      arity _                  = 0

instance (ToCoq name, ToCoq tyname, forall b. ToCoq (uni b), PLC.Closed uni, PLC.Everywhere uni ToCoq) => ToCoq (PIR.Datatype tyname name uni fun a) where
  toCoq (PIR.Datatype _ tvdecl tvdecls name constructors) = apps "Datatype" [toCoq tvdecl, toCoq tvdecls, toCoq name, toCoq (List.map Constructor constructors)]
instance ToCoq (PLC.TyName) where toCoq (PLC.TyName name) = apps "TyName" [toCoq name]


instance ToCoq a => ToCoq (NonEmpty.NonEmpty a) where
  toCoq (x NonEmpty.:| xs) = apps "cons" [toCoq x, toCoq xs]

instance {-# OVERLAPPABLE #-} ToCoq a => ToCoq [a] where
  toCoq []     = "nil"
  toCoq (x:xs) = apps "cons" [toCoq x, toCoq xs]
instance (ToCoq a, ToCoq b) => ToCoq (a, b) where
  toCoq (a, b) = "(" ++ toCoq a ++ "," ++ toCoq b ++ ")"

instance ToCoq PLC.Name where toCoq (PLC.Name str uniq) = apps "Name" [toCoq str, toCoq uniq]
instance ToCoq PLC.Unique where toCoq (PLC.Unique n) = apps "Unique" [toCoq n]
instance ToCoq PLC.DefaultFun where toCoq = show
instance ToCoq PIR.Strictness where toCoq = show
instance ToCoq PIR.Recursivity where toCoq = show

instance ToCoq (PIR.Kind ann) where
  toCoq (PIR.Type _) = "Kind_Base"
  toCoq (PIR.KindArrow _ k1 k2) = apps "Kind_Arrow" [toCoq k1, toCoq k2]

instance (ToCoq tyname, PLC.Closed uni, PLC.Everywhere uni ToCoq, forall a. ToCoq (uni a)) => ToCoq (PIR.Type tyname uni ann) where
  toCoq (PIR.TyVar _ tyname) = apps "Ty_Var" [toCoq tyname]
  toCoq (PIR.TyFun _ ty1 ty2) = apps "Ty_Fun" [toCoq ty1, toCoq ty2]
  toCoq (PIR.TyIFix _ ty1 ty2) = apps "Ty_IFix" [toCoq ty1, toCoq ty2]
  toCoq (PIR.TyForall _ tyname k ty) =
    apps "Ty_Forall" [toCoq tyname, toCoq k, toCoq ty]
  toCoq (PIR.TyBuiltin _ some) = apps "Ty_Builtin" [toCoq some]
  toCoq (PIR.TyLam _ tyname k ty) = apps "Ty_Lam" [toCoq tyname, toCoq k , toCoq ty]
  toCoq (PIR.TyApp _ ty1 ty2) = apps "Ty_App" [toCoq ty1, toCoq ty2]

{-
instance (forall a. ToCoq (f a)) => ToCoq (PLC.Some f) where
  toCoq (PLC.Some x) = apps "Some" [toCoq x]
instance (ToCoq (uni a), PLC.Closed uni, PLC.Everywhere uni ToCoq) => ToCoq (PLC.ValueOf uni a) where
  toCoq (PLC.ValueOf uni x) = PLC.bring (Proxy @ToCoq) uni $ apps "ValueOf" [toCoq uni, toCoq x] -- (PLC.ValueOf ev x) = apps "ValueOf" [toCoq ev, toCoq x]
-}

instance (ToCoq (uni a), PLC.Closed uni, PLC.Everywhere uni ToCoq) => ToCoq (PLC.TypeIn uni a) where
  toCoq (PLC.TypeIn u) = apps "TypeIn" [toCoq u]

instance ToCoq PIR.Pass where
  toCoq PIR.PassRename         = "PassRename"
  toCoq PIR.PassTypeCheck      = "PassTypeCheck"
  toCoq (PIR.PassInline names) = apps "PassInline" [toCoq names]
  toCoq PIR.PassDeadCode       = "PassDeadCode"
  toCoq PIR.PassThunkRec       = "PassThunkRec"
  toCoq PIR.PassFloatTerm      = "PassFloatTerm"
  toCoq PIR.PassLetNonStrict   = "PassLetNonStrict"
  toCoq PIR.PassLetTypes       = "PassLetTypes"
  toCoq PIR.PassLetRec         = "PassLetRec"
  toCoq PIR.PassLetNonRec      = "PassLetNonRec"


instance
  ( PLC.Everywhere uni ToCoq
  , PLC.Closed uni
  , ToCoq fun
  , forall b. ToCoq (uni b)
  )
  => ToCoq (PIR.CompilationTrace uni fun a) where
  toCoq (PIR.CompilationTrace t0 passes) = apps "CompilationTrace" [toCoq t0, toCoq passes]

dumpTracePretty :: PIR.CompilationTrace PLC.DefaultUni PLC.DefaultFun () -> String
dumpTracePretty (PIR.CompilationTrace t0 passes) = unlines . List.intersperse "" $ strs
  where
    strs = pp t0 : concat [ [show pass, pp res] | (pass, res) <- passes]
    pp = show . PP.pretty

-- | Get the 'GHC.Name' corresponding to the given 'TH.Name', or throw an error if we can't get it.
thNameToGhcNameOrFail :: TH.Name -> PluginM uni fun GHC.Name
thNameToGhcNameOrFail name = do
    maybeName <- lift . lift $ GHC.thNameToGhcName name
    case maybeName of
        Just n  -> pure n
        Nothing -> throwError . NoContext $ CoreNameLookupError name

-- | Create a GHC Core expression that will evaluate to the given ByteString at runtime.
makeByteStringLiteral :: BS.ByteString -> PluginM uni fun GHC.CoreExpr
makeByteStringLiteral bs = do
    flags <- GHC.getDynFlags

    {-
    This entire section will crash horribly in a number of circumstances. Such is life.
    - If any of the names we need can't be found as GHC Names
    - If we then can't look up those GHC Names to get their IDs/types
    - If we make any mistakes creating the Core expression
    -}

    -- Get the names of functions/types that we need for our expression
    upio <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'unsafePerformIO
    bsTc <- lift . lift . GHC.lookupTyCon =<< thNameToGhcNameOrFail ''BS.ByteString
    upal <- lift . lift . GHC.lookupId =<< thNameToGhcNameOrFail 'BSUnsafe.unsafePackAddressLen

    -- We construct the following expression:
    -- unsafePerformIO $ unsafePackAddressLen <length as int literal> <data as string literal address>
    -- This technique gratefully borrowed from the file-embed package

    -- The flags here are so GHC can check whether the int is in range for the current platform.
    let lenLit = GHC.mkIntExpr flags $ fromIntegral $ BS.length bs
    -- This will have type Addr#, which is right for unsafePackAddressLen
    let bsLit = GHC.Lit (GHC.LitString bs)
    let upaled = GHC.mkCoreApps (GHC.Var upal) [lenLit, bsLit]
    let upioed = GHC.mkCoreApps (GHC.Var upio) [GHC.Type (GHC.mkTyConTy bsTc), upaled]

    pure upioed

-- | Strips all enclosing 'GHC.Tick's off an expression.
stripTicks :: GHC.CoreExpr -> GHC.CoreExpr
stripTicks = \case
    GHC.Tick _ e -> stripTicks e
    e            -> e

-- | Helper to avoid doing too much construction of Core ourselves
mkCompiledCode :: forall a . BS.ByteString -> BS.ByteString -> CompiledCode a
mkCompiledCode plcBS pirBS = SerializedCode plcBS (Just pirBS)

-- | Make a 'BuiltinNameInfo' mapping the given set of TH names to their
-- 'GHC.TyThing's for later reference.
makePrimitiveNameInfo :: [TH.Name] -> PluginM uni fun BuiltinNameInfo
makePrimitiveNameInfo names = do
    infos <- for names $ \name -> do
        ghcName <- thNameToGhcNameOrFail name
        thing <- lift . lift $ GHC.lookupThing ghcName
        pure (name, thing)
    pure $ Map.fromList infos
