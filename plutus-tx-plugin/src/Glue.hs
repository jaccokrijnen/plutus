{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
module Glue where

import qualified Extracted           as E
import qualified Language.PlutusCore as P (DefaultFun (..), DefaultUni (..), Some (..), TypeIn (..), ValueOf (..))
import qualified Language.PlutusIR   as P

import           Data.Char
import           Data.List.NonEmpty
import           Data.Text

type EString = E.String

type Term a = P.Term P.TyName P.Name P.DefaultUni P.DefaultFun a
type ETerm = E.Term EString EString EString EString

type Binding a = P.Binding P.TyName P.Name P.DefaultUni P.DefaultFun a
type EBinding = E.Binding EString EString EString EString

type PDatatype a = P.Datatype P.TyName P.Name P.DefaultUni P.DefaultFun a
type EDatatype = E.Dtdecl EString EString EString

type Type a = P.Type P.TyName P.DefaultUni a
type EType = E.Ty EString EString

type Kind a = P.Kind a
type EKind = E.Kind

type PVarDecl a = P.VarDecl P.TyName P.Name P.DefaultUni P.DefaultFun a
type EVarDecl = E.Vdecl EString EString EString

type PTyVarDecl a = P.TyVarDecl P.TyName a
type ETyVarDecl = E.Tvdecl EString
type EConstr = E.Constr EString EString EString

glueString :: String -> EString
glueString = Prelude.foldr (E.String0 . charToAscii) E.EmptyString

intToNat :: Int -> E.Nat
intToNat 0 = E.O
intToNat n
  | n < 0 = error "intToNat: negative Int"
  | otherwise = E.S (intToNat (n - 1))

charToAscii :: Char -> E.Ascii0
charToAscii = E.ascii_of_nat . intToNat . ord

glueNonEmpty :: NonEmpty a -> E.List a
glueNonEmpty (x :| xs) = E.Cons x (glueList xs)

glueList :: [a] -> E.List a
glueList []       = E.Nil
glueList (x : xs) = E.Cons x (glueList xs)

glueTerm :: Term a -> ETerm
glueTerm = \case
  (P.Let _ r bs t)       -> E.Let (glueRecursivity r) (glueNonEmpty (fmap glueBinding bs)) (glueTerm t)
  (P.Var _ name)         -> E.Var (glueName name)
  (P.TyAbs _ tyname k t) -> E.TyAbs (glueTyName tyname) (glueKind k) (glueTerm t)
  (P.LamAbs _ name ty t) -> E.LamAbs (glueName name) (glueType ty) (glueTerm t)
  (P.Apply _ t t')       -> E.Apply (glueTerm t) (glueTerm t')
  (P.Constant _ c)       -> E.Constant (glueConstant c) -- (Some (ValueOf uni)) -- ^ a constant term
  (P.Builtin _ fun)      -> E.Builtin (glueDefaultFun fun)
  (P.TyInst _ t ty)      -> E.TyInst (glueTerm t) (glueType ty)
  (P.Unwrap _ t)         -> E.Unwrap (glueTerm t)
  (P.IWrap _ ty1 ty2 t)  -> E.IWrap (glueType ty1) (glueType ty2) (glueTerm t)
  (P.Error _ ty)         -> E.Error (glueType ty)

glueRecursivity :: P.Recursivity -> E.Recursivity
glueRecursivity P.Rec    = E.Rec
glueRecursivity P.NonRec = E.NonRec



glueDefaultFun :: P.DefaultFun -> E.DefaultFun
glueDefaultFun = \case
  P.AddInteger           -> E.AddInteger
  P.SubtractInteger      -> E.SubtractInteger
  P.MultiplyInteger      -> E.MultiplyInteger
  P.DivideInteger        -> E.DivideInteger
  P.QuotientInteger      -> E.QuotientInteger
  P.RemainderInteger     -> E.RemainderInteger
  P.ModInteger           -> E.ModInteger
  P.LessThanInteger      -> E.LessThanInteger
  P.LessThanEqInteger    -> E.LessThanEqInteger
  P.GreaterThanInteger   -> E.GreaterThanInteger
  P.GreaterThanEqInteger -> E.GreaterThanEqInteger
  P.EqInteger            -> E.EqInteger
  P.Concatenate          -> E.Concatenate
  P.TakeByteString       -> E.TakeByteString
  P.DropByteString       -> E.DropByteString
  P.SHA2                 -> E.SHA2
  P.SHA3                 -> E.SHA3
  P.VerifySignature      -> E.VerifySignature
  P.EqByteString         -> E.EqByteString
  P.LtByteString         -> E.LtByteString
  P.GtByteString         -> E.GtByteString
  P.IfThenElse           -> E.IfThenElse
  P.CharToString         -> E.CharToString
  P.Append               -> E.Append
  P.Trace                -> E.Trace

glueConstant :: P.Some (P.ValueOf P.DefaultUni) -> E.Some0 E.ValueOf
glueConstant (P.Some (P.ValueOf u x)) = E.Some (glueDefaultUni u) (E.unsafeCoerce x)

glueStrictness :: P.Strictness -> E.Strictness
glueStrictness P.Strict    = E.Strict
glueStrictness P.NonStrict = E.NonStrict


glueVarDecl :: PVarDecl a -> EVarDecl
glueVarDecl (P.VarDecl _ name ty) = E.VarDecl (glueName name) (glueType ty)

glueTyVarDecl :: PTyVarDecl a -> ETyVarDecl
glueTyVarDecl (P.TyVarDecl _ tyname k) = E.TyVarDecl (glueTyName tyname) (glueKind k)


glueConstructor :: PVarDecl a -> EConstr
glueConstructor (P.VarDecl _ name ty) = E.Constructor (E.VarDecl (glueName name) (glueType ty)) (arity ty)
  where
    arity :: P.Type tyname uni a -> E.Nat
    arity (P.TyFun _ _a b) = E.S (arity b)
    arity _                = E.O

glueDatatype :: PDatatype a -> EDatatype
glueDatatype (P.Datatype _ tvd tvs elim cs) = E.Datatype (glueTyVarDecl tvd) (glueList (fmap glueTyVarDecl tvs)) (glueName elim) (glueList (fmap glueConstructor cs))

glueBinding :: Binding a -> EBinding
glueBinding = \case
  (P.TermBind _ s vd t)  -> E.TermBind (glueStrictness s) (glueVarDecl vd) (glueTerm t) -- (VarDecl tyname name uni fun a) (Term tyname name uni fun a)
  (P.TypeBind _ tvd ty)  -> E.TypeBind (glueTyVarDecl tvd) (glueType ty) -- (TyVarDecl tyname a) (Type tyname uni a)
  (P.DatatypeBind _ dtd) -> E.DatatypeBind (glueDatatype dtd)

-- TODO: use show uniq? Fix rep in plutus
glueName :: P.Name -> EString
glueName (P.Name str _uniq) = glueString (unpack str)

glueTyName :: P.TyName -> EString
glueTyName (P.TyName n) = glueName n

glueDefaultUni :: P.DefaultUni a -> E.DefaultUni
glueDefaultUni u = case u of
  P.DefaultUniInteger    -> E.DefaultUniInteger
  P.DefaultUniByteString -> E.DefaultUniByteString
  P.DefaultUniString     -> E.DefaultUniString
  P.DefaultUniChar       -> E.DefaultUniChar
  P.DefaultUniUnit       -> E.DefaultUniUnit
  P.DefaultUniBool       -> E.DefaultUniBool

glueBuiltinType :: P.Some (P.TypeIn P.DefaultUni) -> E.Some0 ()
glueBuiltinType (P.Some (P.TypeIn u)) = E.Some (glueDefaultUni u) ()

glueType :: Type a -> EType
glueType (P.TyVar _ tyname)        = E.Ty_Var (glueTyName tyname)
glueType (P.TyFun _ t t')          = E.Ty_Fun (glueType t) (glueType t')
glueType (P.TyIFix _ t t')         = E.Ty_IFix (glueType t) (glueType t')
glueType (P.TyForall _ tyname k t) = E.Ty_Forall (glueTyName tyname) (glueKind k) (glueType t)
glueType (P.TyBuiltin _ b)         = E.Ty_Builtin (glueBuiltinType b)
glueType (P.TyLam _ tyname k t)    = E.Ty_Lam (glueTyName tyname) (glueKind k) (glueType t)
glueType (P.TyApp _ t t')          = E.Ty_App (glueType t) (glueType t')

glueKind :: Kind a -> EKind
glueKind (P.Type _)            = E.Kind_Base
glueKind (P.KindArrow _ k1 k2) = E.Kind_Arrow (glueKind k1) (glueKind k2)


-----------------------

glueBool :: E.Bool -> Bool
glueBool E.True  = True
glueBool E.False = False

is_dead_code :: Term a -> Term a -> Bool
is_dead_code t1 t2 = glueBool $ E.dec_Term (glueTerm t1) (glueTerm t2)
