{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE IncoherentInstances  #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.PlutusIR.Certifier.Glue where

import qualified Language.PlutusCore                   as P (DefaultFun (..), DefaultUni (..), Some (..), TypeIn (..),
                                                             ValueOf (..))
import qualified Language.PlutusIR                     as P
import qualified Language.PlutusIR.Certifier.Extracted as E

import           Data.Bits
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
glueString = Prelude.foldr (E.String0 . glueChar) E.EmptyString

intToNat :: Int -> E.Nat
intToNat 0 = E.O
intToNat n
  | n < 0 = error "intToNat: negative Int"
  | otherwise = E.S (intToNat (n - 1))

glueChar :: Char -> E.Ascii0
glueChar = E.ascii_of_nat . intToNat . ord

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
glueConstant (P.Some (P.ValueOf u x)) =
  let any = case u of
        P.DefaultUniInteger    -> E.unsafeCoerce (glueInteger x)
        P.DefaultUniChar       -> E.unsafeCoerce (glueChar x)
        P.DefaultUniUnit       -> E.unsafeCoerce x -- same rep ()
        P.DefaultUniBool       -> E.unsafeCoerce (glueBool x)
        P.DefaultUniString     -> E.unsafeCoerce (glueString x)
        P.DefaultUniByteString -> E.unsafeCoerce (glueString (show x))
  in E.Some (glueDefaultUni u) (E.unsafeCoerce any)

glueInteger :: Integer -> E.Z
glueInteger x
  | x == 0 = E.Z0
  | x > 0  = E.Zpos (gluePositive x)
  | x < 0  = E.Zneg (gluePositive (-1 * x))



-- Coq's representation of Positive: https://coq.inria.fr/library/Coq.Numbers.BinNums.html
gluePositive :: Integer -> E.Positive
gluePositive n
  | n <= 0    = error "gluePositive: non-positive number provided"
  | otherwise = bitsToPos (go n)
  where
    go 0 = []
    go n = case divMod n 2 of
      (r, 0) -> False : go r
      (r, 1) -> True : go r

    bitsToPos :: [Bool] -> E.Positive
    bitsToPos []           = error "bitsToPos: positive number should have a most significant (leading) 1 bit"
    bitsToPos (True : [])  = E.XH
    bitsToPos (True : xs)  = E.XI (bitsToPos xs)
    bitsToPos (False : xs) = E.XO (bitsToPos xs)


glueBool :: Bool -> E.Bool
glueBool True  = E.True
glueBool False = E.False

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
-- glueName (P.Name str _uniq) = glueString (unpack str)
glueName (P.Name _str uniq) = glueString (show uniq)

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

toBool :: E.Bool -> Bool
toBool E.True  = True
toBool E.False = False

is_dead_code :: Term a -> Term a -> Bool
is_dead_code t1 t2 = toBool $ E.dec_Term (glueTerm t1) (glueTerm t2)

is_eq :: Term a -> Term a -> Bool
is_eq t1 t2 = toBool $ E.term_eqb (glueTerm t1) (glueTerm t2)

----------------------------
-- Show instances for debugging conversion glue
--

deriving instance Show E.Unit
deriving instance Show E.Bool
deriving instance Show E.Nat
deriving instance (Show a, Show b) => Show (E.Prod a b)
deriving instance Show a => Show (E.List a)
deriving instance Show E.Sumbool
deriving instance Show E.Positive
deriving instance Show E.Z
deriving instance Show E.Ascii0
deriving instance Show E.Recursivity
deriving instance Show E.Strictness
deriving instance Show E.DefaultUni
instance Show (E.Some0 a) where
  show x = "Some _"
-- instance Show (E.Some0 a) where
--   show (E.Some ty x) = case ty of {
--    E.DefaultUniInteger -> show @E.Z (E.unsafeCoerce x);
--    E.DefaultUniChar    -> show @E.Ascii0 (E.unsafeCoerce x);
--    E.DefaultUniUnit    -> show @E.Unit (E.unsafeCoerce x);
--    E.DefaultUniBool    -> show @E.Bool (E.unsafeCoerce x);
--    _                 -> show @E.String(E.unsafeCoerce x)}
deriving instance Show (E.Some0 ())
deriving instance Show E.DefaultFun
deriving instance Show E.Kind
deriving instance Show E.Binder_info
deriving instance Show E.N

deriving instance Show EType
deriving instance Show EVarDecl
deriving instance Show ETyVarDecl
deriving instance Show EConstr
deriving instance Show EDatatype
deriving instance Show ETerm
deriving instance Show EBinding
deriving instance Show EString
