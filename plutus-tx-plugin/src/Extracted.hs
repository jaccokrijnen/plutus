{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Extracted where

import qualified Prelude  ()

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Unit =
   Tt

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True  -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True  -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True  -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

data Sumbool =
   Left
 | Right

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True  -> False;
             False -> True}}

eqb0 :: Nat -> Nat -> Bool
eqb0 n m =
  case n of {
   O -> case m of {
         O   -> True;
         S _ -> False};
   S n' -> case m of {
            O    -> False;
            S m' -> eqb0 n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O    -> False;
            S m' -> leb n' m'}}

ltb :: Nat -> Nat -> Bool
ltb n m =
  leb (S n) m

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

eqb1 :: Positive -> Positive -> Bool
eqb1 p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb1 p0 q0;
             _     -> False};
   XO p0 -> case q of {
             XO q0 -> eqb1 p0 q0;
             _     -> False};
   XH -> case q of {
          XH -> True;
          _  -> False}}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil      -> Nil;
   Cons a t -> Cons (f a) (map f t)}

existsb :: (a1 -> Bool) -> (List a1) -> Bool
existsb f l =
  case l of {
   Nil       -> False;
   Cons a l0 -> orb (f a) (existsb f l0)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil       -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

eqb2 :: Z -> Z -> Bool
eqb2 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> True;
          _  -> False};
   Zpos p -> case y of {
              Zpos q -> eqb1 p q;
              _      -> False};
   Zneg p -> case y of {
              Zneg q -> eqb1 p q;
              _      -> False}}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

eqb3 :: Ascii0 -> Ascii0 -> Bool
eqb3 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     True  -> eqb a1 b1;
                                     False -> False} of {
                                True  -> eqb a2 b2;
                                False -> False} of {
                           True  -> eqb a3 b3;
                           False -> False} of {
                      True  -> eqb a4 b4;
                      False -> False} of {
                 True  -> eqb a5 b5;
                 False -> False} of {
            True  -> eqb a6 b6;
            False -> False} of {
       True  -> eqb a7 b7;
       False -> False}}}

data String =
   EmptyString
 | String0 Ascii0 String

eqb4 :: String -> String -> Bool
eqb4 s1 s2 =
  case s1 of {
   EmptyString -> case s2 of {
                   EmptyString -> True;
                   String0 _ _ -> False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> False;
     String0 c2 s2' ->
      case eqb3 c1 c2 of {
       True  -> eqb4 s1' s2';
       False -> False}}}

data Recursivity =
   NonRec
 | Rec

data Strictness =
   NonStrict
 | Strict

data DefaultUni =
   DefaultUniInteger
 | DefaultUniByteString
 | DefaultUniString
 | DefaultUniChar
 | DefaultUniUnit
 | DefaultUniBool

defaultUni_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> DefaultUni -> a1
defaultUni_rect f f0 f1 f2 f3 f4 d =
  case d of {
   DefaultUniInteger    -> f;
   DefaultUniByteString -> f0;
   DefaultUniString     -> f1;
   DefaultUniChar       -> f2;
   DefaultUniUnit       -> f3;
   DefaultUniBool       -> f4}

defaultUni_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> DefaultUni -> a1
defaultUni_rec =
  defaultUni_rect

data Some0 f =
   Some DefaultUni f

type UniType = Any

type ValueOf = UniType
  -- singleton inductive, whose constructor was ValueOf

data DefaultFun =
   AddInteger
 | SubtractInteger
 | MultiplyInteger
 | DivideInteger
 | QuotientInteger
 | RemainderInteger
 | ModInteger
 | LessThanInteger
 | LessThanEqInteger
 | GreaterThanInteger
 | GreaterThanEqInteger
 | EqInteger
 | Concatenate
 | TakeByteString
 | DropByteString
 | SHA2
 | SHA3
 | VerifySignature
 | EqByteString
 | LtByteString
 | GtByteString
 | IfThenElse
 | CharToString
 | Append
 | Trace

data Kind =
   Kind_Base
 | Kind_Arrow Kind Kind

data Ty tyname binderTyname =
   Ty_Var tyname
 | Ty_Fun (Ty tyname binderTyname) (Ty tyname binderTyname)
 | Ty_IFix (Ty tyname binderTyname) (Ty tyname binderTyname)
 | Ty_Forall binderTyname Kind (Ty tyname binderTyname)
 | Ty_Builtin (Some0 ())
 | Ty_Lam binderTyname Kind (Ty tyname binderTyname)
 | Ty_App (Ty tyname binderTyname) (Ty tyname binderTyname)

data Vdecl tyname binderName binderTyname =
   VarDecl binderName (Ty tyname binderTyname)

data Tvdecl binderTyname =
   TyVarDecl binderTyname Kind

data Constr tyname binderName binderTyname =
   Constructor (Vdecl tyname binderName binderTyname) Nat

data Dtdecl tyname binderName binderTyname =
   Datatype (Tvdecl binderTyname) (List (Tvdecl binderTyname)) binderName
 (List (Constr tyname binderName binderTyname))

data Term name tyname binderName binderTyname =
   Let Recursivity (List (Binding name tyname binderName binderTyname))
 (Term name tyname binderName binderTyname)
 | Var name
 | TyAbs binderTyname Kind (Term name tyname binderName binderTyname)
 | LamAbs binderName (Ty tyname binderTyname) (Term name tyname binderName
                                              binderTyname)
 | Apply (Term name tyname binderName binderTyname) (Term name tyname
                                                    binderName binderTyname)
 | Constant (Some0 ValueOf)
 | Builtin DefaultFun
 | TyInst (Term name tyname binderName binderTyname) (Ty tyname binderTyname)
 | Error (Ty tyname binderTyname)
 | IWrap (Ty tyname binderTyname) (Ty tyname binderTyname) (Term name
                                                           tyname binderName
                                                           binderTyname)
 | Unwrap (Term name tyname binderName binderTyname)
data Binding name tyname binderName binderTyname =
   TermBind Strictness (Vdecl tyname binderName binderTyname) (Term name
                                                              tyname
                                                              binderName
                                                              binderTyname)
 | TypeBind (Tvdecl binderTyname) (Ty tyname binderTyname)
 | DatatypeBind (Dtdecl tyname binderName binderTyname)

arity :: DefaultFun -> Nat
arity df =
  case df of {
   SHA2            -> S O;
   SHA3            -> S O;
   VerifySignature -> S (S (S O));
   IfThenElse      -> S (S (S (S O)));
   CharToString    -> S O;
   Trace           -> S O;
   _               -> S (S O)}

is_error_b :: (Term String String String String) -> Bool
is_error_b t =
  case t of {
   Error _ -> True;
   _       -> False}

is_value' :: Nat -> (Term String String String String) -> Bool
is_value' n t =
  case t of {
   Let _ _ _ -> False;
   Var _ -> False;
   Apply nv v ->
    andb (andb (is_value' n v) (negb (is_error_b v))) (is_value' (S n) nv);
   Builtin f -> ltb n (arity f);
   TyInst nv _ -> is_value' (S n) nv;
   IWrap _ _ v -> andb (is_value' n v) (negb (is_error_b v));
   Unwrap _ -> False;
   _ -> True}

is_value :: (Term String String String String) -> Bool
is_value =
  is_value' O

forall2b :: (a1 -> a1 -> Bool) -> (List a1) -> (List a1) -> Bool
forall2b p xs ys =
  case xs of {
   Nil -> case ys of {
           Nil      -> True;
           Cons _ _ -> False};
   Cons x xs0 ->
    case ys of {
     Nil        -> False;
     Cons y ys0 -> andb (p x y) (forall2b p xs0 ys0)}}

data Binder_info =
   Let_bound Strictness
 | Lambda_bound

type Ctx = List (Prod String Binder_info)

is_pure_binding :: Ctx -> (Binding String String String String) -> Bool
is_pure_binding _ b =
  case b of {
   TermBind s _ t -> case s of {
                      NonStrict -> True;
                      Strict    -> is_value t};
   _ -> True}

type EqDec a = a -> a -> Sumbool

defaultUni_dec :: EqDec DefaultUni
defaultUni_dec x y =
  defaultUni_rec (\x0 -> case x0 of {
                          DefaultUniInteger -> Left;
                          _                 -> Right}) (\x0 ->
    case x0 of {
     DefaultUniByteString -> Left;
     _                    -> Right}) (\x0 -> case x0 of {
                           DefaultUniString -> Left;
                           _                -> Right}) (\x0 ->
    case x0 of {
     DefaultUniChar -> Left;
     _              -> Right}) (\x0 -> case x0 of {
                           DefaultUniUnit -> Left;
                           _              -> Right}) (\x0 ->
    case x0 of {
     DefaultUniBool -> Left;
     _              -> Right}) x y

type Eqb x = x -> x -> Bool

unit_eqb :: Eqb Unit
unit_eqb _ _ =
  True

strictness_eqb :: Eqb Strictness
strictness_eqb x y =
  case x of {
   NonStrict -> case y of {
                 NonStrict -> True;
                 Strict    -> False};
   Strict -> case y of {
              NonStrict -> False;
              Strict    -> True}}

recursivity_eqb :: Eqb Recursivity
recursivity_eqb x y =
  case x of {
   NonRec -> case y of {
              NonRec -> True;
              Rec    -> False};
   Rec -> case y of {
           NonRec -> False;
           Rec    -> True}}

func_eqb :: Eqb DefaultFun
func_eqb x y =
  case x of {
   AddInteger -> case y of {
                  AddInteger -> True;
                  _          -> False};
   SubtractInteger -> case y of {
                       SubtractInteger -> True;
                       _               -> False};
   MultiplyInteger -> case y of {
                       MultiplyInteger -> True;
                       _               -> False};
   DivideInteger -> case y of {
                     DivideInteger -> True;
                     _             -> False};
   QuotientInteger -> case y of {
                       QuotientInteger -> True;
                       _               -> False};
   RemainderInteger -> case y of {
                        RemainderInteger -> True;
                        _                -> False};
   ModInteger -> case y of {
                  ModInteger -> True;
                  _          -> False};
   LessThanInteger -> case y of {
                       LessThanInteger -> True;
                       _               -> False};
   LessThanEqInteger -> case y of {
                         LessThanEqInteger -> True;
                         _                 -> False};
   GreaterThanInteger -> case y of {
                          GreaterThanInteger -> True;
                          _                  -> False};
   GreaterThanEqInteger ->
    case y of {
     GreaterThanEqInteger -> True;
     _                    -> False};
   EqInteger -> case y of {
                 EqInteger -> True;
                 _         -> False};
   Concatenate -> case y of {
                   Concatenate -> True;
                   _           -> False};
   TakeByteString -> case y of {
                      TakeByteString -> True;
                      _              -> False};
   DropByteString -> case y of {
                      DropByteString -> True;
                      _              -> False};
   SHA2 -> case y of {
            SHA2 -> True;
            _    -> False};
   SHA3 -> case y of {
            SHA3 -> True;
            _    -> False};
   VerifySignature -> case y of {
                       VerifySignature -> True;
                       _               -> False};
   EqByteString -> case y of {
                    EqByteString -> True;
                    _            -> False};
   LtByteString -> case y of {
                    LtByteString -> True;
                    _            -> False};
   GtByteString -> case y of {
                    GtByteString -> True;
                    _            -> False};
   IfThenElse -> case y of {
                  IfThenElse -> True;
                  _          -> False};
   CharToString -> case y of {
                    CharToString -> True;
                    _            -> False};
   Append -> case y of {
              Append -> True;
              _      -> False};
   Trace -> case y of {
             Trace -> True;
             _     -> False}}

uniType_eqb :: DefaultUni -> Eqb UniType
uniType_eqb ty =
  case ty of {
   DefaultUniInteger -> unsafeCoerce eqb2;
   DefaultUniChar    -> unsafeCoerce eqb3;
   DefaultUniUnit    -> unsafeCoerce unit_eqb;
   DefaultUniBool    -> unsafeCoerce eqb;
   _                 -> unsafeCoerce eqb4}


valueOf_eqb :: DefaultUni -> Eqb ValueOf
valueOf_eqb =
  uniType_eqb

some_valueOf_eqb :: Eqb (Some0 ValueOf)
some_valueOf_eqb x y =
  case x of {
   Some t v ->
    case y of {
     Some t' v' ->
      case defaultUni_dec t t' of {
       Left  -> valueOf_eqb t' (eq_rect t v t') v';
       Right -> False}}}

typeIn_eqb :: DefaultUni -> Bool
typeIn_eqb _ =
  True

some_typeIn_eqb :: Eqb (Some0 ())
some_typeIn_eqb x y =
  case x of {
   Some t _ ->
    case y of {
     Some t' _ ->
      case defaultUni_dec t t' of {
       Left  -> typeIn_eqb t';
       Right -> False}}}

kind_eqb :: Kind -> Kind -> Bool
kind_eqb x y =
  case x of {
   Kind_Base -> case y of {
                 Kind_Base      -> True;
                 Kind_Arrow _ _ -> False};
   Kind_Arrow k1 k2 ->
    case y of {
     Kind_Base        -> False;
     Kind_Arrow k3 k4 -> andb (kind_eqb k1 k3) (kind_eqb k2 k4)}}

ty_eqb :: (Ty String String) -> (Ty String String) -> Bool
ty_eqb x y =
  case x of {
   Ty_Var x0 -> case y of {
                 Ty_Var y0 -> eqb4 x0 y0;
                 _         -> False};
   Ty_Fun t1 t2 ->
    case y of {
     Ty_Fun t3 t4 -> andb (ty_eqb t1 t3) (ty_eqb t2 t4);
     _            -> False};
   Ty_IFix t1 u1 ->
    case y of {
     Ty_IFix t2 u2 -> andb (ty_eqb t1 t2) (ty_eqb u1 u2);
     _             -> False};
   Ty_Forall x1 k1 t1 ->
    case y of {
     Ty_Forall x2 k2 t2 ->
      andb (andb (eqb4 x1 x2) (kind_eqb k1 k2)) (ty_eqb t1 t2);
     _ -> False};
   Ty_Builtin s1 ->
    case y of {
     Ty_Builtin s2 -> some_typeIn_eqb s1 s2;
     _             -> False};
   Ty_Lam x1 k1 t1 ->
    case y of {
     Ty_Lam x2 k2 t2 ->
      andb (andb (eqb4 x1 x2) (kind_eqb k1 k2)) (ty_eqb t1 t2);
     _ -> False};
   Ty_App s1 t1 ->
    case y of {
     Ty_App s2 t2 -> andb (ty_eqb s1 s2) (ty_eqb t1 t2);
     _            -> False}}

tVDecl_eqb :: Eqb (Tvdecl String)
tVDecl_eqb x y =
  case x of {
   TyVarDecl ty k ->
    case y of {
     TyVarDecl ty' k' -> andb (eqb4 ty ty') (kind_eqb k k')}}

vDecl_eqb :: Eqb (Vdecl String String String)
vDecl_eqb x y =
  case x of {
   VarDecl x0 ty ->
    case y of {
     VarDecl x' ty' -> andb (eqb4 x0 x') (ty_eqb ty ty')}}

constructor_eqb :: Eqb (Constr String String String)
constructor_eqb x y =
  case x of {
   Constructor c n ->
    case y of {
     Constructor c' n' -> andb (vDecl_eqb c c') (eqb0 n n')}}

list_eqb :: (Eqb a1) -> Eqb (List a1)
list_eqb eqb5 xs ys =
  case xs of {
   Nil -> case ys of {
           Nil      -> True;
           Cons _ _ -> False};
   Cons x xs0 ->
    case ys of {
     Nil        -> False;
     Cons y ys0 -> andb (eqb5 x y) (list_eqb eqb5 xs0 ys0)}}

dTDecl_eqb :: Eqb (Dtdecl String String String)
dTDecl_eqb x y =
  case x of {
   Datatype tvd tvds n cs ->
    case y of {
     Datatype tvd' tvds' n' cs' ->
      andb
        (andb (andb (tVDecl_eqb tvd tvd') (list_eqb tVDecl_eqb tvds tvds'))
          (eqb4 n n')) (list_eqb constructor_eqb cs cs')}}

term_eqb :: (Term String String String String) -> (Term String String
            String String) -> Bool
term_eqb x y =
  case x of {
   Let rec bs t ->
    case y of {
     Let rec' bs' t' ->
      andb (andb (recursivity_eqb rec rec') (list_eqb binding_eqb bs bs'))
        (term_eqb t t');
     _ -> False};
   Var n -> case y of {
             Var n' -> eqb4 n n';
             _      -> False};
   TyAbs n k t ->
    case y of {
     TyAbs n' k' t' ->
      andb (andb (eqb4 n n') (kind_eqb k k')) (term_eqb t t');
     _ -> False};
   LamAbs n ty t ->
    case y of {
     LamAbs n' ty' t' ->
      andb (andb (eqb4 n n') (ty_eqb ty ty')) (term_eqb t t');
     _ -> False};
   Apply s t ->
    case y of {
     Apply s' t' -> andb (term_eqb s s') (term_eqb t t');
     _           -> False};
   Constant c ->
    case y of {
     Constant c' -> some_valueOf_eqb c c';
     _           -> False};
   Builtin f -> case y of {
                 Builtin f' -> func_eqb f f';
                 _          -> False};
   TyInst t ty ->
    case y of {
     TyInst t' ty' -> andb (term_eqb t t') (ty_eqb ty ty');
     _             -> False};
   Error ty -> case y of {
                Error ty' -> ty_eqb ty ty';
                _         -> False};
   IWrap ty1 ty2 t ->
    case y of {
     IWrap ty1' ty2' t' ->
      andb (andb (ty_eqb ty1 ty1') (ty_eqb ty2 ty2')) (term_eqb t t');
     _ -> False};
   Unwrap t -> case y of {
                Unwrap t' -> term_eqb t t';
                _         -> False}}

binding_eqb :: (Binding String String String String) -> (Binding String
               String String String) -> Bool
binding_eqb x y =
  case x of {
   TermBind s vd t ->
    case y of {
     TermBind s' vd' t' ->
      andb (andb (strictness_eqb s s') (vDecl_eqb vd vd')) (term_eqb t t');
     _ -> False};
   TypeBind tvd ty ->
    case y of {
     TypeBind tvd' ty' -> andb (tVDecl_eqb tvd tvd') (ty_eqb ty ty');
     _                 -> False};
   DatatypeBind dtd ->
    case y of {
     DatatypeBind dtd' -> dTDecl_eqb dtd dtd';
     _                 -> False}}

is_cong_binding :: ((Term String String String String) -> (Term String
                   String String String) -> Bool) -> (Binding String
                   String String String) -> (Binding String String String
                   String) -> Bool
is_cong_binding is_R b b' =
  case b of {
   TermBind s v t ->
    case b' of {
     TermBind s' v' t' ->
      andb (andb (strictness_eqb s s') (vDecl_eqb v v')) (is_R t t');
     _ -> False};
   TypeBind v t ->
    case b' of {
     TypeBind v' t' -> andb (tVDecl_eqb v v') (ty_eqb t t');
     _              -> False};
   DatatypeBind d ->
    case b' of {
     DatatypeBind d' -> dTDecl_eqb d d';
     _               -> False}}

is_cong :: ((Term String String String String) -> (Term String String
           String String) -> Bool) -> (Term String String String String) ->
           (Term String String String String) -> Bool
is_cong is_R t t' =
  case t of {
   Let r bs t0 ->
    case t' of {
     Let r' bs' t'0 ->
      andb
        (andb (recursivity_eqb r r')
          (forall2b (is_cong_binding is_R) bs bs')) (is_R t0 t'0);
     _ -> False};
   Var n -> case t' of {
             Var n' -> eqb4 n n';
             _      -> False};
   TyAbs n k t0 ->
    case t' of {
     TyAbs n' k' t'0 -> andb (andb (eqb4 n n') (kind_eqb k k')) (is_R t0 t'0);
     _               -> False};
   LamAbs n t0 t1 ->
    case t' of {
     LamAbs n' t'0 t'1 ->
      andb (andb (eqb4 n n') (ty_eqb t0 t'0)) (is_R t1 t'1);
     _ -> False};
   Apply s t0 ->
    case t' of {
     Apply s' t'0 -> andb (is_R s s') (is_R t0 t'0);
     _            -> False};
   Constant v ->
    case t' of {
     Constant v' -> some_valueOf_eqb v v';
     _           -> False};
   Builtin f -> case t' of {
                 Builtin f' -> func_eqb f f';
                 _          -> False};
   TyInst t0 t1 ->
    case t' of {
     TyInst t'0 t'1 -> andb (ty_eqb t1 t'1) (is_R t0 t'0);
     _              -> False};
   Error t0 -> case t' of {
                Error t'0 -> ty_eqb t0 t'0;
                _         -> False};
   IWrap t1 t2 t0 ->
    case t' of {
     IWrap t1' t2' t'0 ->
      andb (andb (ty_eqb t1 t1') (ty_eqb t2 t2')) (is_R t0 t'0);
     _ -> False};
   Unwrap t0 -> case t' of {
                 Unwrap t'0 -> is_R t0 t'0;
                 _          -> False}}

name_Binding :: (Binding String String String String) -> String
name_Binding b =
  case b of {
   TermBind _ v _ -> case v of {
                      VarDecl x _ -> x};
   TypeBind t _ -> case t of {
                    TyVarDecl x _ -> x};
   DatatypeBind d ->
    case d of {
     Datatype t _ _ _ -> case t of {
                          TyVarDecl x _ -> x}}}

dec_Binding :: ((Term String String String String) -> (Term String String
               String String) -> Bool) -> (Binding String String String
               String) -> (Binding String String String String) -> Bool
dec_Binding dec_Term0 b b' =
  case b of {
   TermBind s vd t ->
    case b' of {
     TermBind s' vd' t' ->
      andb (andb (strictness_eqb s s') (vDecl_eqb vd vd')) (dec_Term0 t t');
     _ -> binding_eqb b b'};
   _ -> binding_eqb b b'}

safely_removed :: (Binding String String String String) -> (List String) ->
                  Bool
safely_removed b bsn =
  andb (negb (existsb (eqb4 (name_Binding b)) bsn)) (is_pure_binding Nil b)

find_Binding :: ((Term String String String String) -> (Term String String
                String String) -> Bool) -> (Binding String String String
                String) -> (List (Binding String String String String)) ->
                Bool
find_Binding dec_Term0 b' bs =
  case bs of {
   Nil -> False;
   Cons b bs0 ->
    case eqb4 (name_Binding b) (name_Binding b') of {
     True  -> dec_Binding dec_Term0 b b';
     False -> find_Binding dec_Term0 b' bs0}}

dec_Bindings :: ((Term String String String String) -> (Term String String
                String String) -> Bool) -> (List
                (Binding String String String String)) -> (List
                (Binding String String String String)) -> Bool
dec_Bindings dec_Term0 bs bs' =
  let {bs'n = map name_Binding bs'} in
  andb (forallb (\b -> safely_removed b bs'n) bs)
    (forallb (\b' -> find_Binding dec_Term0 b' bs) bs')

dec_Term :: (Term String String String String) -> (Term String String
            String String) -> Bool
dec_Term x y =
  case x of {
   Let r bs t ->
    case y of {
     Let r' bs' t' ->
      case dec_Bindings dec_Term bs bs' of {
       True  -> andb (recursivity_eqb r r') (dec_Term t t');
       False -> andb (forallb (is_pure_binding Nil) bs) (dec_Term t t')};
     _ -> is_cong dec_Term x y};
   _ -> is_cong dec_Term x y}


----------------------------------------
-- Extracted nat_of_ascii
--


add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O   -> m;
   S p -> S (add p m)}

data N =
   N0
 | Npos Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH   -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH   -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH   -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH   -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH   -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH   -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH   -> XI XH}}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH   -> y}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH    -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

add1 :: N -> N -> N
add1 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0     -> n;
              Npos q -> Npos (add0 p q)}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0     -> N0;
              Npos q -> Npos (mul p q)}}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0     -> O;
   Npos p -> to_nat p}

n_of_digits :: (List Bool) -> N
n_of_digits l =
  case l of {
   Nil -> N0;
   Cons b l' ->
    add1 (case b of {
           True  -> Npos XH;
           False -> N0}) (mul0 (Npos (XO XH)) (n_of_digits l'))}

n_of_ascii :: Ascii0 -> N
n_of_ascii a =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (Cons a0 (Cons a1 (Cons a2 (Cons a3 (Cons a4 (Cons a5 (Cons
      a6 (Cons a7 Nil))))))))}

nat_of_ascii :: Ascii0 -> Nat
nat_of_ascii a =
  to_nat0 (n_of_ascii a)

-----------------------------
-- extract ascii_of_nat
-- ----------------------------


ascii_of_pos :: Positive -> Ascii0
ascii_of_pos =
  let {
   loop n p =
     case n of {
      O -> zero;
      S n' ->
       case p of {
        XI p' -> shift True (loop n' p');
        XO p' -> shift False (loop n' p');
        XH    -> one}}}
  in loop (S (S (S (S (S (S (S (S O))))))))

ascii_of_N :: N -> Ascii0
ascii_of_N n =
  case n of {
   N0     -> zero;
   Npos p -> ascii_of_pos p}

ascii_of_nat :: Nat -> Ascii0
ascii_of_nat a =
  ascii_of_N (of_nat a)

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O   -> XH;
   S x -> succ (of_succ_nat x)}

of_nat :: Nat -> N
of_nat n =
  case n of {
   O    -> N0;
   S n' -> Npos (of_succ_nat n')}

zero :: Ascii0
zero =
  Ascii False False False False False False False False

one :: Ascii0
one =
  Ascii True False False False False False False False

shift :: Bool -> Ascii0 -> Ascii0
shift c a =
  case a of {
   Ascii a1 a2 a3 a4 a5 a6 a7 _ -> Ascii c a1 a2 a3 a4 a5 a6 a7}

