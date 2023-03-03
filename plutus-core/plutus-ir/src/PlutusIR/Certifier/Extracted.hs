{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module PlutusIR.Certifier.Extracted where

import Prelude qualified

#ifdef __GLASGOW_HASKELL__
import GHC.Base qualified
#else
-- HUGS
import IOExts qualified
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

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Unit =
   Tt

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True  -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

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

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left  -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True  -> Left;
                   False -> Right}) (\x ->
    case x of {
     True  -> Right;
     False -> Left}) b1 b2

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

data N =
   N0
 | Npos Positive

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH   -> XO XH}

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

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

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

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

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

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString  -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ h x ->
    case x of {
     EmptyString -> Right;
     String0 a0 s0 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (h s0))
        (\_ -> Right) (ascii_dec a a0)}) s1 s2

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

type Decidable = Sumbool

type Dec = Decidable
  -- singleton inductive, whose constructor was Build_Dec

dec :: Dec -> Decidable
dec dec0 =
  dec0

type DecOpt =
  Nat -> Option Bool
  -- singleton inductive, whose constructor was Build_DecOpt

decOpt :: DecOpt -> Nat -> Option Bool
decOpt decOpt0 =
  decOpt0

dec_decOpt :: Dec -> DecOpt
dec_decOpt h _ =
  case dec h of {
   Left  -> Some True;
   Right -> Some False}

checker_backtrack :: (List (Unit -> Option Bool)) -> Option Bool
checker_backtrack l =
  let {
   aux l0 b =
     case l0 of {
      Nil -> case b of {
              True  -> None;
              False -> Some False};
      Cons t ts ->
       case t Tt of {
        Some y -> case y of {
                   True  -> Some True;
                   False -> aux ts b};
        None -> aux ts True}}}
  in aux l False

type Dec_Eq a =
  a -> a -> Decidable
  -- singleton inductive, whose constructor was Build_Dec_Eq

dec_eq :: (Dec_Eq a1) -> a1 -> a1 -> Decidable
dec_eq dec_Eq =
  dec_Eq

eq__Dec :: (Dec_Eq a1) -> a1 -> a1 -> Dec
eq__Dec =
  dec_eq

dec_eq_string :: Dec_Eq String
dec_eq_string =
  string_dec

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

decOptNameIn :: String -> (List String) -> DecOpt
decOptNameIn x_ xs_ =
  let {
   aux_arb = let {
              aux_arb init_size size x_0 xs_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case xs_0 of {
                     Nil -> Some False;
                     Cons unkn_0_ _ ->
                      decOpt (dec_decOpt (eq__Dec dec_eq_string unkn_0_ x_0))
                        init_size}) (Cons (\_ -> None) Nil));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case xs_0 of {
                     Nil -> Some False;
                     Cons unkn_2_ _ ->
                      decOpt (dec_decOpt (eq__Dec dec_eq_string unkn_2_ x_0))
                        init_size}) (Cons (\_ ->
                    case xs_0 of {
                     Nil -> Some False;
                     Cons x' xs ->
                      case decOpt (dec_decOpt (eq__Dec dec_eq_string x_0 x'))
                             init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' x_0 xs};
                       None -> None}}) Nil))}}
             in aux_arb}
  in
  (\size -> aux_arb size size x_ xs_)

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
   Some' DefaultUni f

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

bv_constructors :: (List (Constr String String String)) -> List String
bv_constructors cs =
  case cs of {
   Nil -> Nil;
   Cons c cs' ->
    case c of {
     Constructor v _ ->
      case v of {
       VarDecl x _ -> Cons x (bv_constructors cs')}}}

decOptappears_bound_in_ty :: String -> (Ty String String) -> DecOpt
decOptappears_bound_in_ty x_ ty_ =
  let {
   aux_arb = let {
              aux_arb init_size size x_0 ty_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Ty_Forall unkn_4_ _ _ ->
                      decOpt (dec_decOpt (eq__Dec dec_eq_string unkn_4_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Lam unkn_6_ _ _ ->
                      decOpt (dec_decOpt (eq__Dec dec_eq_string unkn_6_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ -> None) Nil)));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Ty_Forall unkn_14_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_14_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Lam unkn_16_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_16_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Fun t1 _ -> aux_arb init_size size' x_0 t1;
                     _           -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Fun _ t2 -> aux_arb init_size size' x_0 t2;
                     _           -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_IFix f _ -> aux_arb init_size size' x_0 f;
                     _           -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_IFix _ t -> aux_arb init_size size' x_0 t;
                     _           -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Forall y _ t ->
                      case decOpt (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                             init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' y t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Lam y _ t ->
                      case decOpt (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                             init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' y t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_App t1 _ -> aux_arb init_size size' x_0 t1;
                     _           -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_App _ t2 -> aux_arb init_size size' x_0 t2;
                     _           -> Some False}) Nil))))))))))}}
             in aux_arb}
  in
  (\size -> aux_arb size size x_ ty_)

decOptappears_bound_in_tm :: String -> (Term String String String String) ->
                             DecOpt
decOptappears_bound_in_tm x_ tm_ =
  let {
   aux_arb = let {
              aux_arb init_size size x_0 tm_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case tm_0 of {
                     LamAbs unkn_20_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_20_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ v _ ->
                          case v of {
                           VarDecl unkn_30_ _ ->
                            decOpt
                              (dec_decOpt
                                (eq__Dec dec_eq_string unkn_30_ x_0))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         DatatypeBind d ->
                          case d of {
                           Datatype _ _ mfunc cs ->
                            let {unkn_32_ = bv_constructors cs} in
                            decOpt (decOptNameIn x_0 (Cons mfunc unkn_32_))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ -> None) Nil))));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case tm_0 of {
                     LamAbs unkn_33_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_33_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ v _ ->
                          case v of {
                           VarDecl unkn_43_ _ ->
                            decOpt
                              (dec_decOpt
                                (eq__Dec dec_eq_string unkn_43_ x_0))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         DatatypeBind d ->
                          case d of {
                           Datatype _ _ mfunc cs ->
                            let {unkn_45_ = bv_constructors cs} in
                            decOpt (decOptNameIn x_0 (Cons mfunc unkn_45_))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     LamAbs y _ t ->
                      case decOpt (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                             init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' x_0 t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Apply t1 _ -> aux_arb init_size size' x_0 t1;
                     _          -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Apply _ t2 -> aux_arb init_size size' x_0 t2;
                     _          -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     TyAbs _ _ t -> aux_arb init_size size' x_0 t;
                     _           -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     TyInst t _ -> aux_arb init_size size' x_0 t;
                     _          -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     IWrap _ _ t -> aux_arb init_size size' x_0 t;
                     _           -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Unwrap t -> aux_arb init_size size' x_0 t;
                     _        -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l t0 ->
                      case l of {
                       Nil      -> aux_arb init_size size' x_0 t0;
                       Cons _ _ -> Some False};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let recty l t0 ->
                      case l of {
                       Nil -> Some False;
                       Cons _ bs ->
                        aux_arb init_size size' x_0 (Let recty bs t0)};
                     _ -> Some False}) (Cons (\_ ->
                    case tm_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ v t ->
                          case v of {
                           VarDecl y _ ->
                            case decOpt
                                   (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                                   init_size of {
                             Some res_b ->
                              case res_b of {
                               True  -> Some False;
                               False -> aux_arb init_size size' x_0 t};
                             None -> None}};
                         _ -> Some False}};
                     _ -> Some False}) Nil)))))))))))))}}
             in aux_arb}
  in
  (\size -> aux_arb size size x_ tm_)

decOptappears_bound_in_ann :: String -> (Term String String String String) ->
                              DecOpt
decOptappears_bound_in_ann x_ ann_ =
  let {
   aux_arb = let {
              aux_arb init_size size x_0 ann_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case ann_0 of {
                     LamAbs _ t _ ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyAbs unkn_49_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_49_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyInst _ t ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     IWrap f _ _ ->
                      decOpt (decOptappears_bound_in_ty x_0 f) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     IWrap _ t _ ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Error t ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ v _ ->
                          case v of {
                           VarDecl _ t ->
                            decOpt (decOptappears_bound_in_ty x_0 t)
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TypeBind t _ ->
                          case t of {
                           TyVarDecl unkn_57_ _ ->
                            decOpt
                              (dec_decOpt
                                (eq__Dec dec_eq_string unkn_57_ x_0))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TypeBind t t0 ->
                          case t of {
                           TyVarDecl y _ ->
                            case decOpt
                                   (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                                   init_size of {
                             Some res_b ->
                              case res_b of {
                               True -> Some False;
                               False ->
                                decOpt (decOptappears_bound_in_ty x_0 t0)
                                  init_size};
                             None -> None}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         DatatypeBind d ->
                          case d of {
                           Datatype t _ _ _ ->
                            case t of {
                             TyVarDecl unkn_58_ _ ->
                              decOpt
                                (dec_decOpt
                                  (eq__Dec dec_eq_string unkn_58_ x_0))
                                init_size}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ -> None) Nil)))))))))));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case ann_0 of {
                     LamAbs _ t _ ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyAbs unkn_62_ _ _ ->
                      decOpt
                        (dec_decOpt (eq__Dec dec_eq_string unkn_62_ x_0))
                        init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyInst _ t ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     IWrap f _ _ ->
                      decOpt (decOptappears_bound_in_ty x_0 f) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     IWrap _ t _ ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Error t ->
                      decOpt (decOptappears_bound_in_ty x_0 t) init_size;
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ v _ ->
                          case v of {
                           VarDecl _ t ->
                            decOpt (decOptappears_bound_in_ty x_0 t)
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TypeBind t _ ->
                          case t of {
                           TyVarDecl unkn_70_ _ ->
                            decOpt
                              (dec_decOpt
                                (eq__Dec dec_eq_string unkn_70_ x_0))
                              init_size};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TypeBind t t0 ->
                          case t of {
                           TyVarDecl y _ ->
                            case decOpt
                                   (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                                   init_size of {
                             Some res_b ->
                              case res_b of {
                               True -> Some False;
                               False ->
                                decOpt (decOptappears_bound_in_ty x_0 t0)
                                  init_size};
                             None -> None}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         DatatypeBind d ->
                          case d of {
                           Datatype t _ _ _ ->
                            case t of {
                             TyVarDecl unkn_71_ _ ->
                              decOpt
                                (dec_decOpt
                                  (eq__Dec dec_eq_string unkn_71_ x_0))
                                init_size}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     LamAbs _ _ t -> aux_arb init_size size' x_0 t;
                     _            -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Apply t1 _ -> aux_arb init_size size' x_0 t1;
                     _          -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Apply _ t2 -> aux_arb init_size size' x_0 t2;
                     _          -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyAbs y _ t ->
                      case decOpt (dec_decOpt (eq__Dec dec_eq_string x_0 y))
                             init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' x_0 t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     TyInst t _ -> aux_arb init_size size' x_0 t;
                     _          -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     IWrap _ _ t -> aux_arb init_size size' x_0 t;
                     _           -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Unwrap t -> aux_arb init_size size' x_0 t;
                     _        -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l t0 ->
                      case l of {
                       Nil      -> aux_arb init_size size' x_0 t0;
                       Cons _ _ -> Some False};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let recty l t0 ->
                      case l of {
                       Nil -> Some False;
                       Cons _ bs ->
                        aux_arb init_size size' x_0 (Let recty bs t0)};
                     _ -> Some False}) (Cons (\_ ->
                    case ann_0 of {
                     Let _ l _ ->
                      case l of {
                       Nil -> Some False;
                       Cons b _ ->
                        case b of {
                         TermBind _ _ t -> aux_arb init_size size' x_0 t;
                         _              -> Some False}};
                     _ -> Some False}) Nil))))))))))))))))))))}}
             in aux_arb}
  in
  (\size -> aux_arb size size x_ ann_)

decOptunique_ty :: (Ty String String) -> DecOpt
decOptunique_ty ty_ =
  let {
   aux_arb = let {
              aux_arb init_size size ty_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Ty_Builtin _ -> Some True;
                     _            -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Var _ -> Some True;
                     _        -> Some False}) (Cons (\_ -> None) Nil)));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Ty_Builtin _ -> Some True;
                     _            -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Var _ -> Some True;
                     _        -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Fun t1 t2 ->
                      case aux_arb init_size size' t1 of {
                       Some res_b ->
                        case res_b of {
                         True  -> aux_arb init_size size' t2;
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Forall x _ t ->
                      case decOpt (decOptappears_bound_in_ty x t) init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_IFix f t ->
                      case aux_arb init_size size' f of {
                       Some res_b ->
                        case res_b of {
                         True  -> aux_arb init_size size' t;
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_Lam x _ t ->
                      case decOpt (decOptappears_bound_in_ty x t) init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Ty_App t1 t2 ->
                      case aux_arb init_size size' t1 of {
                       Some res_b ->
                        case res_b of {
                         True  -> aux_arb init_size size' t2;
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) Nil)))))))}}
             in aux_arb}
  in
  (\size -> aux_arb size size ty_)

decOptunique_tm :: (Term String String String String) -> DecOpt
decOptunique_tm ty_ =
  let {
   aux_arb = let {
              aux_arb init_size size ty_0 =
                case size of {
                 O ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Var _ -> Some True;
                     _     -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Constant _ -> Some True;
                     _          -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Builtin _ -> Some True;
                     _         -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Error t -> decOpt (decOptunique_ty t) init_size;
                     _       -> Some False}) (Cons (\_ -> None) Nil)))));
                 S size' ->
                  checker_backtrack (Cons (\_ ->
                    case ty_0 of {
                     Var _ -> Some True;
                     _     -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Constant _ -> Some True;
                     _          -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Builtin _ -> Some True;
                     _         -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Error t -> decOpt (decOptunique_ty t) init_size;
                     _       -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     LamAbs x t t0 ->
                      case decOpt (decOptappears_bound_in_tm x t0) init_size of {
                       Some res_b ->
                        case res_b of {
                         True -> Some False;
                         False ->
                          case aux_arb init_size size' t0 of {
                           Some res_b0 ->
                            case res_b0 of {
                             True  -> decOpt (decOptunique_ty t) init_size;
                             False -> Some False};
                           None -> None}};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Apply t1 t2 ->
                      case aux_arb init_size size' t1 of {
                       Some res_b ->
                        case res_b of {
                         True  -> aux_arb init_size size' t2;
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     TyAbs x _ t ->
                      case decOpt (decOptappears_bound_in_ann x t) init_size of {
                       Some res_b ->
                        case res_b of {
                         True  -> Some False;
                         False -> aux_arb init_size size' t};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     TyInst t t0 ->
                      case aux_arb init_size size' t of {
                       Some res_b ->
                        case res_b of {
                         True  -> decOpt (decOptunique_ty t0) init_size;
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     IWrap f t t0 ->
                      case decOpt (decOptunique_ty f) init_size of {
                       Some res_b ->
                        case res_b of {
                         True ->
                          case decOpt (decOptunique_ty t) init_size of {
                           Some res_b0 ->
                            case res_b0 of {
                             True  -> aux_arb init_size size' t0;
                             False -> Some False};
                           None -> None};
                         False -> Some False};
                       None -> None};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Unwrap t -> aux_arb init_size size' t;
                     _        -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Let _ l t0 ->
                      case l of {
                       Nil      -> aux_arb init_size size' t0;
                       Cons _ _ -> Some False};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Let recty l t0 ->
                      case l of {
                       Nil -> Some False;
                       Cons b bs ->
                        case b of {
                         TermBind _ v t ->
                          case v of {
                           VarDecl x _ ->
                            case decOpt (decOptappears_bound_in_tm x t)
                                   init_size of {
                             Some res_b ->
                              case res_b of {
                               True -> Some False;
                               False ->
                                case decOpt
                                       (decOptappears_bound_in_tm x (Let
                                         recty bs t0)) init_size of {
                                 Some res_b0 ->
                                  case res_b0 of {
                                   True -> Some False;
                                   False ->
                                    case aux_arb init_size size' t of {
                                     Some res_b1 ->
                                      case res_b1 of {
                                       True ->
                                        aux_arb init_size size' (Let recty bs
                                          t0);
                                       False -> Some False};
                                     None -> None}};
                                 None -> None}};
                             None -> None}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Let recty l t0 ->
                      case l of {
                       Nil -> Some False;
                       Cons b bs ->
                        case b of {
                         TypeBind t t1 ->
                          case t of {
                           TyVarDecl x _ ->
                            case decOpt (decOptappears_bound_in_ty x t1)
                                   init_size of {
                             Some res_b ->
                              case res_b of {
                               True -> Some False;
                               False ->
                                case decOpt
                                       (decOptappears_bound_in_ann x (Let
                                         recty bs t0)) init_size of {
                                 Some res_b0 ->
                                  case res_b0 of {
                                   True -> Some False;
                                   False ->
                                    case decOpt (decOptunique_ty t1)
                                           init_size of {
                                     Some res_b1 ->
                                      case res_b1 of {
                                       True ->
                                        aux_arb init_size size' (Let recty bs
                                          t0);
                                       False -> Some False};
                                     None -> None}};
                                 None -> None}};
                             None -> None}};
                         _ -> Some False}};
                     _ -> Some False}) (Cons (\_ ->
                    case ty_0 of {
                     Let recty l t0 ->
                      case l of {
                       Nil -> Some False;
                       Cons b bs ->
                        case b of {
                         DatatypeBind d ->
                          case d of {
                           Datatype t _ _ _ ->
                            case t of {
                             TyVarDecl x _ ->
                              case decOpt
                                     (decOptappears_bound_in_ann x (Let recty
                                       bs t0)) init_size of {
                               Some res_b ->
                                case res_b of {
                                 True -> Some False;
                                 False ->
                                  aux_arb init_size size' (Let recty bs t0)};
                               None -> None}}};
                         _ -> Some False}};
                     _ -> Some False}) Nil))))))))))))))}}
             in aux_arb}
  in
  (\size -> aux_arb size size ty_)

dec_unique :: (Term String String String String) -> Nat -> Option Bool
dec_unique t =
  decOpt (decOptunique_tm t)

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
   Some' t v ->
    case y of {
     Some' t' v' ->
      case defaultUni_dec t t' of {
       Left  -> valueOf_eqb t' (eq_rect t v t') v';
       Right -> False}}}

typeIn_eqb :: DefaultUni -> Bool
typeIn_eqb _ =
  True

some_typeIn_eqb :: Eqb (Some0 ())
some_typeIn_eqb x y =
  case x of {
   Some' t _ ->
    case y of {
     Some' t' _ ->
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
is_cong_binding dec_R b b' =
  case b of {
   TermBind s v t ->
    case b' of {
     TermBind s' v' t' ->
      andb (andb (strictness_eqb s s') (vDecl_eqb v v')) (dec_R t t');
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
is_cong dec_R t t' =
  case t of {
   Let r bs t0 ->
    case t' of {
     Let r' bs' t'0 ->
      andb
        (andb (recursivity_eqb r r')
          (forall2b (is_cong_binding dec_R) bs bs')) (dec_R t0 t'0);
     _ -> False};
   Var n -> case t' of {
             Var n' -> eqb4 n n';
             _      -> False};
   TyAbs n k t0 ->
    case t' of {
     TyAbs n' k' t'0 ->
      andb (andb (eqb4 n n') (kind_eqb k k')) (dec_R t0 t'0);
     _ -> False};
   LamAbs n t0 t1 ->
    case t' of {
     LamAbs n' t'0 t'1 ->
      andb (andb (eqb4 n n') (ty_eqb t0 t'0)) (dec_R t1 t'1);
     _ -> False};
   Apply s t0 ->
    case t' of {
     Apply s' t'0 -> andb (dec_R s s') (dec_R t0 t'0);
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
     TyInst t'0 t'1 -> andb (ty_eqb t1 t'1) (dec_R t0 t'0);
     _              -> False};
   Error t0 -> case t' of {
                Error t'0 -> ty_eqb t0 t'0;
                _         -> False};
   IWrap t1 t2 t0 ->
    case t' of {
     IWrap t1' t2' t'0 ->
      andb (andb (ty_eqb t1 t1') (ty_eqb t2 t2')) (dec_R t0 t'0);
     _ -> False};
   Unwrap t0 -> case t' of {
                 Unwrap t'0 -> dec_R t0 t'0;
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
safely_removed b bs' =
  case negb (existsb (eqb4 (name_Binding b)) bs') of {
   True  -> is_pure_binding Nil b;
   False -> True}

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
       False -> andb (forallb (is_pure_binding Nil) bs) (dec_Term t y)};
     _ -> andb (forallb (is_pure_binding Nil) bs) (dec_Term t y)};
   _ -> is_cong dec_Term x y}
