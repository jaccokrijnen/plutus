-- TODO: this module adds a copy of the 'Value' type
-- in which the underlying maps are 'Data.AssocMap'.
{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
-- Prevent unboxing, which the plugin can't deal with
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}

-- We need -fexpose-all-unfoldings to compile the Marlowe validator with GHC 9.6.2.
-- TODO. Look into this more closely: see https://github.com/IntersectMBO/plutus/issues/6172.

-- | Functions for working with 'Value'.
module PlutusLedgerApi.V1.Data.Value (
  -- ** Currency symbols
  CurrencySymbol (..),
  currencySymbol,
  adaSymbol,

  -- ** Token names
  TokenName (..),
  tokenName,
  toString,
  adaToken,

  -- * Asset classes
  AssetClass (..),
  assetClass,
  assetClassValue,
  assetClassValueOf,

  -- ** Value
  Value (..),
  singleton,
  valueOf,
  withCurrencySymbol,
  currencySymbolValueOf,
  lovelaceValue,
  lovelaceValueOf,
  scale,
  symbols,

  -- * Partial order operations
  geq,
  gt,
  leq,
  lt,

  -- * Etc.
  isZero,
  split,
  unionWith,
  flattenValue,
  Lovelace (..),
) where

import Prelude qualified as Haskell

import Control.DeepSeq (NFData)
import Data.ByteString qualified as BS
import Data.Data (Data)
import Data.Function ((&))
import Data.String (IsString (fromString))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as E
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Bytes (LedgerBytes (LedgerBytes), encodeByteString)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), definitionIdFromType,
                                      definitionRef)
import PlutusTx.Blueprint.Schema (MapSchema (..), PairSchema (..), Schema (..), withSchemaInfo)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap (Map)
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List (List)
import PlutusTx.Lift (makeLift)
import PlutusTx.Ord qualified as Ord
import PlutusTx.Prelude as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.These (These (..))
import Prettyprinter (Pretty, (<>))
import Prettyprinter.Extras (PrettyShow (PrettyShow))

{-| ByteString representing the currency, hashed with /BLAKE2b-224/.
It is empty for `Ada`, 28 bytes for `MintingPolicyHash`.
Forms an `AssetClass` along with `TokenName`.
A `Value` is a map from `CurrencySymbol`'s to a map from `TokenName` to an `Integer`.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -- editorconfig-checker-disable-file
-}
newtype CurrencySymbol = CurrencySymbol
  { unCurrencySymbol :: PlutusTx.BuiltinByteString
  }
  deriving
    ( IsString
      -- ^ from hex encoding
    , Haskell.Show
      -- ^ using hex encoding
    , Pretty
      -- ^ using hex encoding
    )
    via LedgerBytes
  deriving stock (Generic, Data)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Eq
    , Ord
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )
  deriving anyclass (NFData, HasBlueprintDefinition)

instance HasBlueprintSchema CurrencySymbol referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    schema @PlutusTx.BuiltinByteString
      & withSchemaInfo \info ->
        info{title = Just "CurrencySymbol"}

-- | Creates `CurrencySymbol` from raw `ByteString`.
currencySymbol :: BS.ByteString -> CurrencySymbol
currencySymbol = CurrencySymbol . PlutusTx.toBuiltin
{-# INLINEABLE currencySymbol #-}

{-| ByteString of a name of a token.
Shown as UTF-8 string when possible.
Should be no longer than 32 bytes, empty for Ada.
Forms an `AssetClass` along with a `CurrencySymbol`.

This is a simple type without any validation, __use with caution__.
You may want to add checks for its invariants. See the
 [Shelley ledger specification](https://github.com/IntersectMBO/cardano-ledger/releases/download/cardano-ledger-spec-2023-04-03/shelley-ledger.pdf). -- editorconfig-checker-disable-file
-}
newtype TokenName = TokenName {unTokenName :: PlutusTx.BuiltinByteString}
  deriving stock (Generic, Data)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Eq
    , Ord
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )
  deriving anyclass (NFData, HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow TokenName)

-- | UTF-8 encoding. Doesn't verify length.
instance IsString TokenName where
  fromString = fromText . Text.pack

instance HasBlueprintSchema TokenName referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    schema @PlutusTx.BuiltinByteString
      & withSchemaInfo \info ->
        info{title = Just "TokenName"}

-- | Creates `TokenName` from raw `BS.ByteString`.
tokenName :: BS.ByteString -> TokenName
tokenName = TokenName . PlutusTx.toBuiltin
{-# INLINEABLE tokenName #-}

fromText :: Text -> TokenName
fromText = tokenName . E.encodeUtf8

fromTokenName :: (BS.ByteString -> r) -> (Text -> r) -> TokenName -> r
fromTokenName handleBytestring handleText (TokenName bs) =
  either (\_ -> handleBytestring $ PlutusTx.fromBuiltin bs) handleText
    $ E.decodeUtf8' (PlutusTx.fromBuiltin bs)

-- | Encode a `ByteString` to a hex `Text`.
asBase16 :: BS.ByteString -> Text
asBase16 bs = Text.concat ["0x", encodeByteString bs]

-- | Wrap the input `Text` in double quotes.
quoted :: Text -> Text
quoted s = Text.concat ["\"", s, "\""]

{-| Turn a TokenName to a hex-encoded 'String'

Compared to `show` , it will not surround the string with double-quotes.
-}
toString :: TokenName -> Haskell.String
toString = Text.unpack . fromTokenName asBase16 id

instance Haskell.Show TokenName where
  show = Text.unpack . fromTokenName asBase16 quoted

-- | The 'CurrencySymbol' of the 'Ada' currency.
adaSymbol :: CurrencySymbol
adaSymbol = CurrencySymbol emptyByteString
{-# INLINEABLE adaSymbol #-}

-- | The 'TokenName' of the 'Ada' currency.
adaToken :: TokenName
adaToken = TokenName emptyByteString
{-# INLINEABLE adaToken #-}

-- | An asset class, identified by a `CurrencySymbol` and a `TokenName`.
newtype AssetClass = AssetClass {unAssetClass :: (CurrencySymbol, TokenName)}
  deriving stock (Generic, Data)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Haskell.Show
    , Eq
    , Ord
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )
  deriving anyclass (NFData, HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow (CurrencySymbol, TokenName))

instance HasBlueprintSchema AssetClass referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    SchemaBuiltInPair emptySchemaInfo
      $ MkPairSchema
        { left = schema @CurrencySymbol
        , right = schema @TokenName
        }

-- | The curried version of 'AssetClass' constructor
assetClass :: CurrencySymbol -> TokenName -> AssetClass
assetClass s t = AssetClass (s, t)
{-# INLINEABLE assetClass #-}

{- Note [Value vs value]
We call two completely different things "values": the 'Value' type and a value within a key-value
pair. To distinguish between the two we write the former with a capital "V" and enclosed in single
quotes and we write the latter with a lower case "v" and without the quotes, i.e. 'Value' vs value.
-}

{- Note [Optimising Value]

We have attempted to improve the performance of 'Value' and other usages of
'PlutusTx.AssocMap.Map' by choosing a different representation for 'PlutusTx.AssocMap.Map',
see https://github.com/IntersectMBO/plutus/pull/5697.
This approach has been found to not be suitable, as the PR's description mentions.

Another approach was to define a specialised 'ByteStringMap', where the key type was 'BuiltinByteString',
since that is the representation of both 'CurrencySymbol' and 'TokenName'.
Unfortunately, this approach actually had worse performance in practice. We believe it is worse
because having two map libraries would make some optimisations, such as CSE, less effective.
We base this on the fact that turning off all optimisations ended up making the code more performant.
See https://github.com/IntersectMBO/plutus/pull/5779 for details on the experiment done.
-}

-- See Note [Value vs value].
-- See Note [Optimising Value].

{-| The 'Value' type represents a collection of amounts of different currencies.
We can think of 'Value' as a vector space whose dimensions are currencies.

Operations on currencies are usually implemented /pointwise/. That is,
we apply the operation to the quantities for each currency in turn. So
when we add two 'Value's the resulting 'Value' has, for each currency,
the sum of the quantities of /that particular/ currency in the argument
'Value'. The effect of this is that the currencies in the 'Value' are "independent",
and are operated on separately.

Whenever we need to get the quantity of a currency in a 'Value' where there
is no explicit quantity of that currency in the 'Value', then the quantity is
taken to be zero.

There is no 'Ord Value' instance since 'Value' is only a partial order, so 'compare' can't
do the right thing in some cases.
-}
newtype Value = Value {getValue :: Map CurrencySymbol (Map TokenName Integer)}
  deriving stock (Generic, Haskell.Show)
  deriving newtype (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
  deriving Pretty via (PrettyShow Value)

instance HasBlueprintDefinition Value where
  type Unroll Value = '[Value, CurrencySymbol, TokenName, Integer]
  definitionId = definitionIdFromType @Value

instance HasBlueprintSchema Value referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    SchemaMap
      emptySchemaInfo
        { title = Just "Value"
        }
      MkMapSchema
        { keySchema = definitionRef @CurrencySymbol
        , valueSchema =
            SchemaMap
              emptySchemaInfo
              MkMapSchema
                { keySchema = definitionRef @TokenName
                , valueSchema = definitionRef @Integer
                , minItems = Nothing
                , maxItems = Nothing
                }
        , minItems = Nothing
        , maxItems = Nothing
        }

instance Haskell.Eq Value where
  (==) = eq

instance Eq Value where
  {-# INLINEABLE (==) #-}
  (==) = eq

instance Haskell.Semigroup Value where
  (<>) = unionWith (+)

instance Semigroup Value where
  {-# INLINEABLE (<>) #-}
  (<>) = unionWith (+)

instance Haskell.Monoid Value where
  mempty = Value Map.empty

instance Monoid Value where
  {-# INLINEABLE mempty #-}
  mempty = Value Map.empty

instance Group Value where
  {-# INLINEABLE inv #-}
  inv = scale @Integer @Value (-1)

deriving via (Additive Value) instance AdditiveSemigroup Value
deriving via (Additive Value) instance AdditiveMonoid Value
deriving via (Additive Value) instance AdditiveGroup Value

instance Module Integer Value where
  {-# INLINEABLE scale #-}
  scale i (Value xs) = Value (Map.map (Map.map (\i' -> i * i')) xs)

instance JoinSemiLattice Value where
  {-# INLINEABLE (\/) #-}
  (\/) = unionWith Ord.max

instance MeetSemiLattice Value where
  {-# INLINEABLE (/\) #-}
  (/\) = unionWith Ord.min

{-| Get the quantity of the given currency in the 'Value'.
Assumes that the underlying map doesn't contain duplicate keys.
-}
valueOf :: Value -> CurrencySymbol -> TokenName -> Integer
valueOf value cur tn =
  withCurrencySymbol cur value 0 \tokens ->
    case Map.lookup tn tokens of
      Nothing -> 0
      Just v  -> v
{-# INLINEABLE valueOf #-}

{-| Apply a continuation function to the token quantities of the given currency
symbol in the value or return a default value if the currency symbol is not present
in the value.
-}
withCurrencySymbol :: CurrencySymbol -> Value -> a -> (Map TokenName Integer -> a) -> a
withCurrencySymbol currency value def k =
  case Map.lookup currency (getValue value) of
    Nothing              -> def
    Just tokenQuantities -> k tokenQuantities
{-# INLINEABLE withCurrencySymbol #-}

{-| Get the total value of the currency symbol in the 'Value' map.
Assumes that the underlying map doesn't contain duplicate keys.

Note that each token of the currency symbol may have a value that is positive,
zero or negative.
-}
currencySymbolValueOf :: Value -> CurrencySymbol -> Integer
currencySymbolValueOf value cur = withCurrencySymbol cur value 0 \tokens ->
  -- This is more efficient than `PlutusTx.sum (Map.elems tokens)`, because
  -- the latter materializes the intermediate result of `Map.elems tokens`.
  Map.foldr (\amt acc -> amt + acc) 0 tokens
{-# INLINEABLE currencySymbolValueOf #-}

-- | The list of 'CurrencySymbol's of a 'Value'.
symbols :: Value -> List CurrencySymbol
symbols (Value mp) = Map.keys mp
{-# INLINEABLE symbols #-}

-- | Make a 'Value' containing only the given quantity of the given currency.
singleton :: CurrencySymbol -> TokenName -> Integer -> Value
singleton c tn i = Value (Map.singleton c (Map.singleton tn i))
{-# INLINEABLE singleton #-}

-- | A 'Value' containing the given quantity of Lovelace.
lovelaceValue :: Lovelace -> Value
lovelaceValue = singleton adaSymbol adaToken . getLovelace
{-# INLINEABLE lovelaceValue #-}

-- | Get the quantity of Lovelace in the 'Value'.
lovelaceValueOf :: Value -> Lovelace
lovelaceValueOf v = Lovelace (valueOf v adaSymbol adaToken)
{-# INLINEABLE lovelaceValueOf #-}

-- | A 'Value' containing the given amount of the asset class.
assetClassValue :: AssetClass -> Integer -> Value
assetClassValue (AssetClass (c, t)) = singleton c t
{-# INLINEABLE assetClassValue #-}

-- | Get the quantity of the given 'AssetClass' class in the 'Value'.
assetClassValueOf :: Value -> AssetClass -> Integer
assetClassValueOf v (AssetClass (c, t)) = valueOf v c t
{-# INLINEABLE assetClassValueOf #-}

-- | Combine two 'Value' maps, assumes the well-definedness of the two maps.
unionVal :: Value -> Value -> Map CurrencySymbol (Map TokenName (These Integer Integer))
unionVal (Value l) (Value r) =
  let
    combined = Map.union l r
    unThese k = case k of
      This a    -> Map.map This a
      That b    -> Map.map That b
      These a b -> Map.union a b
   in
    Map.map unThese combined
{-# INLINEABLE unionVal #-}

{-| Combine two 'Value' maps with the argument function.
Assumes the well-definedness of the two maps.
-}
unionWith :: (Integer -> Integer -> Integer) -> Value -> Value -> Value
unionWith f ls rs =
  let
    combined = unionVal ls rs
    unThese k' = case k' of
      This a    -> f a 0
      That b    -> f 0 b
      These a b -> f a b
   in
    Value (Map.map (Map.map unThese) combined)
{-# INLINEABLE unionWith #-}

{-| Convert a 'Value' to a simple list, keeping only the non-zero amounts.
Note that the result isn't sorted, meaning @v1 == v2@ doesn't generally imply
@flattenValue v1 == flattenValue v2@.
Also assumes that there are no duplicate keys in the 'Value' 'Map'.
-}
flattenValue :: Value -> [(CurrencySymbol, TokenName, Integer)]
flattenValue v = goOuter [] (Map.toSOPList $ getValue v)
 where
  goOuter acc []             = acc
  goOuter acc ((cs, m) : tl) = goOuter (goInner cs acc (Map.toSOPList m)) tl

  goInner _ acc [] = acc
  goInner cs acc ((tn, a) : tl)
    | a /= 0 = goInner cs ((cs, tn, a) : acc) tl
    | otherwise = goInner cs acc tl
{-# INLINEABLE flattenValue #-}

-- Num operations

-- | Check whether a 'Value' is zero.
isZero :: Value -> Bool
isZero (Value xs) = Map.all (Map.all (\i -> 0 == i)) xs
{-# INLINEABLE isZero #-}

{-| Checks whether a predicate holds for all the values in a 'Value'
union. Assumes the well-definedness of the two underlying 'Map's.
-}
checkPred :: (These Integer Integer -> Bool) -> Value -> Value -> Bool
checkPred f l r =
  let
    inner :: Map TokenName (These Integer Integer) -> Bool
    inner = Map.all f
   in
    Map.all inner (unionVal l r)
{-# INLINEABLE checkPred #-}

{-| Check whether a binary relation holds for value pairs of two 'Value' maps,
  supplying 0 where a key is only present in one of them.
-}
checkBinRel :: (Integer -> Integer -> Bool) -> Value -> Value -> Bool
checkBinRel f l r =
  let
    unThese k' = case k' of
      This a    -> f a 0
      That b    -> f 0 b
      These a b -> f a b
   in
    checkPred unThese l r
{-# INLINEABLE checkBinRel #-}

{-| Check whether one 'Value' is greater than or equal to another. See 'Value' for an explanation
of how operations on 'Value's work.
-}
geq :: Value -> Value -> Bool
-- If both are zero then checkBinRel will be vacuously true, but this is fine.
geq = checkBinRel (>=)
{-# INLINEABLE geq #-}

{-| Check whether one 'Value' is less than or equal to another. See 'Value' for an explanation of
how operations on 'Value's work.
-}
leq :: Value -> Value -> Bool
-- If both are zero then checkBinRel will be vacuously true, but this is fine.
leq = checkBinRel (<=)
{-# INLINEABLE leq #-}

{-| Check whether one 'Value' is strictly greater than another.
This is *not* a pointwise operation. @gt l r@ means @geq l r && not (eq l r)@.
-}
gt :: Value -> Value -> Bool
gt l r = geq l r && not (eq l r)
{-# INLINEABLE gt #-}

{-| Check whether one 'Value' is strictly less than another.
This is *not* a pointwise operation. @lt l r@ means @leq l r && not (eq l r)@.
-}
lt :: Value -> Value -> Bool
lt l r = leq l r && not (eq l r)
{-# INLINEABLE lt #-}

{-| Split a 'Value' into its positive and negative parts. The first element of
  the tuple contains the negative parts of the 'Value', the second element
  contains the positive parts.

  @negate (fst (split a)) `plus` (snd (split a)) == a@
-}
split :: Value -> (Value, Value)
split (Value mp) = (negate (Value neg), Value pos)
 where
  (neg, pos) = Map.mapThese splitIntl mp

  splitIntl :: Map TokenName Integer -> These (Map TokenName Integer) (Map TokenName Integer)
  splitIntl mp' = These l r
   where
    (l, r) = Map.mapThese (\i -> if i <= 0 then This i else That i) mp'
{-# INLINEABLE split #-}

{-| Check equality of two lists of distinct key-value pairs, each value being uniquely
identified by a key, given a function checking whether a 'Value' is zero and a function
checking equality of values. Note that the caller must ensure that the two lists are
well-defined in this sense. This is not checked or enforced in `unordEqWith`, and therefore
it might yield undefined results for ill-defined input.

This function recurses on both the lists in parallel and checks whether the key-value pairs are
equal pointwise. If there is a mismatch, then it tries to find the left key-value pair in the right
list. If that succeeds then the pair is removed from both the lists and recursion proceeds pointwise
as before until there's another mismatch. If at some point a key-value pair from the left list is
not found in the right one, then the function returns 'False'. If the left list is exhausted, but
the right one still has some non-zero elements, the function returns 'False' as well.

We check equality of values of two key-value pairs right after ensuring that the keys match. This is
disadvantageous if the values are big and there's a key that is present in one of the lists but not
in the other, since in that case computing equality of values was expensive and pointless. However

1. we've checked and on the chain 'Value's very rarely contain 'CurrencySymbol's with more than 3
   'TokenName's associated with them, so we optimize for the most common use case
2. computing equality of values before ensuring equality of all the keys certainly does help when we
   check equality of 'TokenName'-value pairs, since the value of a 'TokenName' is an 'Integer' and
   @(==) :: Integer -> Integer -> Bool@ is generally much faster than repeatedly searching for keys
   in a list
3. having some clever logic for computing equality of values right away in some cases, but not in
   others would not only complicate the algorithm, but also increase the size of the function and
   this resource is quite scarce as the size of a program growing beyond what's acceptable by the
   network can be a real deal breaker, while general performance concerns don't seem to be as
   pressing

The algorithm we use here is very similar, if not identical, to @valueEqualsValue4@ from
https://github.com/IntersectMBO/plutus/issues/5135
-}
unordEqWith
  :: (BuiltinData -> Bool)
  -> (BuiltinData -> BuiltinData -> Bool)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> Bool
unordEqWith is0 eqV = goBoth
 where
  goBoth
    :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
    -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
    -> Bool
  goBoth l1 l2 =
    B.matchList
      l1
      -- null l1 case
      ( \() ->
          B.matchList
            l2
            -- null l2 case
            (\() -> True)
            -- non-null l2 case
            (\_ _ -> Map.all is0 (Map.unsafeFromBuiltinList l2 :: Map BuiltinData BuiltinData))
      )
      -- non-null l1 case
      ( \hd1 tl1 ->
          B.matchList
            l2
            -- null l2 case
            (\() -> Map.all is0 (Map.unsafeFromBuiltinList l1 :: Map BuiltinData BuiltinData))
            -- non-null l2 case
            ( \hd2 tl2 ->
                let
                  k1 = BI.fst hd1
                  v1 = BI.snd hd1
                  k2 = BI.fst hd2
                  v2 = BI.snd hd2
                 in
                  if k1 == k2
                    then
                      if eqV v1 v2
                        then goBoth tl1 tl2
                        else False
                    else
                      if is0 v1
                        then goBoth tl1 l2
                        else
                          let
                            goRight
                              :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
                              -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
                              -> Bool
                            goRight acc l =
                              B.matchList
                                l
                                -- null l case
                                (\() -> False)
                                -- non-null l case
                                ( \hd tl ->
                                    let
                                      k = BI.fst hd
                                      v = BI.snd hd
                                     in
                                      if is0 v
                                        then goRight acc tl
                                        else
                                          if k == k1
                                            then
                                              if eqV v1 v
                                                then goBoth tl1 (revAppend' acc tl)
                                                else False
                                            else goRight (hd `BI.mkCons` acc) tl
                                )
                           in
                            goRight
                              ( if is0 v2
                                  then BI.mkNilPairData BI.unitval
                                  else hd2 `BI.mkCons` BI.mkNilPairData BI.unitval
                              )
                              tl2
            )
      )

  revAppend' = rev
   where
    rev l acc =
      B.matchList
        l
        (\() -> acc)
        ( \hd tl ->
            rev tl (hd `BI.mkCons` acc)
        )
{-# INLINEABLE unordEqWith #-}

-- | Check equality of two maps of maps indexed by 'CurrencySymbol's,

--- given a function checking whether a value is zero and a function
-- checking equality of values.
eqMapOfMapsWith
  :: (Map TokenName Integer -> Bool)
  -> (Map TokenName Integer -> Map TokenName Integer -> Bool)
  -> Map CurrencySymbol (Map TokenName Integer)
  -> Map CurrencySymbol (Map TokenName Integer)
  -> Bool
eqMapOfMapsWith is0 eqV map1 map2 =
  let xs1 = Map.toBuiltinList map1
      xs2 = Map.toBuiltinList map2
      is0' v = is0 (unsafeFromBuiltinData v)
      eqV' v1 v2 = eqV (unsafeFromBuiltinData v1) (unsafeFromBuiltinData v2)
   in unordEqWith is0' eqV' xs1 xs2
{-# INLINEABLE eqMapOfMapsWith #-}

{-| Check equality of two 'Map Token Integer's given a function checking whether a value is zero and a function
checking equality of values.
-}
eqMapWith
  :: (Integer -> Bool)
  -> (Integer -> Integer -> Bool)
  -> Map TokenName Integer
  -> Map TokenName Integer
  -> Bool
eqMapWith is0 eqV map1 map2 =
  let xs1 = Map.toBuiltinList map1
      xs2 = Map.toBuiltinList map2
      is0' v = is0 (unsafeFromBuiltinData v)
      eqV' v1 v2 = eqV (unsafeFromBuiltinData v1) (unsafeFromBuiltinData v2)
   in unordEqWith is0' eqV' xs1 xs2
{-# INLINEABLE eqMapWith #-}

{-| Check equality of two 'Value's. Does not assume orderness of lists within a 'Value' or a lack
of empty values (such as a token whose quantity is zero or a currency that has a bunch of such
tokens or no tokens at all), but does assume that no currencies or tokens within a single
currency have multiple entries.
-}
eq :: Value -> Value -> Bool
eq (Value currs1) (Value currs2) =
  eqMapOfMapsWith (Map.all (0 ==)) (eqMapWith (0 ==) (==)) currs1 currs2
{-# INLINEABLE eq #-}

newtype Lovelace = Lovelace {getLovelace :: Integer}
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow Lovelace)
  deriving anyclass (HasBlueprintDefinition)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Haskell.Show
    , Haskell.Num
    , Haskell.Real
    , Haskell.Enum
    , PlutusTx.Eq
    , PlutusTx.Ord
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    , PlutusTx.AdditiveSemigroup
    , PlutusTx.AdditiveMonoid
    , PlutusTx.AdditiveGroup
    , PlutusTx.Show
    )

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''CurrencySymbol)
$(makeLift ''TokenName)
$(makeLift ''AssetClass)
$(makeLift ''Value)
$(makeLift ''Lovelace)
