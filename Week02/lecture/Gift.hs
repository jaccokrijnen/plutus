
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ViewPatterns        #-}

module Gift where

import PlutusLedgerApi.V2
import PlutusTx (BuiltinData, CompiledCode (..), compile)
import PlutusTx.IsData (unstableMakeIsData)
import PlutusTx.Prelude (traceError, (<=))
import Prelude (Bool (..), IO, Integer, ($))
-- import           Utilities            (writeValidatorToFile)

---------------------------------------------------------------------------------------------------
-------------------------------- ON-CHAIN CODE / VALIDATOR ----------------------------------------

data EndDate = Fixed Integer | Never
unstableMakeIsData ''EndDate -- Use TH to create an instance for IsData.

check :: Bool -> ()
check True  = ()
check False = traceError "Script returned false"

-- This validator always succeeds
--                    Datum         Redeemer     ScriptContext
mkGiftValidator :: EndDate -> Integer -> BuiltinData -> ()
mkGiftValidator end current _ =
    let
        {-# NOINLINE inlineMe #-}
        inlineMe = current
        {-# NOINLINE remove#-}
        remove = Fixed 3
        {-# NOINLINE keep#-}
        keep   = case Never of {Never -> False;_ -> True}
    in case end of
    Fixed n -> check (n <= inlineMe)
    Never   -> check keep
{-# INLINABLE mkGiftValidator #-}

validatorGift :: PlutusTx.CompiledCode (EndDate -> Integer -> BuiltinData -> ())
validatorGift = $$(PlutusTx.compile [|| mkGiftValidator ||])

-- validator :: PlutusTx.CompiledCode (EndDate -> Integer -> BuiltinData -> Bool)
-- validator = $$(PlutusTx.compile [|| mkPastEnd ||])




-- | Copied from Plutus.Script.Utils.Typed (in plutus-apps)
-- I don't know how to properly depend on plutus-apps while using local plutus
-- master branch
type UntypedValidator = BuiltinData -> BuiltinData -> BuiltinData -> ()

mkUntypedValidator
    :: (UnsafeFromData d, UnsafeFromData r, UnsafeFromData sc)
    => (d -> r -> sc -> Bool)
    -> UntypedValidator
-- We can use unsafeFromBuiltinData here as we would fail immediately anyway if parsing failed
mkUntypedValidator f d r p =
    check $ f (unsafeFromBuiltinData d)
              (unsafeFromBuiltinData r)
              (unsafeFromBuiltinData p)

-- validator :: PlutusTx.CompiledCode (EndDate -> Integer -> Bool)
-- validator = $$(PlutusTx.compile [|| mkPastEnd ||])
---------------------------------------------------------------------------------------------------
------------------------------------- HELPER FUNCTIONS --------------------------------------------

-- saveVal :: IO ()
-- saveVal = writeValidatorToFile "./assets/gift.plutus" validator
