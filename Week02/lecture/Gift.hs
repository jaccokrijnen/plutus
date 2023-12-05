{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Gift where

import PlutusLedgerApi.V2 qualified as PlutusV2
import PlutusTx (BuiltinData, CompiledCode (..), compile)
import Prelude (Bool (..), IO, Integer, (<=))
-- import           Utilities            (writeValidatorToFile)

---------------------------------------------------------------------------------------------------
-------------------------------- ON-CHAIN CODE / VALIDATOR ----------------------------------------

data EndDate = Fixed Integer | Never

-- This validator always succeeds
--                    Datum         Redeemer     ScriptContext
mkGiftValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkGiftValidator _ _ _ = ()
{-# INLINABLE mkGiftValidator #-}

validator :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
validator = $$(PlutusTx.compile [|| mkGiftValidator ||])

pastEnd :: PlutusTx.CompiledCode (EndDate -> Integer -> Bool)
pastEnd = $$(compile [|| \(end::EndDate) (current::Integer) ->
    let remove = Fixed 3
        keep   = case Never of {Never -> False;_ -> True}
    in case end of
    Fixed n -> n <= current
    Never   -> keep
  ||])
---------------------------------------------------------------------------------------------------
------------------------------------- HELPER FUNCTIONS --------------------------------------------

-- saveVal :: IO ()
-- saveVal = writeValidatorToFile "./assets/gift.plutus" validator
