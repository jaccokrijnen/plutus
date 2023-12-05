{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Burn where

import PlutusLedgerApi.V2 qualified as PlutusV2
import PlutusTx (BuiltinData, compile)
import PlutusTx.Prelude (traceError)
import Prelude (IO)
-- import           Utilities            (writeValidatorToFile)

---------------------------------------------------------------------------------------------------
----------------------------------- ON-CHAIN / VALIDATOR ------------------------------------------

-- This validator always fails
--                    Datum         Redeemer     ScriptContext
mkBurnValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkBurnValidator _ _ _ = traceError "it burns!!!"
{-# INLINABLE mkBurnValidator #-}

validator :: PlutusV2.Validator
validator = PlutusV2.mkValidatorScript $$(PlutusTx.compile [|| mkBurnValidator ||])

---------------------------------------------------------------------------------------------------
------------------------------------- HELPER FUNCTIONS --------------------------------------------

-- saveVal :: IO ()
-- saveVal = writeValidatorToFile "./assets/burn.plutus" validator
