module Example where

import qualified Prelude

type Float = Prelude.Float

onef :: Float
onef = 1.0

data Dual =
   Build_dual Float Float

identity :: Float -> Dual
identity x =
  Build_dual x onef

