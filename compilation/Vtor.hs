module Vtor where
import Data.List

data Vtor t =
  NilV
  | ConsV t Int (Vtor t)
  
