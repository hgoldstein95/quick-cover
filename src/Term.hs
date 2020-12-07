{-# LANGUAGE DeriveGeneric #-}

module Term where

import Data.List (intercalate)
import GHC.Generics (Generic)

data Term a = Term a [Term a]
  deriving (Eq, Ord, Generic)

instance Show a => Show (Term a) where
  show (Term c []) = show c
  show (Term c xs) = show c ++ "(" ++ intercalate ", " (show <$> xs) ++ ")"
