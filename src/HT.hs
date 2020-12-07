module HT where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Universe.Helpers (choices)
import Term
import Test.QuickCheck

type Ty = String

data Description a
  = Top
  | Cons
      a
      [Description a]
  | Eventually (Description a)
  | Next (Description a)
  deriving (Eq, Ord)

type HT a = Map Ty [(a, [Ty])]

instance Show a => Show (Description a) where
  show Top = "⊤"
  show (Cons c []) = show c
  show (Cons c ts) = show c ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"
  show (Eventually d) = "(⋄" ++ show d ++ ")"
  show (Next d) = "(⚬" ++ show d ++ ")"

matches :: Eq a => Term a -> Description a -> Bool
matches _ Top = True
matches (Term c' as') (Cons c as) =
  c == c'
    && length as == length as'
    && all (uncurry . flip $ matches) (zip as as')
matches (Term _ as) (Next d) = any (`matches` d) as
matches t@(Term _ as) (Eventually d) =
  t `matches` d || any (`matches` Eventually d) as

splitN :: Int -> Int -> [[Int]]
splitN _ 0 = [[]]
splitN n l = do
  x <- [0 .. n]
  xs <- splitN (n - x) (l - 1)
  pure $ x : xs

covers :: Ord a => Int -> Term a -> [Description a]
covers 0 _ = [Top]
covers n (Term c args) =
  S.toList . S.fromList $
    (covers n =<< args)
      ++ [ Eventually (Cons c args')
           | ns <- splitN (n - 1) (length args),
             args' <- choices $ uncurry covers <$> zip ns args
         ]

reachableNext :: HT a -> Ty -> Set Ty
reachableNext h t = S.fromList . concatMap snd $ h M.! t

reachableEventually :: HT a -> Ty -> Set Ty
reachableEventually h t = go (S.singleton t)
  where
    go :: Set Ty -> Set Ty
    go ts =
      let new = S.unions . map (reachableNext h) $ S.toList ts
          ts' = ts `S.union` new
       in if ts == ts'
            then ts
            else go ts'

-- gen :: Int -> HT -> Ty -> [Description]
-- gen n h t = Eventually <$> genC n h t

gen :: Int -> HT a -> Ty -> [Description a]
gen 0 _ _ = pure Top
gen n h t = [Eventually d | t' <- reach, d <- genC n h t']
  where
    reach = S.toList $ reachableEventually h t

genC :: Int -> HT a -> Ty -> [Description a]
genC 0 _ _ = pure Top
genC n h t = do
  (c, ts) <- cs
  ms <- splitN n' (length ts)
  Cons c <$> sequence [gen m h ty | (m, ty) <- zip ms ts]
  where
    cs = h M.! t
    n' =
      if length cs == 1
        then n
        else n - 1

data Spec a t = Spec
  { specH :: HT t,
    specTy :: Ty,
    specToTerm :: a -> Term t,
    specFromTerm :: Term t -> a,
    specGen :: Gen a
  }

type ThrownAway = Int

ccomb :: (Ord a, Ord t) => Spec a t -> Int -> Gen ([a], ThrownAway)
ccomb spec k = do
  (es, ta) <- fst <$> genTerms (0 :: Int) (0 :: Int) (S.fromList $ gen k h ty) S.empty
  pure (S.toList es, ta)
  where
    h = specH spec
    ty = specTy spec
    genTerms ta n ds es
      | S.null ds = pure ((es, ta), 0)
      | otherwise =
        if n == 100 -- we've gone through 100 examples without adding coverage
          then pure ((es, ta), n)
          else do
            x <- specGen spec
            let t = specToTerm spec x
            if any (matches t) ds
              then genTerms ta 0 (ds S.\\ S.fromList (covers k t)) (S.insert x es)
              else genTerms (ta + 1) (n + 1) ds es

combCheck :: (Ord a, Ord t) => Spec a t -> Int -> (a -> Bool) -> IO ()
combCheck spec t prop = do
  (tests, _) <- generate $ ccomb spec t
  mapM_ (quickCheck . prop) tests
