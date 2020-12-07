{-# LANGUAGE TupleSections, FlexibleInstances, InstanceSigs #-}
module QuickCheckEnum where

import System.Random
import System.Clock
import System.Timeout
import System.IO.Unsafe (unsafePerformIO)
import Data.List( group, sort, sortBy, intersperse, transpose )
import Control.Monad( ap, liftM2, liftM3, liftM4, MonadPlus, mzero, mplus, msum )
import Control.Applicative( Alternative, empty, (<|>) )
import Control.Arrow (first)
import Data.Function (on)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either

import Control.Monad.Random hiding (interleave)
--import qualified Data.Urn as Urn

import Control.Monad.Logic.Class

import Debug.Trace

import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (race)

infixr 0 ==>
infix  1 `classify`

--------------------------------------------------------------------
-- Generator

{- begin Hybrid -}
newtype Gen a = Gen { run :: Int -> StdGen -> [a] }
{- end Hybrid -}

sized :: (Int -> Gen a) -> Gen a
sized fgen = Gen (\n r -> run (fgen n) n r)

resize :: Int -> Gen a -> Gen a
resize n g = Gen (\_ r -> run g n r)

rand :: Gen StdGen
rand = Gen (\n r -> [r])

-- TODO: Oneof
{- begin promote -}
promote :: (a -> Gen b) -> Gen (a -> b)
promote f = Gen (\n r -> [ \a -> head $ run (f a) n r ])
{- end promote -}

variant :: Int -> Gen a -> Gen a
variant v g = Gen (\n r -> run g n (rands r !! (v+1)))
 where
  rands r0 = r1 : rands r2 where (r1, r2) = split r0

generate :: Int -> StdGen -> Gen a -> a
generate n rnd g = head $ run g size rnd'
 where
  (size, rnd') = randomR (0, n) rnd

generateSafe :: Int -> StdGen -> Gen a -> Maybe a
generateSafe n rnd g =
  case run g size rnd' of
    [] -> Nothing
    x : _ -> Just x
 where
  (size, rnd') = randomR (0, n) rnd


generate' :: Int -> StdGen -> Gen a -> [a]
generate' n rnd g = run g size rnd'
 where
  (size, rnd') = randomR (0, n) rnd

instance Functor Gen where
  fmap f m = m >>= return . f

{- begin HybridMonad -}
instance Monad Gen where
  return :: a -> Gen    a
  return a = Gen (\n r -> [a])

  (>>=) :: Gen a -> (a -> Gen b) -> Gen b
  g >>= k =
    Gen (\n r0 ->
      let (r1,r2) = split r0
          aux r [] = []
          aux r (a:as) =
            let (r1, r2) = split r in
            run (k a) n r1 ++ aux r2 as
      in aux r2 (run g n r1))
{- end HybridMonad -}

{- begin mix -}
mix :: Gen a -> Gen a -> Gen a
mix g1 g2 = Gen (\n r0 -> let (switch, r1) = random r0
                          in if switch then run g1 n r1 else run g2 n r1)
{- end mix -}

{- begin enumerate -}
enumerate :: [a] -> Gen a
enumerate xs = Gen (\_ _ -> xs)
{- end enumerate -}

{- begin takeG -}
takeG :: Int -> Gen a -> Gen a
takeG n g = Gen (\s r -> take n $ run g s r)
{- end takeG -}

{- begin liftListFn -}
liftListFn :: ([a]->[a]) -> Gen a -> Gen a
liftListFn f g = Gen (\s r -> f $ run g s r)
{- end liftListFn -}

nubOrdG :: Ord a => Gen a -> Gen a
nubOrdG = liftListFn $ nubOrd Set.empty
  where nubOrd s [] = []
        nubOrd s (x:xs) = if Set.member x s then nubOrd s xs else x : nubOrd (Set.insert x s) xs

{- begin cut -}
cut :: Gen a -> Gen a
cut = takeG 1
{- end cut -}

{- begin filterG -}
filterG :: (a -> Bool) -> Gen a -> Gen a
filterG pred = liftListFn (filter pred) -- Gen (\s r -> filter pred $ run g s r)
{- end filterG -}

-- derived
choose :: Random a => (a, a) -> Gen a
choose bounds = (fst . randomR bounds) `fmap` rand

{- begin elements -}
elements :: [a] -> Gen a
elements [] = empty
-- Used to be: elements [] = error "QuickCheck.elements used with empty list"
elements xs = (xs !!) `fmap` choose (0, length xs - 1)
{- end elements -}

-- At each step pick from g1 and g2 randomly according to weight.
{- begin weightedChoice -}
weightedChoice :: (Int, Gen a) -> (Int, Gen a) -> Gen a
weightedChoice (w1, g1) (w2, g2) =
  Gen (\s r0 ->
         let (r1, r2) = split r0
             (r1', r2') = split r1
         in weightedInterleave w1 w2 r2 (run g1 s r1') (run g2 s r2'))
{- end weightedChoice -}

{- begin weightedInterleave -}
weightedInterleave :: Int -> Int -> StdGen -> [a] -> [a] -> [a]
weightedInterleave _ _ _ l1 [] = l1
weightedInterleave _ _ _ [] l2 = l2
weightedInterleave w1 w2 r l1@(x:xs) l2@(y:ys)
  = let (switch, r2) = randomR (1,w1+w2) r
    in if switch <= w1
       then x : weightedInterleave w1 w2 r2 xs l2
       else y : weightedInterleave w1 w2 r2 l1 ys
{- end weightedInterleave -}

{- begin randomize' -}
randomize' :: Gen a -> Gen a
randomize' g =
  Gen (\n r0 ->
         let (r1, r2) = split r0
             ns = randoms r1 :: [Int]
             as = run g n r2
             ordered = sortBy (compare `on` fst) $ zip ns as
         in map snd ordered)
{- end randomize' -}

{- begin randomOrder' -}
randomOrder' :: [a] -> Gen a
randomOrder' = randomize' . enumerate
{- end randomOrder' -}

{- begin permuteWeighted -}
{-
permuteWeighted :: [(Int, a)] -> Gen [a]
permuteWeighted x =
  let Just u = Urn.fromList $ map (first fromIntegral) x
      aux u = do (w, a, mu) <- Urn.remove u
                 case mu of
                   Just u' -> (a:) <$> aux u'
                   _       -> pure [a]
  in aux u
-}
{- end permuteWeighted -}

{- begin randomize -}
{-
randomize :: Gen a -> Gen a
randomize g =
  Gen (\n r0 ->
         let (r1, r2) = split r0
             weightedValues = map (1, ) $ run g n r1
         in concat $ run (permuteWeighted weightedValues) n r2)
-}
-- De-urned
randomize :: Gen a -> Gen a
randomize g =
  Gen (\n r0 ->
         let (r1, r2) = split r0
             ns = randoms r1 :: [Int]
             as = run g n r2
             ordered = sortBy (compare `on` fst) $ zip ns as
         in map snd ordered)
{- end randomize -}

instance MonadRandom Gen where
  getRandomR = choose
--instance Urn.MonadSample Gen 

{- begin randomOrderOld -}
randomOrderOld :: [a] -> Gen a
randomOrderOld = randomize . enumerate
{- end randomOrderOld -}

{-
randomOrder'old :: [a] -> Gen a
randomOrder'old xs = do
  xs' <- permuteWeighted $ map (1,) xs
  enumerate xs'
-}

randomOrderN :: Int -> (Int, Int) -> Gen Int
randomOrderN n (l,h) = aux n Set.empty 
  where aux 0 s = empty
        aux n s = do
          mx <- choose (l,h) `suchThatMaybe` (\x -> not $ Set.member x s)
          case mx of
            Just x -> (pure x) <|>  aux (n-1) (Set.insert x s)
            Nothing -> empty

randomOrder :: (Int, Int) -> Gen Int 
randomOrder (l,h) = randomOrderN 10 (l,h)

-- This is just alternateM or something? mplus?
randomOrderN' :: Int -> (Int, Int) -> Gen Int
randomOrderN' n (l,h) = aux n
  where aux 0 = empty
        aux n = choose (l,h) <|> aux (n-1)

-- Pick and drop a specific item from a list with no weights.
pickDropUnbiased :: a -> [a] -> Int -> (a, [a])
pickDropUnbiased def xs n
  = case xs of
      [] -> (def, [])
      (x : xs) -> if n <= 0 then (x, xs)
                   else let (x', xs') = pickDropUnbiased def xs (n-1)
                        in (x', x : xs')

{- begin shuffleGens -}
shuffleGens :: [Gen a] -> Gen a
shuffleGens = randomize . allof
{- end shuffleGens -}

{- begin shuffleGens' -}
shuffleGens' :: [Gen a] -> Gen a
shuffleGens' = randomize' . allof
{- end shuffleGens' -}

-- Not sure how performance compares. I'd think this is worse, but I recall it was performing better.
shuffleGensOld :: [Gen a] -> Gen a
shuffleGensOld gs = shuffle' (length gs) gs
  where
    shuffle' :: Int -> [Gen a] -> Gen a
    shuffle' 0 _ = empty
    shuffle' _ [] = empty
    shuffle' n gs
      = do let n' = n - 1
           i <- choose (0, length gs - 1);;
           let (g, gs') = pickDropUnbiased empty gs i
           g <|> shuffle' n' gs'

{- begin allof -}
allof :: [Gen a] -> Gen a
allof = msum
{- end allof -}

{- begin fairallof -}
fairAllof :: [Gen a] -> Gen a
fairAllof gs =
  Gen (\s r ->
         let seeds = randomseeds r
         in concat . transpose $ run <$> gs <*> repeat s <*> seeds)
{- end fairallof -}

randomseeds :: StdGen -> [StdGen]
randomseeds r = let (r1, r2) = split r in r1 : randomseeds r2

{- begin weightedallof -}
weightedAllof :: [(Int, Gen a)] -> Gen a
weightedAllof wgs =
    Gen (\s r0 ->
           let (r1, r2) = split r0
           in concat $ run (permuteWeightedGens wgs s r1) s r2)
{- end weightedallof -}

{- begin permuteWeightedGens -}
permuteWeightedGens :: [(Int, Gen a)] -> Int -> StdGen -> Gen [a]
permuteWeightedGens [] _ _ = empty
permuteWeightedGens wgs s r0 = do
  k <- choose (0, total-1)
  pd <- pickDropGen wgs k
  case pd of
    Nothing -> empty
    Just (_, x, wgs') ->
      let (r1, r2) = split r0
      in return $ x : concat (run (permuteWeightedGens wgs' s r1) s r2)
  where total = sum $ map fst wgs
{- end permuteWeightedGens -}

{- begin pickDrop -}
pickDropGen :: [(Int, Gen a)] -> Int -> Gen (Maybe (Int, a, [(Int, Gen a)]))
pickDropGen [] _ = return Nothing
pickDropGen ((k, g) : gs) n =
  if n < k
  then do split <- msplit g
          case split of
            Nothing -> pickDropGen gs (n-k)
            Just (x, g') -> return $ Just (k, x, (k, g') : gs)
  else do pd <- pickDropGen gs (n-k)
          case pd of
            Nothing -> return Nothing
            Just (k', x', gs') ->
              return $ Just (k', x', (k, g) : gs')
{- end pickDrop -}

{- begin tryMany -}
tryMany :: Int -> Gen a -> Gen a
tryMany n g = allof $ replicate n g
{- end tryMany -}

{- begin retry -}
retry :: Int -> Gen a -> Gen a
retry n g = cut $ tryMany n g
{- end retry -}


vector :: Arbitrary a => Int -> Gen [a]
vector n = sequence [ arbitrary | i <- [1..n] ]

vectorOf :: Int -> Gen a -> Gen [a]
vectorOf n g = sequence [ g | i <- [1..n] ]

oneof :: [Gen a] -> Gen a
oneof gens = elements gens >>= id

frequency :: [(Int, Gen a)] -> Gen a
frequency xs = choose (1, tot) >>= (`pick` xs)
 where
  tot = sum (map fst xs)

  pick _ [] = empty
  pick n ((k,x):xs)
    | n <= k    = x
    | otherwise = pick (n-k) xs

-- general monadic

two :: Monad m => m a -> m (a, a)
two m = liftM2 (,) m m

three :: Monad m => m a -> m (a, a, a)
three m = liftM3 (,,) m m m

four :: Monad m => m a -> m (a, a, a, a)
four m = liftM4 (,,,) m m m m

--------------------------------------------------------------------
-- Arbitrary

class Arbitrary a where
  arbitrary   :: Gen a
  coarbitrary :: a -> Gen b -> Gen b

instance Arbitrary () where
  arbitrary     = return ()
  coarbitrary _ = variant 0

instance Arbitrary Bool where
  arbitrary     = elements [True, False]
  coarbitrary b = if b then variant 0 else variant 1

instance Arbitrary Int where
  arbitrary     = sized $ \n -> choose (-n,n)
  coarbitrary n = variant (if n >= 0 then 2*n else 2*(-n) + 1)

instance Arbitrary Integer where
  arbitrary     = sized $ \n -> choose (-fromIntegral n,fromIntegral n)
  coarbitrary n = variant (fromInteger (if n >= 0 then 2*n else 2*(-n) + 1))

instance Arbitrary Float where
  arbitrary     = liftM3 fraction arbitrary arbitrary arbitrary 
  coarbitrary x = coarbitrary (decodeFloat x)

instance Arbitrary Double where
  arbitrary     = liftM3 fraction arbitrary arbitrary arbitrary 
  coarbitrary x = coarbitrary (decodeFloat x)

fraction a b c = fromInteger a + (fromInteger b / (abs (fromInteger c) + 1))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a, b) where
  arbitrary          = liftM2 (,) arbitrary arbitrary
  coarbitrary (a, b) = coarbitrary a . coarbitrary b

instance (Arbitrary a, Arbitrary b, Arbitrary c) => Arbitrary (a, b, c) where
  arbitrary             = liftM3 (,,) arbitrary arbitrary arbitrary
  coarbitrary (a, b, c) = coarbitrary a . coarbitrary b . coarbitrary c

instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d)
      => Arbitrary (a, b, c, d)
 where
  arbitrary = liftM4 (,,,) arbitrary arbitrary arbitrary arbitrary
  coarbitrary (a, b, c, d) =
    coarbitrary a . coarbitrary b . coarbitrary c . coarbitrary d

instance Arbitrary a => Arbitrary [a] where
  arbitrary          = sized (\n -> choose (0,n) >>= vector)
  coarbitrary []     = variant 0
  coarbitrary (a:as) = coarbitrary a . variant 1 . coarbitrary as

instance (Arbitrary a, Arbitrary b) => Arbitrary (a -> b) where
  arbitrary         = promote (`coarbitrary` arbitrary)
  coarbitrary f gen = arbitrary >>= ((`coarbitrary` gen) . f)

--------------------------------------------------------------------
-- Testable

data Result
  = Result { ok :: Maybe Bool, stamp :: [String], arguments :: [String] }

instance Show Result where
  show (Result ok s args) = "Result: " ++ show ok ++ " , " ++ show s ++ " , " ++ show args 

nothing :: Result
nothing = Result{ ok = Nothing, stamp = [], arguments = [] }

newtype Property
  = Prop (Gen Result)

result :: Result -> Property
result res = Prop (return res)

evaluate :: Testable a => a -> Gen Result
evaluate a = gen where Prop gen = property a

class Testable a where
  property :: a -> Property

instance Testable () where
  property _ = result nothing

instance Testable Bool where
  property b = result (nothing{ ok = Just b })

instance Testable (Either String ()) where
  property (Left s) = trace s $ property False
  property (Right _) = property True

instance Testable Result where
  property res = result res

instance Testable Property where
  property prop = prop

instance (Arbitrary a, Show a, Testable b) => Testable (a -> b) where
  property f = forAll arbitrary f

forAll :: (Show a, Testable b) => Gen a -> (a -> b) -> Property
forAll gen body = Prop $
  do a   <- gen
     res <- evaluate (body a)
     return (argument a res)
 where
  argument a res = res{ arguments = show a : arguments res }

(==>) :: Testable a => Bool -> a -> Property
True  ==> a = property a
False ==> a = property ()

label :: Testable a => String -> a -> Property
label s a = Prop (add `fmap` evaluate a)
 where
  add res = res{ stamp = s : stamp res }

classify :: Testable a => Bool -> String -> a -> Property
classify True  name = label name
classify False _    = property

trivial :: Testable a => Bool -> a -> Property
trivial = (`classify` "trivial")

collect :: (Show a, Testable b) => a -> b -> Property
collect v = label (show v)

--
instance Applicative Gen where
    pure  = return
    (<*>) = ap

--------------------------------------------------------------------
-- Testing

data Config = Config
  { configMaxTest :: Int
  , configMaxFail :: Int
  , configSize    :: Int -> Int
  , configEvery   :: Int -> [String] -> String
  }

quick :: Config
quick = Config
  { configMaxTest = 100
  , configMaxFail = 1000
  , configSize    = (+ 3) . (`div` 2)
  , configEvery   = \n args -> let s = show n in s ++ [ '\b' | _ <- s ]
  }
         
verbose :: Config
verbose = quick
  { configEvery = \n args -> show n ++ ":\n" ++ unlines args
  }

defaultConfig :: Config
defaultConfig = quick

data Summary = Summary { summaryOk :: Bool, summaryTests :: Int, summaryTime :: Integer, summaryFail :: Int}
  deriving Show

test, quickCheck, verboseCheck :: Testable a => a -> IO ()
test         = check' quick
quickCheck   = check' quick
verboseCheck = check' verbose
         
check :: Testable a => Config -> a -> IO Summary
check config a =
  do rnd <- newStdGen
     now <- getTime ProcessCPUTime
     tests config (evaluate a) rnd now 0 0 []

check' :: Testable a => Config -> a -> IO ()
check' config a =
  do res <- check config a
     putStrLn $ show res
     return ()

sample :: Show a => Gen a -> IO ()
sample a =
  do rnd <- newStdGen
     print $ generate' 10 rnd a

sampleList :: Show a => Gen a -> IO [a]
sampleList a =
  do rnd <- newStdGen
     return $ generate' 42 rnd a

sampleOne :: Show a => Gen a -> IO a
sampleOne a =
  do rnd <- newStdGen
     return $ generate 42 rnd a

sampleOneSafe :: Show a => Gen a -> IO (Maybe a)
sampleOneSafe a =
  do rnd <- newStdGen
     return $ generateSafe 42 rnd a

withTimeout :: Int -> a -> IO (Either () a)
withTimeout timeout v =
  race (liftIO $ threadDelay timeout)
       (return $! v)

-- Not working yet:
within :: Testable a => Int -> a -> Property
within microseconds a = Prop $ 
  let Prop (Gen g) = property a in
  Gen $ \n r -> unsafePerformIO $ do
    res <- timeout microseconds $ return $! g n r
    case res of
      Just x  -> return x
      Nothing -> return [nothing { ok = Just False }]
--  where aux as = case unsafePerformIO $ timeout microseconds $ return $ evalHead as of
--                   Just [] -> []
--                   Just (a:as) -> a : aux as
--                   Nothing -> [nothing { ok = Just False }]
--        evalHead [] = []
--        evalHead (a:as) = seq (ok a) (a:as)

data MTTF = MTTFGreaterThan Double Double | Inconclusive | MTTF Double Double
  deriving Show

mttfToCSV :: MTTF -> [String]
mttfToCSV (MTTFGreaterThan tests time) = ["MTTFGreaterThan", show tests, show time]
mttfToCSV Inconclusive = ["Inconclusive", "0", "0"]
mttfToCSV (MTTF tests time) = ["MTTF", show tests, show time]

-- TODO: Failures
statsToCSV :: (Double, Int, Double, Int) -> [String]
statsToCSV (d1, f, d2, i) = [show d1, show d2, show i]

gatherStats :: Testable a => Int -> Int -> Int -> a -> IO (Double, Int, Double, Int)
gatherStats runs to numTests p = aux runs 0.0 0 0.0 0
  where aux :: Int -> Double -> Int -> Double -> Int -> IO (Double, Int, Double, Int)
        aux 0 totalTests totalFails totalTime timeouts = do
          let successes = fromIntegral (runs - timeouts)
              toSeconds x = x / (10^9)
          return (totalTests / successes,
                  totalFails,
                  toSeconds $ totalTime  / successes ,
                  timeouts)
        aux n tests fails times timeouts = do
          res <- timeout to $! check config p
          case res of
            Just s ->
              if summaryOk s then
                error "You should run more tests cause you didn't reach the time limit"
              else
                aux (n-1) (tests + fromIntegral (summaryTests s))
                          (fails + summaryFail s)
                          (times + fromIntegral (summaryTime  s))
                          timeouts
            Nothing ->
                aux (n-1) tests fails times (timeouts + 1)

        config = quick { configMaxTest = numTests
                       , configMaxFail = numTests
                       }
  
mttf :: Testable a => Int -> Int -> a -> IO MTTF
mttf maxTimeout meanTestsToFailureEstimate p = do
  s <- check config p
  print s
  if summaryOk s
    then return $ MTTFGreaterThan (fromIntegral meanTestsToFailureEstimate)  
                                  (fromIntegral (summaryTime s) / fromIntegral factor / 1000000000)
    else aux 9 [summaryTests s] [summaryTime s]

  where aux 0 testss timess =
          return $ MTTF ((fromIntegral $ sum testss) / 10) ((fromIntegral $ sum timess) / 10 / 1000000000) 
        aux n testss timess = do
          res <- timeout maxTimeout $! check config p
          case res of
            Just s -> 
              if summaryOk s
                then return Inconclusive
                else aux (n-1) (summaryTests s : testss) (summaryTime s : timess)
            Nothing -> do putStrLn "TIMEOUT"
                          aux n testss timess
          
        factor = 20
        config = quick
          { configMaxTest = factor * meanTestsToFailureEstimate
          , configMaxFail = factor * 10 * meanTestsToFailureEstimate
          , configEvery   = \n args -> if n `mod` 1000 == 0 then let s =  show n in s ++ [ '\b' | _ <- s ] else ""
          }

-- | Generates a value that satisfies a predicate.
suchThat :: Gen a -> (a -> Bool) -> Gen a
gen `suchThat` p =
  do mx <- gen `suchThatMaybe` p
     case mx of
       Just x  -> return x
       Nothing -> sized (\n -> resize (n+1) (gen `suchThat` p))

suchThatMaybe :: Gen a -> (a -> Bool) -> Gen (Maybe a)
gen `suchThatMaybe` p = sized (\n -> try n (2*n))
 where
  try m n
    | m > n = return Nothing
    | otherwise = do
        x <- resize m gen
        if p x then return (Just x) else try (m+1) n

{- begin tests -}
tests :: Config -> Gen Result -> StdGen -> TimeSpec -> Int -> Int -> [[String]] -> IO Summary
tests config gen rnd0 startTime ntest nfail stamps
  | ntest >= configMaxTest config = done "OK, passed" ntest nfail stamps startTime
  | nfail >= configMaxFail config =
      done "Arguments exhausted after" ntest nfail stamps startTime
  | otherwise               = 
      case results of
        [] -> tests config gen rnd1 startTime ntest (nfail + 1) stamps
        _ ->  checkResults config results ntest nfail stamps
     where
      results     =  generate' (configSize config ntest) rnd2 gen
      (rnd1,rnd2) = split rnd0

      checkResults config [] ntest nfail stamps = tests config gen rnd1 startTime ntest nfail stamps
      checkResults config (r:rs) ntest nfail stamps 
        | ntest >= configMaxTest config = done "OK, passed" ntest nfail stamps startTime
        | nfail >= configMaxFail config =
            done "Arguments exhausted after" ntest nfail stamps startTime
        | otherwise               = 
            do putStr (configEvery config ntest (arguments r))
               case ok r of
                 Nothing    ->
                   checkResults config rs ntest (nfail+1) stamps
                 Just True  ->
                   checkResults config rs (ntest+1) nfail (stamp r:stamps)
                 Just False -> do
                   putStr ( "Falsifiable, after "
                            ++ show (ntest+1)
                            ++ " tests ("
                            ++ show nfail
                            ++ " discards):\n"
                            ++ unlines (arguments r)
                          )
                   summarize False (ntest+1) nfail startTime
{- end tests -}

done :: String -> Int -> Int -> [[String]] -> TimeSpec -> IO Summary
done mesg ntest nfail stamps startTime =
  do putStr ( mesg ++ " " ++ show ntest ++ " tests" ++ table )
     summarize True ntest nfail startTime
 where
  table = display
        . map entry
        . reverse
        . sort
        . map pairLength
        . group
        . sort
        . filter (not . null)
        $ stamps

  display []  = ".\n"
  display [x] = " (" ++ x ++ ").\n"
  display xs  = ".\n" ++ unlines (map (++ ".") xs)

  pairLength xss@(xs:_) = (length xss, xs)
  entry (n, xs)         = percentage n ntest
                       ++ " "
                       ++ concat (intersperse ", " xs)

  percentage n m        = show ((100 * n) `div` m) ++ "%"

summarize ok ntest nfail startTime = do
     endTime <- getTime ProcessCPUTime
     let time = toNanoSecs $ diffTimeSpec startTime endTime
     return $ Summary { summaryOk = ok, summaryTests = ntest, summaryTime = time, summaryFail = nfail } 

{- begin Alternative -}
instance Alternative Gen where
  empty = Gen (\n r -> [])
  (Gen f1) <|> (Gen f2) = Gen (\n r -> let (r1, r2) = split r
                                     in f1 n r1 ++ f2 n r2)

{-
  {- begin empty -}
empty :: Gen a
empty = Gen (\n r -> [])
  {- end empty -}
  {- begin alt -}
(<|>) :: Gen a -> Gen a -> Gen a
(Gen f1) <|> (Gen f2) = Gen (\n r -> let (r1, r2) = split r
                                         in f1 n r1 ++ f2 n r2)
  {- end alt -}
-}
{- end Alternative -}

{-
{- begin guard -}
guard :: Bool -> Gen ()
guard True  = return ()
guard False = empty
{- end guard -}
-}

{- begin MonadPlus -}
instance MonadPlus Gen where
  mzero = empty
  mplus = (<|>)
{- end MonadPlus -}

{- begin MonadLogic -}
instance MonadLogic Gen where
  msplit ga = Gen (\n r ->
                      case run ga n r of
                        [] -> return Nothing
                        (x:xs) -> return $ Just (x, enumerate xs))
{- end MonadLogic -}

