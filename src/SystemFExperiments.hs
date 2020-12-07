{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-methods -Wno-partial-type-signatures #-}

{-
  Generators and properties for SystemF
-}

module SystemFExperiments where

-- import Criterion (nfAppIO, benchmark)

import Control.Monad
import Control.Monad.State (StateT, evalStateT, get, liftIO, put, runStateT)
import Data.Data hiding (typeOf)
import Data.IORef (IORef, modifyIORef, newIORef, readIORef, writeIORef)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ord (comparing)
import qualified Data.Set as S
import HT hiding (Expr)
import System.IO.Unsafe (unsafePerformIO)
import System.Microtimer (formatSeconds, time_)
import System.Timeout (timeout)
import SystemF
import Term hiding (eval)
import Test.QuickCheck
import Text.Printf

{-# ANN module "HLint: Reduce duplication." #-}

------------------------------------------
-- GENERATION
------------------------------------------

genType :: _ => Int -> Gen Type
genType freeTypeVar = sized (arb freeTypeVar)
  where
    arb ftv 0 = elements $ Base : (TVar <$> [0 .. ftv -1])
    arb ftv n =
      oneof
        [ arb ftv 0,
          (:->) <$> arb ftv (n `div` 6) <*> arb ftv (n `div` 4),
          ForAll <$> arb (ftv + 1) (n -1)
        ]

genExpr :: _ => Gen (Maybe Expr)
genExpr =
  sized $ \n -> do t <- genType 0; arb 0 [] t n
  where
    arb :: Int -> [Type] -> Type -> Int -> Gen (Maybe Expr)
    arb ftv c t 0 =
      oneofMaybe $
        [return $ Just Con | t == Base]
          ++
          -- [ return $ Just BTrue | t == TBool ] ++
          -- [ return $ Just BFalse | t == TBool ] ++
          [return $ Just $ Var i | (i, t') <- zip [0 ..] c, t == t']
          ++ [fmap (Lam t1) <$> arb ftv (t1 : c) t2 0 | (t1 :-> t2) <- [t]]
          ++ [fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t]] -- MUTANT?
    arb ftv c t n =
      frequency $
        [(6, arb ftv c t 0)]
          ++ [(8, fmap (Lam t1) <$> arb ftv (t1 : c) t2 (n -1)) | (t1 :-> t2) <- [t]]
          ++ [(4, fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 (n -1)) | (ForAll t1) <- [t]]
          ++ [ ( 8,
                 do
                   t2 <- do
                     arbT <- resize 10 $ genType ftv -- for now; should be bigger?
                     elements (nub $ michal c t ++ [arbT])
                   me1 <- arb ftv c (t2 :-> t) (n `div` 2)
                   me2 <- arb ftv c t2 (n `div` 2)
                   return $ (:@:) <$> me1 <*> me2
               )
             ]
          ++ [ ( 4,
                 do
                   t1t2 <- genT1T2 t
                   case t1t2 of
                     Just (t1, t2) -> do
                       me1 <- arb ftv c t1 (n - 1)
                       return $ TApp <$> me1 <*> return t2
                     Nothing -> return Nothing --  ++
                     -- [ (0, do e1 <- arb ftv c TBool (n `div` 3)
                     --          e2 <- arb ftv c t (n `div` 3)
                     --          e3 <- arb ftv c t (n `div` 3)
                     --          return $ Cond <$> e1 <*> e2 <*> e3) ]
               )
             ]

michal :: [Type] -> Type -> [Type]
michal c t =
  [ t' | varType <- c, t' <- aux varType
  ]
  where
    aux (t1 :-> t2)
      | t == t2 = [t1]
      | t /= t2 = aux t2
    aux _ = []

-- Check if a type has any type variables.
-- TODO: replace with "isClosed"
hasTVars :: Type -> Bool
hasTVars (TVar _) = True
hasTVars (t1 :-> t2) = hasTVars t1 || hasTVars t2
hasTVars (ForAll t) = hasTVars t
hasTVars TBool = False
hasTVars Base = False

isClosed :: Type -> Bool
isClosed = isClosed' 0
  where
    isClosed' :: Int -> Type -> Bool
    isClosed' tc (TVar x) = x < tc
    isClosed' tc (t1 :-> t2) = isClosed' tc t1 && isClosed' tc t2
    isClosed' tc (ForAll t) = isClosed' (tc + 1) t
    isClosed' _ TBool = True
    isClosed' _ Base = True

-- Randomly fetch a subterm of a type
fetchSubType :: Type -> Gen (Maybe Type)
fetchSubType t =
  oneofMaybe $
    [return (Just t) | isClosed t]
      ++ [fetchSubType t1 | (t1 :-> _) <- [t]]
      ++ [fetchSubType t2 | (_ :-> t2) <- [t]]
      ++ [fetchSubType t' | (ForAll t') <- [t]]

oneofMaybe :: [Gen (Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe gs = oneof gs

-- "Replace (some occurrences of) closed type s in type t by (TVar n)"
replaceSubType :: Int -> Type -> Type -> Gen Type
replaceSubType n s t =
  oneof $
    [return t]
      ++ [return $ TVar n | s == t]
      ++ [do t1' <- replaceSubType n s t1; t2' <- replaceSubType n s t2; return $ t1' :-> t2' | (t1 :-> t2) <- [t]]
      ++ [do t'' <- replaceSubType (n + 1) s t'; return $ ForAll t'' | (ForAll t') <- [t], t' == s]

-- Generate t1 t2 such that t1{0:=t2} = t
genT1T2 :: Type -> Gen (Maybe (Type, Type))
genT1T2 t = do
  let t' = let ?mutant = NoMutant in liftType 0 t
  t2 <- fetchSubType t'
  case t2 of
    Just t2' -> do
      t1 <- replaceSubType 0 t2' t'
      return $ Just (ForAll t1, t2')
    Nothing -> return Nothing

------------------------------------------
-- GENERATION CONFIGURATIONS
------------------------------------------

data GenConfig = GC
  { gcName :: String,
    gcTake :: Gen Expr -> Gen Expr,
    gcBaseChoice :: [Gen Expr] -> Gen Expr,
    gcRecChoice :: [(Int, Gen Expr)] -> Gen Expr,
    gcRetryType :: Int,
    gcRetryTApp :: Int,
    gcRetryFun :: Int
  }

instance PrintfArg GenConfig where
  formatArg x fmt
    | fmtChar (vFmt 's' fmt) == 's' = formatString (show x) (fmt {fmtChar = 's', fmtPrecision = Nothing})
  formatArg _ fmt = errorBadFormat $ fmtChar fmt

data GenConfigType
  = GCPlain
  | GCBacktrack
  | GCRetryLeaf
  | GCRetryType
  | GCRetryTypeCut
  | GCRetryFun
  | GCRetryFunCut
  deriving (Data, Typeable, Show, Eq)

gcOfGcType :: GenConfigType -> GenConfig
gcOfGcType GCPlain = gcPlain
gcOfGcType GCBacktrack = gcBacktrack
gcOfGcType GCRetryLeaf = gcSimple1
gcOfGcType GCRetryType = gcSimple2
gcOfGcType GCRetryFun = gcSimple3
gcOfGcType GCRetryTypeCut = gcRetryTypeCut
gcOfGcType GCRetryFunCut = gcRetryFunCut

instance Show GenConfig where
  show gc = show (gcName gc, gcRetryType gc, gcRetryFun gc, gcRetryTApp gc)

takeG n = id

retry n = id

cut = id

gcPlain =
  GC
    { gcName = "Random",
      gcTake = id,
      gcBaseChoice = oneof,
      gcRecChoice = frequency,
      gcRetryType = 1,
      gcRetryFun = 1,
      gcRetryTApp = 1
    }

gcBacktrack =
  GC
    { gcName = "Hybrid",
      gcTake = takeG 10,
      gcBaseChoice = oneof,
      gcRecChoice = cut . frequency,
      gcRetryType = 1,
      gcRetryFun = 2,
      gcRetryTApp = 1
    }

gcSimple1 =
  gcPlain
    { gcName = "Simple1 (leaves only)",
      gcBaseChoice = oneof, -- LOOK HERE
      gcTake = takeG 1
    }

gcSimple2 =
  gcPlain
    { gcName = "Simple2 (retry type)",
      gcRetryType = 2,
      gcTake = takeG 1
    }

gcRetryTypeCut =
  gcPlain
    { gcName = "Retry type with cut",
      gcRetryType = 2,
      gcRecChoice = cut . frequency,
      gcTake = takeG 1
    }

gcSimple3 =
  gcPlain
    { gcName = "Simple3 (retry fun)",
      gcRetryFun = 2,
      gcTake = takeG 1
    }

gcRetryFunCut =
  gcPlain
    { gcName = "Retry fun with cut",
      gcRecChoice = cut . frequency,
      gcRetryFun = 2,
      gcTake = takeG 1
    }

all_configs = [GCPlain]

{-
              , GCRetryLeaf
              , GCRetryType, GCRetryTypeCut
              , GCRetryFun,  GCRetryFunCut
              ]
-}

------------------------------------------
-- SHRINKING
------------------------------------------

shrinkType :: Type -> [Type]
shrinkType Base = []
shrinkType TBool = [Base]
shrinkType (t1 :-> t2) =
  Base :
  t1 :
  t2 :
  [t1' :-> t2 | t1' <- shrinkType t1]
    ++ [t1 :-> t2' | t2' <- shrinkType t2]
shrinkType (TVar n) = Base : [TVar n' | n' <- shrink n]
shrinkType (ForAll t) = Base : t : [ForAll t' | t' <- shrinkType t]

shrinkExpr' Con = []
shrinkExpr' (Var n) = Con : [Var n' | n' <- shrink n]
shrinkExpr' (Lam t e) =
  Con :
  e :
  [Lam t' e | t' <- shrinkType t]
    ++ [Lam t e' | e' <- shrinkExpr' e]
shrinkExpr' (e1 :@: e2) = Con : e1 : e2 : [e1' :@: e2 | e1' <- shrinkExpr' e1] ++ [e1 :@: e2' | e2' <- shrinkExpr' e2]
shrinkExpr' (Cond e1 e2 e3) = Con : e1 : e2 : e3 : [Cond e1' e2 e3 | e1' <- shrinkExpr' e1] ++ [Cond e1 e2' e3 | e2' <- shrinkExpr' e2] ++ [Cond e1 e2 e3' | e3' <- shrinkExpr' e3]
shrinkExpr' BTrue = [Con]
shrinkExpr' BFalse = [Con, BTrue]
shrinkExpr' (TLam e) = Con : e : [TLam e' | e' <- shrinkExpr' e]
shrinkExpr' (TApp e t) = Con : e : [TApp e' t | e' <- shrinkExpr' e] ++ [TApp e t' | t' <- shrinkType t]

shrinkExpr :: _ => Expr -> [Expr]
shrinkExpr e =
  [e' | e' <- shrinkExpr' e, wellTyped e']
    ++ [e'' | e' <- shrinkExpr' e, e'' <- shrinkExpr' e', wellTyped e'']
    ++ [e' | Just e' <- [step e], size e' < size e] --, typeOf e' = typeOf e]

------------------------------------------
-- LAMBDA CSV GEN
------------------------------------------

-- lambda_csv_gen :: String -> [(Mutant, PropType)] -> [GenConfigType] ->
--                   Int -> Int -> Int -> Int -> Int -> IO ()
-- lambda_csv_gen file setups cs tpt gt numTests runs max_size = do
--   results <- forM [ (mutant, pt, config) | (mutant, pt) <- setups , config <- map gcOfGcType cs ] $ \(m,pt,c) -> do
--     putStrLn $ "Running Config: " ++ show (m,c,pt)
--     res <- do let ?mutant = m
--                   ?config = c
--               gatherStatsPure runs gt numTests max_size (forAll genExpr $ propTimeout tpt (propOfPropType pt))
--     return (m, pt, c, res)
--   putStrLn $ unlines $ map (\(m, p, c, r) -> show (m, p, c, statsShow r)) results

--   -- To CSV
--   let csvStr = genCsvFile $ map (\(m, p, c, r) -> [show m, show p, show c] ++ statsToCSV r) results
--   writeFile file csvStr

--
--lambda_csv_gen' :: String -> IO ()
--lambda_csv_gen' file = do
--  results <- forM [ (mutant, config) | mutant <- all_mutants , config <- all_configs ] $ \(m,c) -> do
--    putStrLn $ "Running Config: " ++ show (m,c)
--    res <- do let ?mutant = m
--                  ?config = c
--              mttf (-1) 1000 (forAll genExpr $ propTimeout 10000 (\e -> bToE e $ prop_normalform e))
--    return (m, c, res)
--  putStrLn $ unlines $ map show results
--
--  -- To CSV
--  let csvStr = genCsvFile $ map (\(m, c, r) -> [show m, show c] ++ mttfToCSV r) results
--  writeFile file csvStr

------------------------------------------
-- LAMBDA STATS
------------------------------------------

-- lambda_stats :: _ => Int -> _
-- lambda_stats n = do
--   let aux :: Int -> IO [Expr]
--       aux 0 = return []
--       aux m = do
--         es <- catMaybes <$> sample' genExpr
--         let es' = take m es
--         es'' <- aux (m - length es')
--         return (es' ++ es'')
--   es <- aux n -- sequence $ replicate 10000 $ concat <$> sampleList (genExpr :: Gen Expr)
--   putStrLn "Number of terms:"
--   print $ length $ es
--   putStrLn "Number of non-Con terms:"
--   print $ length $ filter (/=Con) $ es
--   putStrLn "Number of unique terms:"
--   print $ length $ nub' $ es
--   putStrLn "Distribution of sizes:"
--   print $ dist $ map size $ es
--   putStrLn "Distribution of sizes of unique terms:"
--   print $ dist $ map size $ nub' $ es
--   let terms = es
--   let totVars = sum $ map (length . vars) $ terms
--   let totLams = sum $ map lambdas $ terms
--   print "Total vars / lambdas:"
--   print $ fromIntegral totVars / fromIntegral totLams
--   print "Reduction sequence lengths:"
--   print $ dist $ map (length . eval) terms
--   print "Reduction sequence lengths for unique terms:"
--   print $ dist $ map (length . eval) $ nub' terms

-- where dist es = map (\gs -> (head gs, length gs)) $ group $ sort $ es

-- nub' = map head . group . sort

------------------------------------------
-- LAMBDA STATS
------------------------------------------
{-
lambda_stats :: _ => _
lambda_stats = do
  es <- sequence $ replicate 10000 $ concat <$> sampleList (genExpr :: Gen Expr)
  putStrLn "Number of terms:"
  print $ length $ concat es
  putStrLn "Number of non-Con terms:"
  print $ length $ filter (/=Con) $ concat es
  putStrLn "Number of unique terms:"
  print $ length $ nub' $ concat es
  putStrLn "Distribution of sizes:"
  print $ dist $ map size $ concat es
  putStrLn "Distribution of sizes of unique terms:"
  print $ dist $ map size $ nub' $ concat es
  let terms = concat es
  let totVars = sum $ map (length . vars) $ terms
  let totLams = sum $ map lambdas $ terms
  print "Total vars / lambdas:"
  print $ fromIntegral totVars / fromIntegral totLams
  print "Reduction sequence lengths:"
  print $ dist $ map (length . eval) terms
  print "Reduction sequence lengths for unique terms:"
  print $ dist $ map (length . eval) $ nub' terms

  where dist es = map (\gs -> (head gs, length gs)) $ group $ sort $ es

nub' = map head . group . sort
-}

------------------------------------------
-- PROPERTIES
------------------------------------------

data PropType
  = PropStrongNormalization
  | PropStrongNormalizationStep
  | PropEvalMakesProgress
  | PropStepMakesProgress
  | PropEvalShort
  | PropBigSmallStep
  | PropHnfNoStep
  | PropEvalNoMoreSteps
  | PropGenWellTyped
  | PropPreservation
  | PropParallelPreservation
  | PropPreservationMulti
  | PropProgress
  | PropEvalSame
  | PropPSame
  | PropEvalStepSame
  | PropTest
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Data, Typeable)

instance Testable (Either String ()) where
  property (Left s) = whenFail (putStrLn s) False
  property (Right _) = property True

propOfPropType :: _ => PropType -> (Expr -> Property)
propOfPropType PropStrongNormalization e = property $ prop_normalform e
propOfPropType PropStrongNormalizationStep e = property $ prop_normalform' e
propOfPropType PropEvalMakesProgress e = property $ prop_evalMakesProgress e
propOfPropType PropStepMakesProgress e = property $ prop_stepMakesProgress e
propOfPropType PropEvalShort e = property $ prop_evalShort e
propOfPropType PropBigSmallStep e = property $ prop_bigSmallStep e
propOfPropType PropHnfNoStep e = property $ prop_hnfNoStep e
propOfPropType PropEvalNoMoreSteps e = property $ prop_evalNoMoreSteps e
propOfPropType PropGenWellTyped e = property $ prop_wellTyped e
propOfPropType PropPreservation e = prop_preservation e
propOfPropType PropParallelPreservation e = prop_ppreservation e
propOfPropType PropPreservationMulti e = prop_preservation_multi 0 20 e
propOfPropType PropProgress e = property $ prop_progress e
propOfPropType PropEvalSame e = property $ prop_evalSame e
propOfPropType PropPSame e = property $ prop_PSame e
propOfPropType PropEvalStepSame e = property $ prop_evalStepSame e
propOfPropType PropTest e = property $ prop_test e

bToE :: (Show a) => a -> Bool -> Either String ()
bToE _ True = Right ()
bToE x False = Left (show x)

prop_normalform e = isHnf . last . eval $ e

prop_normalform' e = isHnf . last . eval' $ e

prop_wellTyped e = wellTyped e

prop_evalMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where
    es = eval e

prop_stepMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where
    es = eval' e

prop_evalShort e =
  length (eval e) < 100

prop_bigSmallStep e =
  let es = eval e
      es' = eval' e
   in last es == last es'

prop_hnfNoStep e =
  (not $ isHnf e) || (isNothing $ step e)

prop_evalNoMoreSteps e =
  isNothing $ step (last $ eval e)

prop_preservation e =
  case step e of
    Just s ->
      whenFail
        ( do
            putStrLn $ "Original:  " ++ show e
            putStrLn $ "With Type: " ++ show (typeOf e)
            putStrLn $ "Steps To:  " ++ show s
            putStrLn $ "With Type: " ++ show (typeOf s)
        )
        (typeOf e == typeOf s)
    Nothing -> discard

prop_ppreservation e =
  let s = pstep e
   in whenFail
        ( do
            putStrLn $ "Original:  " ++ show e
            putStrLn $ "With Type: " ++ show (typeOf e)
            putStrLn $ "Steps To:  " ++ show s
            putStrLn $ "With Type: " ++ show (typeOf s)
        )
        (typeOf e == typeOf s)

prop_preservation_multi n max e =
  if n == max
    then collect n True
    else case step e of
      Just s ->
        whenFail
          ( do
              putStrLn $ "Original:  " ++ show e
              putStrLn $ "With Type: " ++ show (typeOf e)
              putStrLn $ "Steps To:  " ++ show s
              putStrLn $ "With Type: " ++ show (typeOf s)
          )
          $ if typeOf e == typeOf s
            then prop_preservation_multi (n + 1) max s
            else property False
      Nothing -> collect n True

prop_progress e = isHnf e || canStep e

prop_evalSame e =
  take 100 (let ?mutant = NoMutant in eval e) == take 100 (eval e)

prop_pevalSame e =
  (let ?mutant = NoMutant in peval e) == peval e

prop_PSame e =
  (let ?mutant = NoMutant in pstep e) == pstep e

prop_evalStepSame e =
  take 100 (let ?mutant = NoMutant in eval' e) == take 100 (eval' e)

prop_test e =
  case e of
    Lam _ (Lam _ _) :@: Lam _ _ -> False
    Lam _ e -> prop_test e
    TLam e -> prop_test e
    e1 :@: e2 -> prop_test e1 && prop_test e2
    TApp e1 _ -> prop_test e1
    Cond e1 e2 e3 -> prop_test e1 && prop_test e2 && prop_test e3
    _ -> True

propTimeout :: Int -> (Expr -> Property) -> Maybe Expr -> Property
propTimeout microseconds p Nothing = discard
propTimeout microseconds p (Just e) =
  unsafePerformIO $ do
    res <- timeout microseconds $ return $! p e
    case res of
      Just x -> return x
      Nothing -> discard

-- checkProperty mutant config propType numTests tpt = do
--   let qcConfig = stdArgs {maxSuccess = numTests, maxDiscardRatio = 10, maxSize = 100}
--   let ?mutant = mutant
--       ?config = gcOfGcType $ config
--   quickCheckWithResult qcConfig $ forAll genExpr $ propTimeout tpt (propOfPropType propType)

data SFC
  = SFBase
  | SFTBool
  | SFFunc
  | SFTBoundVar
  | SFTFreeVar
  | SFForAll
  | SFCon
  | SFBoundVar
  | SFFreeVar
  | SFLam
  | SFApp
  | SFCond
  | SFBTrue
  | SFBFalse
  | SFTLam
  | SFTApp
  deriving (Ord, Eq, Show)

typeToTerm :: Type -> Term SFC
typeToTerm = aux (-1)
  where
    aux _ Base = Term SFBase []
    aux _ TBool = Term SFTBool []
    aux i (t1 :-> t2) = Term SFFunc [aux i t1, aux i t2]
    aux i (TVar n) = Term (if i < n then SFTFreeVar else SFTBoundVar) []
    aux i (ForAll t) = Term SFForAll [aux (i + 1) t]

typeSpec :: Spec Type SFC
typeSpec =
  Spec
    { specH =
        M.fromList
          [ ( "Type",
              [ (SFBase, []),
                (SFTBool, []),
                (SFFunc, ["Type", "Type"]),
                (SFTBoundVar, []),
                (SFTFreeVar, []),
                (SFForAll, ["Type"])
              ]
            )
          ],
      specTy = "Type",
      specFromTerm = undefined,
      specToTerm = typeToTerm,
      specGen = genType 0
    }

exprToTerm :: Expr -> Term SFC
exprToTerm = aux (-1)
  where
    aux _ Con = Term SFCon []
    aux i (Var n) = Term (if i < n then SFFreeVar else SFBoundVar) []
    aux i (Lam t e) = Term SFLam [typeToTerm t, aux (i + 1) e]
    aux i (e1 :@: e2) = Term SFApp [aux i e1, aux i e2]
    aux i (Cond e1 e2 e3) = Term SFCond [aux i e1, aux i e2, aux i e3]
    aux _ BTrue = Term SFBTrue []
    aux _ BFalse = Term SFBFalse []
    aux i (TLam e) = Term SFTLam [aux i e]
    aux i (TApp e t) = Term SFTApp [aux i e, typeToTerm t]

untilJust :: Monad m => m (Maybe a) -> m a
untilJust m = do
  x <- m
  case x of
    Nothing -> untilJust m
    Just y -> pure y

exprSpec :: _ => Spec Expr SFC
exprSpec =
  Spec
    { specH =
        M.fromList
          [ ( "Expr",
              [ (SFCon, []),
                (SFBoundVar, []),
                (SFFreeVar, []),
                (SFLam, ["Type", "Expr"]),
                (SFApp, ["Expr", "Expr"]),
                (SFCond, ["Expr", "Expr", "Expr"]),
                (SFBTrue, []),
                (SFBFalse, []),
                (SFTLam, ["Expr"]),
                (SFTApp, ["Expr", "Type"])
              ]
            )
          ]
          `M.union` specH typeSpec,
      specTy = "Expr",
      specFromTerm = undefined,
      specToTerm = exprToTerm,
      specGen = untilJust genExpr
    }

findBug :: Spec a SFC -> (a -> Bool) -> IO Int
findBug spec p = go 0
  where
    go n = do
      x <- generate (specGen spec)
      if p x then go (n + 1) else pure (n + 1)

class Coverage c where
  coverageImprovement :: [Description SFC] -> c -> Double
  updateCoverage :: [Description SFC] -> c -> c

instance Coverage (M.Map (Description SFC) Int) where
  coverageImprovement ds m = sum (proportionalIncrease <$> ds)
    where
      proportionalIncrease k = 1 / fromIntegral (M.findWithDefault 0 k m + 1)
  updateCoverage ds m =
    foldr (\d m' -> M.insert d (M.findWithDefault 0 d m' + 1) m') m ds

instance Coverage (S.Set (Description SFC)) where
  coverageImprovement ds s = fromIntegral . length . filter (not . (`S.member` s)) $ ds
  updateCoverage ds = S.union (S.fromList ds)

type Strength = Int

type FanOut = Int

-- | Returns Mean-Tests-To-Failure if no timeout.
findBugComb :: Coverage c => c -> FanOut -> Strength -> Spec a SFC -> (a -> Bool) -> IO Int
findBugComb c fanOut k spec p = evalStateT (go 0) c
  where
    go n = do
      xs <- liftIO . replicateM fanOut . generate $ specGen spec
      cov <- get
      let (x, descriptionsX, _) =
            maximumBy
              (comparing $ \(_, _, i) -> i)
              [ (x, ds, coverageImprovement ds cov)
                | x <- xs,
                  let ds = covers k (specToTerm spec x)
              ]
      if p x
        then put (updateCoverage descriptionsX cov) >> go (n + 1)
        else pure (n + 1)

stats :: [Double] -> (Double, Double)
stats xs = (average xs, stdDev xs)
  where
    average = (/) <$> sum <*> realToFrac . length
    stdDev ys = sqrt . average . map ((^ 2) . (-) (average ys)) $ ys

trials :: Int -> IO Double -> IO (Double, Double)
trials n = fmap stats . replicateM n

showStats :: Maybe (Double, Double) -> String
showStats = \case
  Nothing -> "timeout"
  Just (m, s) -> show m ++ "," ++ show s

data Setup
  = Setup
      { setupStrength :: Strength,
        setupFanout :: FanOut
      }
  | Random

instance Show Setup where
  show (Setup t f) = "comb (t=" ++ show t ++ " f=" ++ show f ++ ")"
  show Random = "random"

experimentProperty :: _ => Expr -> Bool
experimentProperty e = prop_evalSame e && prop_pevalSame e

replace :: Eq a => a -> a -> [a] -> [a]
replace a b = map (\c -> if c == a then b else c)

formatMeanCount :: Double -> String
formatMeanCount = replace '.' ',' . show

runSetupCount :: _ => c -> Setup -> IO Double
runSetupCount c (Setup k f) = fromIntegral <$> findBugComb c f k exprSpec experimentProperty
runSetupCount _ Random = fromIntegral <$> findBug exprSpec experimentProperty

runSetupTime :: _ => c -> Setup -> IO Double
runSetupTime c (Setup k f) = time_ $ findBugComb c f k exprSpec experimentProperty
runSetupTime _ Random = time_ $ findBug exprSpec experimentProperty

easyMutants :: [Mutant]
easyMutants =
  [ SubstSwapped,
    SubstNoIncr,
    AppForgetSubst,
    SubstLT,
    SubstInTypeLT,
    SubstInTypeNoIncr,
    TSubstNoIncr,
    TAppForgetSubst,
    SubstVar,
    LiftVar,
    LiftLam,
    LiftTypeForAll,
    LiftTypeTVar,
    LiftTNoIncr,
    SubstInTypeNoDecr,
    SubstNoLift
  ]

hardMutants :: [Mutant]
hardMutants =
  [ LiftTLamA,
    LiftTLamB,
    LiftTApp
  ]

experiments :: IO ()
experiments = do
  let t = 100
  let setups = Random : [Setup k f | k <- [2], f <- [6, 10, 30]]
  let mutants = easyMutants
  let time = False
  let sep = ";"
  let initialCov = M.empty :: M.Map (Description SFC) Int

  putStrLn . intercalate sep $ "" : (show <$> setups)
  forM_ mutants $ \mutant -> do
    putStr $ show mutant ++ sep
    means <- forM setups $ \setup ->
      let ?mutant = mutant
       in if time
            then formatSeconds . fst <$> trials t (runSetupTime initialCov setup)
            else formatMeanCount . fst <$> trials t (runSetupCount initialCov setup)
    putStrLn $ intercalate sep means
