{-# LANGUAGE DataKinds
           , FlexibleContexts
           , GADTs
           , KindSignatures
           , OverloadedStrings
           , RankNTypes
           , TypeOperators #-}

import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Singletons
import Prelude hiding (and, not)
import Z3.Monad hiding (Sort, eval, assert, local)

import qualified Prelude as P

import Data.Expression
import Data.Expression.Z3

data Test where
    IsConstant :: forall f. ( IShow f, ArithmeticF :<: f ) => IFix f 'IntegralSort -> Int -> Test
    IsOneOf    :: forall f (s :: Sort). ( IShow f, IEq1 f, IFunctor f ) => IFix f s -> [IFix f s] -> Test
    ShouldBe   :: forall f. ( IToZ3 f, IShow f ) => IFix f 'BooleanSort -> Result -> Test
    HasModel   :: forall f (s :: Sort).
                  ( IToZ3 f
                  , IFromZ3 f
                  , IEq1 f
                  , IShow f
                  , EqualityF :<: f
                  , NegationF :<: f
                  , SingI s )
               => IFix f 'BooleanSort -> (IFix f s, IFix f s) -> Test

test :: Test -> (String, IO Bool)
test (IsConstant a v) =
    ( "Test " ++ show a ++ " is an expected constant value"
    , return $ case match a of
        Just (Const c) -> c == v
        _              -> False )
test (IsOneOf a bs) =
    ( "Test " ++ show a ++ " is one of " ++ show bs
    , return $ any (a ==) bs )
test (ShouldBe a r) =
    ( "Test " ++ show a ++ " is " ++ show r
    , evalZ3 $ do
        assert a
        liftA (r ==) check )
test (HasModel a (ex, ev)) =
    ( "Test " ++ show a ++ " has model with " ++ show ex ++ " = " ++ show ev
    , evalZ3 $ do
        assert a
        go ) where

    go = do
      _  <- check
      zx <- toZ3 ex
      mw <- runMaybeT $ do
          m  <- MaybeT $ snd <$> getModel
          zv <- MaybeT $ modelEval m zx True
          lift $ fromZ3 zv
      case mw of
          Nothing -> return False
          Just ew ->
              if ev == ew then return True else do
                  assert (ex ./=. ew)
                  go

main :: IO ()
main = do
    -- model
    m <- evalZ3 . local $ do
        assert j
        model (x :: Lia 'IntegralSort)

    -- unsat
    (u : _) <- evalZ3 $ unsatcore [ not i, h, true, k ]

    -- interpolate
    [l] <- evalZ3 $ interpolate [ h, not i ]

    -- eliminate
    v <- evalZ3 $ eliminate g

    let
        p1  =                 f `ShouldBe`   Sat
        p2  =             not f `ShouldBe`   Unsat
        p3  =                 g `ShouldBe`   Sat
        p4  =             not g `ShouldBe`   Unsat
        p5  =                 h `HasModel`   (x, c5)
        p6  =                 i `HasModel`   (x, c5)
        p7  =                 m `IsConstant` 8
        p8  =                 u `IsOneOf`    [ h, not i, k ]
        p9  = not (h .->. l)    `ShouldBe`   Unsat
        p10 =     (l .&. not i) `ShouldBe`   Unsat
        p11 =             not v `ShouldBe`   Unsat

        eval t = do
            let (n, a) = test t
            putStr $ n ++ take (column - length n) (repeat ' ') ++ "   "
            r <- a
            if r then putStrLn "passed" else putStrLn "failed"
            return r

        props = [ p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11 ]
        tests = map test props
        column = maximum $ map (length . fst) tests

    putStrLn ""
    guard . P.and =<< traverse eval props where

      f, g, h, i, j :: Lia 'BooleanSort
      f = forall [x] (exists [y] (x .+. y .=. c0))
      g = forall [x, y] (x .=. y .->. (x .+. c1) .=. (y .+. c1))
      h = (x .+. m1 .=. y .+. c1) .&. (y .+. m1 .=. z .+. c1) .&. (z .=. c1)
      i = x .>. c0
      j = x .=. c5 .+. c1 .+. c1 .+. c1
      k = x .=. y .+. c1 .+. c1

      x, y, z :: forall f. VarF :<: f => IFix f 'IntegralSort
      x = var "x"
      y = var "y"
      z = var "z"

      c0, c1, c5, m1 :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort
      c0 = cnst 0
      c1 = cnst 1
      c5 = cnst 5
      m1 = cnst (-1)
