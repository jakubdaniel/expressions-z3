{-# LANGUAGE DataKinds
           , FlexibleContexts
           , GADTs
           , KindSignatures
           , OverloadedStrings
           , RankNTypes
           , TypeOperators #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Singletons
import Prelude hiding (and, not)
import Z3.Monad hiding (Sort, eval)

import qualified Prelude as P

import Data.Expression
import Data.Expression.Z3

data Test where
    ShouldBe :: forall f. ( IToZ3 f, IShow f ) => IFix f 'BooleanSort -> Result -> Test
    HasModel :: forall f (s :: Sort).
                ( IToZ3 f
                , IFromZ3 f
                , IEq1 f
                , IShow f
                , EqualityF :<: f
                , NegationF :<: f
                , SingI s )
             => IFix f 'BooleanSort -> (IFix f s, IFix f s) -> Test

test :: Test -> (String, IO Bool)
test (ShouldBe a r) =
    ( "Test " ++ show a ++ " is " ++ show r
    , evalZ3 $ do
        assert =<< toZ3 a
        liftA (r ==) check )
test (HasModel a (ex, ev)) =
    ( "Test " ++ show a ++ " has model with " ++ show ex ++ " = " ++ show ev
    , evalZ3 $ do
        assert =<< toZ3 a
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
                  assert =<< toZ3 (ex ./=. ew)
                  go

main :: IO ()
main = do
    putStrLn ""
    guard . P.and =<< traverse eval props where

    props = [ p1, p2, p3, p4, p5, p6 ]
    tests = map test props
    column = maximum $ map (length . fst) tests

    eval t = do
        let (n, a) = test t
        putStr $ n ++ take (column - length n) (repeat ' ') ++ "   "
        r <- a
        if r then putStrLn "passed" else putStrLn "failed"
        return r

    p1 =     f `ShouldBe` Sat
    p2 = not f `ShouldBe` Unsat
    p3 =     g `ShouldBe` Sat
    p4 = not g `ShouldBe` Unsat
    p5 =     h `HasModel`  (x, c5)
    p6 =     i `HasModel`  (x, c5)

    f, g, h, i :: Lia 'BooleanSort
    f = forall [x] (exists [y] (x .+. y .=. c0))
    g = forall [x, y] (x .=. y .->. (x .+. c1) .=. (y .+. c1))
    h = (x .+. m1 .=. y .+. c1) .&. (y .+. m1 .=. z .+. c1) .&. (z .=. c1)
    i = x .>. c0

    x, y, z :: forall f. VarF :<: f => IFix f 'IntegralSort
    x = var "x"
    y = var "y"
    z = var "z"

    c0, c1, c5, m1 :: forall f. ArithmeticF :<: f => IFix f 'IntegralSort
    c0 = cnst 0
    c1 = cnst 1
    c5 = cnst 5
    m1 = cnst (-1)
