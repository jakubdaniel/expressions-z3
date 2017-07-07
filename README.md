[![Hackage](https://img.shields.io/hackage/v/expressions-z3.svg)](https://hackage.haskell.org/package/expressions-z3)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/expressions-z3.svg)](https://packdeps.haskellers.com/feed?needle=expressions-z3)
[![Build Status](https://travis-ci.org/jakubdaniel/expressions-z3.svg?branch=master)](https://travis-ci.org/jakubdaniel/expressions-z3)

# Usage

    λ> :set -XTypeInType
    λ> :m Z3.Monad Data.Expression Data.Expression.Z3

## Encode expression in Z3 AST

    λ> evalZ3 $ astToString =<< toZ3 (forall [var "x" :: Var 'IntegralSort] (exists [var "y" :: Var 'IntegralSort] (var "x" .+. var "y" .=. cnst 0)) :: Lia 'BooleanSort)
    (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0)))

## Decode expression from Z3 AST

    λ> :{
    evalZ3 $ do
      x  <- mkIntVar =<< mkStringSymbol "x"
      x' <- toApp x
      y  <- mkIntVar =<< mkStringSymbol "y"
      y' <- toApp y
      z  <- mkInt 0 =<< mkIntSort
      fromZ3 =<< mkForallConst [] [x'] =<< mkExistsConst [] [y'] =<< mkEq z =<< mkAdd [x, y] :: Z3 (Lia 'BooleanSort)
    :}
    (forall ((x : int)) (exists ((y : int)) (= 0 (+ (x : int) (y : int)))))
