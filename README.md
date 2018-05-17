[![Hackage](https://img.shields.io/hackage/v/expressions-z3.svg)](https://hackage.haskell.org/package/expressions-z3)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/expressions-z3.svg)](https://packdeps.haskellers.com/feed?needle=expressions-z3)
[![Build Status](https://travis-ci.org/jakubdaniel/expressions-z3.svg?branch=master)](https://travis-ci.org/jakubdaniel/expressions-z3)

# Usage

    λ> :set -XDataKinds -XFlexibleContexts -XKindSignatures -XRankNTypes -XTypeInType -XTypeOperators
    λ> :m Data.Expression Data.Expression.Z3 Data.Singletons
    λ> import Z3.Monad hiding (assert)

## Encode expression in Z3 AST

    λ> :{
    let x, y :: forall f. VarF :<: f => IFix f 'IntegralSort
        x = var "x"
        y = var "y"
    :}
    λ> evalZ3 $ astToString =<< toZ3 (forall [x] (exists [y] (x .+. y .=. cnst 0)) :: Lia 'BooleanSort)
    (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0)))

## Decode expression from Z3 AST

    λ> :{
    evalZ3 $ do
      x  <- mkIntVar =<< mkStringSymbol "x"
      x' <- toApp x
      y  <- mkIntVar =<< mkStringSymbol "y"
      y' <- toApp y
      z  <- mkInt 0 =<< mkIntSort
      fromZ3 =<< mkForallConst [] [x']
             =<< mkExistsConst [] [y']
             =<< mkEq z
             =<< mkAdd [x, y] :: Z3 (Lia 'BooleanSort)
    :}
    (forall ((x : int)) (exists ((y : int)) (= 0 (+ (x : int) (y : int)))))

## Z3 API

    λ> :{
    evalZ3 $ do
      let x', y' :: forall f. VarF :<: f => IFix f 'IntegralSort
          x' = var "x"
          y' = var "y"

          x, y :: Lia 'IntegralSort
          x = x'
          y = y'

      m <- local $ do
        assert (x .=. cnst 42)
        model x

      uc <- unsatcore [ x .=. cnst 2, x .=. cnst 1, y .=. cnst 2, x ./=. y ]

      i <- interpolate [ x .=. cnst 2, x .=. y, y .=. cnst 4 ]

      e <- eliminate $ forall [x'] (x .=. cnst 2)

      return (m, uc, i, e)
    :}
    (42,[(= (x : int) 2),(= (x : int) 1)],[(= (x : int) 2),(not (= (y : int) 4))],false)
