{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , GeneralizedNewtypeDeriving
           , KindSignatures
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TypeOperators
           , UndecidableInstances #-}

module Data.Expression.Z3 ( IToZ3
                          , toZ3
                          , IFromZ3
                          , fromZ3

                          -- Z3 API wrappers
                          , assert
                          , model
                          , unsatcore
                          , interpolate
                          , eliminate

                          -- re-export Z3 API
                          , Z3.local
                          , Z3.push
                          , Z3.pop
                          , Z3.check
                          , Z3.Result(..) ) where

import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Expression
import Data.List hiding (and, or)
import Data.Maybe
import Data.Proxy
import Data.Singletons
import Data.Singletons.Decide
import ListT hiding (head, null)
import Prelude hiding (and, or, not)

import qualified Data.Functor.Const as F
import qualified Data.Map as M
import qualified Z3.Monad as Z3

type Cache g = M.Map Z3.AST (DynamicallySortedFix g)

newtype Decoder g a b = Decoder { unwrap :: StateT (Cache g) (ListT a) b } deriving ( Functor, Applicative, Alternative, Monad, MonadIO )

instance Z3.MonadZ3 z3 => Z3.MonadZ3 (Decoder f z3) where
    getSolver  = Decoder . lift . lift $ Z3.getSolver
    getContext = Decoder . lift . lift $ Z3.getContext

class IFunctor f => IToZ3 f where
    itoZ3 :: forall (s :: Sort) z3. Z3.MonadZ3 z3 => f (F.Const (z3 Z3.AST)) s -> F.Const (z3 Z3.AST) s

sortToZ3 :: forall (s :: Sort) z3. Z3.MonadZ3 z3 => Sing s -> z3 Z3.Sort
sortToZ3  SBooleanSort    = Z3.mkBoolSort
sortToZ3  SIntegralSort   = Z3.mkIntSort
sortToZ3 (SArraySort i e) = do
    z3i <- sortToZ3 i
    z3e <- sortToZ3 e
    Z3.mkArraySort z3i z3e

instance IToZ3 VarF where
    itoZ3 (Var n s) = F.Const $ do
        z3n <- Z3.mkStringSymbol n
        z3s <- sortToZ3 s
        Z3.mkVar z3n z3s

instance IToZ3 ConjunctionF where
    itoZ3 (And as) = F.Const $ Z3.mkAnd =<< mapM F.getConst as

instance IToZ3 DisjunctionF where
    itoZ3 (Or os) = F.Const $ Z3.mkOr =<< mapM F.getConst os

instance IToZ3 NegationF where
    itoZ3 (Not n) = F.Const $ Z3.mkNot =<< F.getConst n

instance IToZ3 (UniversalF v) where
    itoZ3 (Forall vs a) = F.Const $ do
        z3vs <- mapM (Z3.toApp <=< toZ3) vs
        Z3.mkForallConst [] z3vs =<< F.getConst a

instance IToZ3 (ExistentialF v) where
    itoZ3 (Exists vs a) = F.Const $ do
        z3vs <- mapM (Z3.toApp <=< toZ3) vs
        Z3.mkExistsConst [] z3vs =<< F.getConst a

instance IToZ3 EqualityF where
    itoZ3 (Equals _ a b) = F.Const . join $ liftM2 Z3.mkEq (F.getConst a) (F.getConst b)

instance IToZ3 ArithmeticF where
    itoZ3 (Const c)      = F.Const $ Z3.mkInt c =<< Z3.mkIntSort
    itoZ3 (Add as)       = F.Const $ Z3.mkAdd =<< mapM F.getConst as
    itoZ3 (Mul ms)       = F.Const $ Z3.mkMul =<< mapM F.getConst ms
    itoZ3 (Divides c a)  = F.Const $ do
        z3c <- Z3.mkInt c =<< Z3.mkIntSort
        z30 <- Z3.mkInt 0 =<< Z3.mkIntSort
        z3a <- F.getConst a
        Z3.mkEq z30 =<< Z3.mkMod z3a z3c
    itoZ3 (LessThan a b) = F.Const . join $ liftM2 Z3.mkLt (F.getConst a) (F.getConst b)

instance IToZ3 IfThenElseF where
    itoZ3 (IfThenElse _ i t e) = F.Const . join $ liftM3 Z3.mkIte (F.getConst i) (F.getConst t) (F.getConst e)

instance IToZ3 ArrayF where
    itoZ3 (Select _ _ a i)   = F.Const . join $ liftM2 Z3.mkSelect (F.getConst a) (F.getConst i)
    itoZ3 (Store  _ _ a i v) = F.Const . join $ liftM3 Z3.mkStore  (F.getConst a) (F.getConst i) (F.getConst v)

instance ( IToZ3 f, IToZ3 g ) => IToZ3 (f :+: g) where
    itoZ3 (InL a) = itoZ3 a
    itoZ3 (InR b) = itoZ3 b

toZ3 :: forall f (s :: Sort) z3. ( IToZ3 f, Z3.MonadZ3 z3 ) => IFix f s -> z3 Z3.AST
toZ3 = F.getConst . icata itoZ3

class IFromZ3Into (f :: (Sort -> *) -> Sort -> *) (g :: (Sort -> *) -> Sort -> *) where
    ifromZ3App        :: Z3.MonadZ3 z3 => Proxy f -> (Z3.AST -> Decoder g z3 (DynamicallySortedFix g)) -> String -> Z3.App           -> Decoder g z3 (DynamicallySortedFix g)
    ifromZ3Quantifier :: Z3.MonadZ3 z3 => Proxy f -> (Z3.AST -> Decoder g z3 (DynamicallySortedFix g)) -> Bool -> [Z3.AST] -> Z3.AST -> Decoder g z3 (DynamicallySortedFix g)
    ifromZ3Numeral    :: Z3.MonadZ3 z3 => Proxy f ->                                                   Int                           -> Decoder g z3 (DynamicallySortedFix g)

    ifromZ3App        _ _ _ _   = empty
    ifromZ3Quantifier _ _ _ _ _ = empty
    ifromZ3Numeral    _ _       = empty

class IFromZ3Into f f => IFromZ3 f

sortFromZ3 :: Z3.MonadZ3 z3 => Z3.Sort -> z3 DynamicSort
sortFromZ3 s = do
    k <- Z3.getSortKind s
    case k of
        Z3.Z3_BOOL_SORT  -> return (DynamicSort SBooleanSort)
        Z3.Z3_INT_SORT   -> return (DynamicSort SIntegralSort)
        Z3.Z3_ARRAY_SORT -> do
            DynamicSort i <- sortFromZ3 =<< Z3.getArraySortDomain s
            DynamicSort e <- sortFromZ3 =<< Z3.getArraySortRange s
            return (DynamicSort $ SArraySort i e)
        _ -> error "unrecognized sort"

instance IFromZ3 VarF
instance VarF :<: g => IFromZ3Into VarF g where
    ifromZ3App _ _ name app = do
        guard . null =<< Z3.getAppArgs app
        DynamicSort s <- sortFromZ3 =<< Z3.getSort =<< Z3.appToAst app
        return $ dynvar name s

instance IFromZ3 ConjunctionF
instance ConjunctionF :<: g => IFromZ3Into ConjunctionF g where
    ifromZ3App _ _ "true" app = do
        guard . null =<< Z3.getAppArgs app
        return . toDynamicallySorted $ true
    ifromZ3App _ r "and" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just as -> return . toDynamicallySorted . and $ as
            _ -> empty
    ifromZ3App _ _ _ _ = empty

instance IFromZ3 DisjunctionF
instance DisjunctionF :<: g => IFromZ3Into DisjunctionF g where
    ifromZ3App _ _ "false" app = do
        guard . null =<< Z3.getAppArgs app
        return . toDynamicallySorted $ false
    ifromZ3App _ r "or" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just os -> return . toDynamicallySorted . or $ os
            _ -> empty
    ifromZ3App _ _ _ _ = empty

instance IFromZ3 NegationF
instance NegationF :<: g => IFromZ3Into NegationF g where
    ifromZ3App _ r "not" app = do
        args <- mapM r =<< Z3.getAppArgs app
        guard (length args == 1)
        case toStaticallySorted (head args) of
            Just n -> return . toDynamicallySorted . not $ n
            _ -> empty
    ifromZ3App _ _ _ _ = empty

varFromZ3 :: Z3.MonadZ3 z3 => Z3.AST -> Decoder VarF z3 (DynamicallySorted Var)
varFromZ3 = ifromZ3 (Proxy :: Proxy (VarF :: (Sort -> *) -> Sort -> *)) varFromZ3

local :: Z3.MonadZ3 z3 => Decoder VarF z3 a -> Decoder g z3 a
local = Decoder . lift . flip evalStateT M.empty . unwrap

instance SingI v => IFromZ3 (UniversalF v)
instance ( UniversalF v :<: g, SingI v ) => IFromZ3Into (UniversalF v) g where
    ifromZ3Quantifier _ r True as f = do
        vs <- mapM (local . varFromZ3) as
        let (vvs, rest) = partition (isVSorted . fst) $ zip vs as

        if null vvs then empty else do
            let (vs', bound) = unzip vvs

            vs'' <- mapM (Z3.toApp . snd) rest
            a'   <- if null vs'' then return f else Z3.mkForallConst [] vs'' f
            b    <- r =<< Z3.substituteVars a' bound

            case toStaticallySorted b of
                Just b'' -> return . toDynamicallySorted $ forall (fromJust . mapM toStaticallySorted $ vs' :: [IFix VarF v]) b''
                _ -> empty
        where

            isVSorted :: DynamicallySorted Var -> Bool
            isVSorted = isJust . ( toStaticallySorted :: DynamicallySorted Var -> Maybe (IFix VarF v) )

    ifromZ3Quantifier _ _ _ _ _ = empty

instance SingI v => IFromZ3 (ExistentialF v)
instance ( ExistentialF v :<: g, SingI v ) => IFromZ3Into (ExistentialF v) g where
    ifromZ3Quantifier _ r False as f = do
        vs <- mapM (local . varFromZ3) as
        let (vvs, rest) = partition (isVSorted . fst) $ zip vs as

        if null vvs then empty else do
            let (vs', bound) = unzip vvs

            vs'' <- mapM (Z3.toApp . snd) rest
            a'   <- if null vs'' then return f else Z3.mkExistsConst [] vs'' f
            b    <- r =<< Z3.substituteVars a' bound

            case toStaticallySorted b of
                Just b'' -> return . toDynamicallySorted $ exists (fromJust . mapM toStaticallySorted $ vs' :: [IFix VarF v]) b''
                _ -> empty
        where

            isVSorted :: DynamicallySorted Var -> Bool
            isVSorted = isJust . ( toStaticallySorted :: DynamicallySorted Var -> Maybe (IFix VarF v) )

    ifromZ3Quantifier _ _ _ _ _ = empty

instance IFromZ3 EqualityF
instance EqualityF :<: g => IFromZ3Into EqualityF g where
    ifromZ3App _ r name app = case name of
        "="   -> ifromZ3'' =<< mapM r =<< Z3.getAppArgs app
        "iff" -> ifromZ3'' =<< mapM r =<< Z3.getAppArgs app
        _ -> empty

        where

            ifromZ3'' :: Z3.MonadZ3 z3 => [DynamicallySortedFix g] -> Decoder g z3 (DynamicallySortedFix g)
            ifromZ3'' [DynamicallySorted s1 a, DynamicallySorted s2 b] = case s1 %~ s2 of
                Proved Refl -> return . toDynamicallySorted . inject $ Equals s1 a b
                Disproved _ -> empty
            ifromZ3'' _ = empty

instance IFromZ3 ArithmeticF
instance ArithmeticF :<: g => IFromZ3Into ArithmeticF g where
    ifromZ3Numeral _ c = return . toDynamicallySorted . cnst $ c
    ifromZ3App _ r "+" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just as -> return . toDynamicallySorted . add $ as
            _ -> empty
    ifromZ3App _ r "*" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just ms -> return . toDynamicallySorted . mul $ ms
            _ -> empty
    ifromZ3App _ r "<" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just [k, l] -> return . toDynamicallySorted $ k .<. l
            _ -> empty
    ifromZ3App _ r ">" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just [k, l] -> return . toDynamicallySorted $ l .<. k
            _ -> empty
    ifromZ3App _ r "<=" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just [k, l] -> return . toDynamicallySorted $ k .<. l .+. cnst 1
            _ -> empty
    ifromZ3App _ r ">=" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case mapM toStaticallySorted args of
            Just [k, l] -> return . toDynamicallySorted $ l .<. k .+. cnst 1
            _ -> empty
    ifromZ3App _ r "=" app = do
        args <- Z3.getAppArgs app
        case args of
            [m, n] -> modulo m n <|> modulo n m
            _ -> empty

        where

            modulo k l = do
                ka <- Z3.getAstKind k
                kb <- Z3.getAstKind l
                case (ka, kb) of
                    (Z3.Z3_NUMERAL_AST, Z3.Z3_APP_AST) -> do
                        z    <- Z3.getInt k
                        app'  <- Z3.toApp l
                        name <- Z3.getSymbolString =<< Z3.getDeclName =<< Z3.getAppDecl app'
                        case (z, name) of
                            (0, "mod") -> do
                                args <- Z3.getAppArgs app'
                                case args of
                                    [n, c] -> do
                                        kc <- Z3.getAstKind c
                                        case kc of
                                            Z3.Z3_NUMERAL_AST -> do
                                                c' <- fromIntegral <$> Z3.getInt c
                                                n' <- r n
                                                case toStaticallySorted n' of
                                                    Just n'' -> return . toDynamicallySorted $ c' .\. n''
                                                    _ -> empty
                                            _ -> empty
                                    _ -> empty
                            _ -> empty
                    _ -> empty
    ifromZ3App _ _ _ _ = empty

instance IFromZ3 IfThenElseF
instance IfThenElseF :<: g => IFromZ3Into IfThenElseF g where
    ifromZ3App _ r "if" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case args of
            [DynamicallySorted SBooleanSort i, DynamicallySorted ts t, DynamicallySorted es e] -> case ts %~ es of
                Proved Refl -> return . DynamicallySorted ts $ inject (IfThenElse ts i t e)
                Disproved _ -> empty
            _ -> empty
    ifromZ3App _ _ _ _ = empty

instance IFromZ3 ArrayF
instance ArrayF :<: g => IFromZ3Into ArrayF g where
    ifromZ3App _ r "select" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case args of
            [DynamicallySorted (SArraySort is1 es) a, DynamicallySorted is2 i] -> case is1 %~ is2 of
                Proved Refl -> return . DynamicallySorted es $ inject (Select is1 es a i)
                Disproved _ -> empty
            _ -> empty
    ifromZ3App _ r "store" app = do
        args <- mapM r =<< Z3.getAppArgs app
        case args of
            [DynamicallySorted as@(SArraySort _ _) a, DynamicallySorted is i, DynamicallySorted es v] -> case as %~ SArraySort is es of
                Proved Refl -> return . DynamicallySorted as $ inject (Store is es a i v)
                Disproved _ -> empty
            _ -> empty
    ifromZ3App _ _ _ _ = empty

instance ( IFromZ3Into f (f :+: g), IFromZ3Into g (f :+: g) ) => IFromZ3 (f :+: g)
instance ( IFromZ3Into f h, IFromZ3Into g h ) => IFromZ3Into (f :+: g) h where
    ifromZ3App        _ r name app = ifromZ3App (Proxy :: Proxy f) r name app <|> ifromZ3App (Proxy :: Proxy g) r name app
    ifromZ3Quantifier _ r q vs b   = ifromZ3Quantifier (Proxy :: Proxy f) r q vs b <|> ifromZ3Quantifier (Proxy :: Proxy g) r q vs b
    ifromZ3Numeral    _ c          = ifromZ3Numeral (Proxy :: Proxy f) c <|> ifromZ3Numeral (Proxy :: Proxy g) c

ifromZ3 :: forall (f :: (Sort -> *) -> Sort -> *)
                  (g :: (Sort -> *) -> Sort -> *)
                  z3.
           ( IFromZ3Into f g, Z3.MonadZ3 z3 )
         => Proxy f -> (Z3.AST -> Decoder g z3 (DynamicallySortedFix g)) -> Z3.AST -> Decoder g z3 (DynamicallySortedFix g)
ifromZ3 p r a = do
    c <- Decoder $ get
    if a `M.member` c then do
        return (c M.! a)
    else do
        k <- Z3.getAstKind a
        e <- case k of
            Z3.Z3_NUMERAL_AST -> ifromZ3Numeral p . fromIntegral =<< Z3.getInt a
            Z3.Z3_APP_AST -> do
                app <- Z3.toApp a
                name <- Z3.getSymbolString =<< Z3.getDeclName =<< Z3.getAppDecl app
                ifromZ3App p r name app
            Z3.Z3_QUANTIFIER_AST -> do
                t  <- Z3.isQuantifierForall a
                vs <- Z3.getQuantifierBoundVars a
                b  <- Z3.getQuantifierBody a
                ifromZ3Quantifier p r t vs b
            _ -> empty
        Decoder $ modify (M.insert a e)
        return e

fromZ3 :: forall (f :: (Sort -> *) -> Sort -> *) (s :: Sort) z3. ( IFromZ3 f, Z3.MonadZ3 z3, SingI s ) => Z3.AST -> z3 (IFix f s)
fromZ3 a = let r = ifromZ3 (Proxy :: Proxy f) r in head' <=< fmap (mapMaybe toStaticallySorted) . toList . flip evalStateT M.empty . unwrap . r $ a where
    head' (h : _) = return h
    head' _       = Z3.astToString a >>= \s -> error ("couldn't re-encode Z3 AST: " ++ s)


--
-- Z3 API
--

assert :: forall (f :: (Sort -> *) -> Sort -> *) z3. ( IToZ3 f, Z3.MonadZ3 z3 ) => IFix f 'BooleanSort -> z3 ()
assert = Z3.assert <=< toZ3

model :: forall (f :: (Sort -> *) -> Sort -> *) (s :: Sort) z3.
         ( IToZ3 f, IFromZ3 f, IShow f, Z3.MonadZ3 z3, SingI s ) => IFix f s -> z3 (IFix f s)
model e = do
    e' <- toZ3 e
    r  <- Z3.getModel
    case r of
        (Z3.Sat, Just m) -> do
            v <- Z3.modelEval m e' True
            case v of
                Just v' -> fromZ3 v'
                Nothing -> error $ "failed valuating " ++ show e
        (Z3.Unsat, _) -> error "failed extracting model from an unsatisfiable query"
        _             -> error "failed extracting model"

unsatcore :: forall (f :: (Sort -> *) -> Sort -> *) z3. ( IToZ3 f, Z3.MonadZ3 z3 ) => [IFix f 'BooleanSort] -> z3 [IFix f 'BooleanSort]
unsatcore fs = do
    as <- mapM toZ3 fs
    ps <- mapM (const $ Z3.mkFreshBoolVar "p") fs
    zipWithM_ (\a p -> Z3.assert =<< Z3.mkIff a p) as ps
    r <- Z3.checkAssumptions ps
    case r of
        Z3.Sat   -> error "failed extracting unsat core from a satisfiable query"
        Z3.Unsat -> map (M.fromList (zip ps fs) M.!) <$> Z3.getUnsatCore
        _        -> error "failed extracting unsat core"

interpolate :: forall (f :: (Sort -> *) -> Sort -> *) z3.
               ( IToZ3 f, IFromZ3 f, Z3.MonadZ3 z3 ) => [IFix f 'BooleanSort] -> z3 [IFix f 'BooleanSort]
interpolate []        = return []
interpolate [_]       = return []
interpolate (f : fs)  = do
    f'  <- toZ3 f
    fs' <- mapM toZ3 fs
    q   <- foldM (\a g -> Z3.mkAnd . (: [g]) =<< Z3.mkInterpolant a) f' fs'
    r   <- Z3.local $ Z3.computeInterpolant q =<< Z3.mkParams

    case r of
        Just (Left  _ ) -> error "failed extracting interpolants from a satisfiable query"
        Just (Right is) -> mapM fromZ3 is
        _               -> error "failed extracting interpolants"

eliminate :: forall (f :: (Sort -> *) -> Sort -> *) z3.
             ( IToZ3 f, IFromZ3 f, Z3.MonadZ3 z3 ) => IFix f 'BooleanSort -> z3 (IFix f 'BooleanSort)
eliminate f = do
    g <- Z3.mkGoal True True False
    Z3.goalAssert g =<< toZ3 f
    qe  <- Z3.mkTactic "qe"
    aig <- Z3.mkTactic "aig"
    t   <- Z3.andThenTactic qe aig
    a   <- Z3.applyTactic t g
    fromZ3 =<< Z3.mkAnd =<< Z3.getGoalFormulas =<< Z3.getApplyResultSubgoal a 0
