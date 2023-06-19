{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}

module Types where

import Data.List
import Data.Tree
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive
import Data.Graph.Inductive.Arbitrary
import Test.QuickCheck
import Data.Kind (Type)


-- * Here's some settings which our graph generator can enforce
undirected :: Bool
undirected = True

positive :: Bool
positive = True

connected :: Bool
connected = True
-- * Modify ^^^^^^^^^^^^^^^^^^^^^



-- returns whether two lists contain the same elements with the same cardinalities
(=~=) :: Eq a => [a] -> [a] -> Bool
(=~=) xs ys = null (xs \\ ys) && null (ys \\ xs)

-- applies a function if the input is True, otherwise returns the input
applyIf :: Bool -> a -> (a -> a) -> a
applyIf False x _ = x
applyIf True  x f = f x

newtype Set a = Set [a]
    deriving Show

instance Eq a => Eq (Set a) where
    (Set xs) == (Set ys) = xs =~= ys

-- dataclass for making equivalent graph pairs
data Equivs gr gr' a b = gr a b :?=: gr' a b deriving Show

-- instance (Graph gr, Graph gr0, Arbitrary (gr a b), Num b) => Arbitrary (Equivs gr gr0 a b) where
--     arbitrary :: Gen (Equivs gr gr0 a b)
--     arbitrary = do
--         -- connected graph generation
--         -- og <- if connected
--         --     then (arbitrary :: Gen (gr a b)) `suchThat` isConnected
--         --     else (arbitrary :: Gen (gr a b))
--         og <- arbitrary :: Gen (gr a b)

--         let ns   = labNodes og
--             es   = labEdges og
--             es'  = applyIf positive   es  (map (\(a, b, x) -> (a, b, abs x)))
--             es'' = applyIf undirected es' (\xs -> xs ++ [(b, a, x) | (a, b, x) <- xs])
--             g'   = mkGraph ns es'' :: gr a b
--             g''  = mkGraph ns es'' :: gr0 a b

--         return (g' :?=: g'')

--     shrink :: Equivs gr gr0 a b -> [Equivs gr gr0 a b]
--     shrink (g :?=: _) =
--         let gs = shrink g in
--             map (\j -> j :?=: convert j) gs
--         where
--             convert :: gr a b -> gr0 a b
--             convert x = mkGraph (labNodes x) (labEdges x)

instance (Graph gr, Graph gr', Arbitrary (gr a b), Num b) => Arbitrary (Equivs gr gr' a b) where
    arbitrary :: Gen (Equivs gr gr' a b)
    arbitrary = do
        g <- arbitrary :: Gen (gr a b)
        let ns  = labNodes g
            es  = labEdges g
            g'  = mkGraph ns es :: gr a b
            g'' = mkGraph ns es :: gr' a b

        return (g' :?=: g'')

    shrink :: Equivs gr gr' a b -> [Equivs gr gr' a b]
    shrink (g :?=: _) =
        let gs = shrink g in
            map (\j -> j :?=: convert j) gs
        where
            convert :: gr a b -> gr' a b
            convert x = mkGraph (labNodes x) (labEdges x)



-- helper method to see if two trees have the same structure depthwise
-- ie. two LayerSets are equal if their nodes are at the same depths
eqSetBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqSetBy f xs ys =
  length xs                    == length ys &&
  length (intersectBy f xs ys) == length xs &&
  length (unionBy f xs ys)     == length xs

eqLayers :: Eq a => Tree a -> Tree a -> Bool
eqLayers (Node x ts) (Node x' ts') =
  x == x' && eqSetBy eqLayers ts ts'

newtype LayerSet a = LayerSet [Tree a] deriving Show

instance Eq a => Eq (LayerSet a) where
  (LayerSet ts) == (LayerSet ts') = eqSetBy eqLayers ts ts'

-- Let's create a new typeclass which includes a subset of the nodes
-- so that we don't need to include it as a precondition.

data NEquivs gr gr' a b = NE (gr a b) (gr' a b) [Node] deriving Show

instance (Graph gr, Graph gr', Arbitrary (gr a b), Num b) => Arbitrary (NEquivs gr gr' a b) where
    arbitrary = do
        g   <- arbitrary :: Gen (gr a b)
        sub <- sublistOf (nodes g)
        let ns  = labNodes g
            -- es  = labEdges g
            es  = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- POSITIVE WEIGHTS
            -- es  = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- NEGATIVE WEIGHTS
            es'  = es ++ [(b, a, x) | (a, b, x) <- es] -- UNDIRECTED
            g'  = mkGraph ns es' :: gr a b
            g'' = mkGraph ns es' :: gr' a b
        return (NE g' g'' sub)


