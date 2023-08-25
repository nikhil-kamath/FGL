{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Types where

import Config
import Data.Graph.Inductive
import Data.Tree
import Test.QuickCheck
import Util (applyIf, eqLayers, eqSetBy, (=~=))

-- * Type: Set

-- wrapper around the list type which allows for checking
-- if two lists contain the same elements
newtype Set a = Set [a]
  deriving (Show)

instance Eq a => Eq (Set a) where
  (==) :: Set a -> Set a -> Bool
  (Set xs) == (Set ys) = xs =~= ys

-- * Type: Equivs

-- wrapper which generates 2 identical graphs
-- using 2 separate implementations of the Graph datatype
data Equivs gr gr' a b = gr a b :?=: gr' a b deriving (Show)

instance (Graph gr, Graph gr0, Arbitrary (gr a b), Arbitrary (gr0 a b), Num b) => Arbitrary (Equivs gr gr0 a b) where
  arbitrary = do
    -- connected graph generation
    og <-
      if connected
        then arbitrary `suchThat` isConnected
        else (arbitrary :: Gen (gr a b))

    let ns = labNodes og
        es = labEdges og
        es' = applyIf positive es (map (\(a, b, x) -> (a, b, abs x)))
        es'' = applyIf undirected es' (\xs -> xs ++ [(b, a, x) | (a, b, x) <- xs])
        g' = mkGraph ns es'' :: gr a b
        g'' = mkGraph ns es'' :: gr0 a b

    return (g' :?=: g'')

  shrink (g :?=: _) =
    let gs = shrink g
     in map (\j -> j :?=: convert j) gs
    where
      convert :: gr a b -> gr0 a b
      convert x = mkGraph (labNodes x) (labEdges x)

-- * Type: LayerSet

-- Type which checks whether two trees are equal leyer-by-layer.
-- Essentially the set property lifted to trees.
newtype LayerSet a = LayerSet [Tree a] deriving (Show)

instance Eq a => Eq (LayerSet a) where
  (LayerSet ts) == (LayerSet ts') = eqSetBy eqLayers ts ts'

-- * Type: NEquivs

-- A version of Equivs which comes with a subset of the nodes
-- which are guaranteed to be within the graph
data NEquivs gr gr' a b = NE (gr a b) (gr' a b) [Node] deriving (Show)

instance (Graph gr, Graph gr', Arbitrary (gr a b), Num b) => Arbitrary (NEquivs gr gr' a b) where
  arbitrary :: Gen (NEquivs gr gr' a b)
  arbitrary = do
    g <- arbitrary :: Gen (gr a b)
    sub <- sublistOf (nodes g)
    let ns = labNodes g
        -- es  = labEdges g
        es = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- POSITIVE WEIGHTS
        -- es  = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- NEGATIVE WEIGHTS
        es' = es ++ [(b, a, x) | (a, b, x) <- es] -- UNDIRECTED
        g' = mkGraph ns es' :: gr a b
        g'' = mkGraph ns es' :: gr' a b
    return (NE g' g'' sub)
