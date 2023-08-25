{-# LANGUAGE RankNTypes #-}

module Util where

import Data.List
import Data.Graph.Inductive
import Data.Tree


-- returns whether two lists contain the same elements with the same cardinalities
(=~=) :: Eq a => [a] -> [a] -> Bool
(=~=) xs ys = null (xs \\ ys) && null (ys \\ xs)


-- convert the second graph into an instance of the first
-- to compare 2 different implementations
equal' :: (Eq a, Eq b, Graph gr, Graph gr') => gr a b -> gr' a b -> Bool
equal' g g' =
  g `equal` g''
  where
    ns = labNodes g'
    es = labEdges g'
    g'' = mkGraph ns es

convert :: (Graph gr, Graph gr1) => gr a b -> gr1 a b -> gr a b
convert _ g =
  mkGraph (labNodes g) (labEdges g)

-- applies a function if the first argument is True, otherwise returns the input
applyIf :: Bool -> a -> (a -> a) -> a
applyIf False x _ = x
applyIf True x f = f x

-- helper method to see if two trees have the same structure depthwise
-- ie. two LayerSets are equal if their nodes are at the same depths
eqSetBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqSetBy f xs ys =
  length xs == length ys
    && length (intersectBy f xs ys) == length xs
    && length (unionBy f xs ys) == length xs

eqLayers :: Eq a => Tree a -> Tree a -> Bool
eqLayers (Node x ts) (Node x' ts') =
  x == x' && eqSetBy eqLayers ts ts'