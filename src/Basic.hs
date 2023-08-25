{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Basic where

import Data.Graph.Inductive
import Data.List
import Data.Maybe
import Test.QuickCheck
import Util

-- * Section 1: Validity Testing

-- let's come up with some things that all correct
-- implementations of Graph should have

-- Let's start with some basic checks.

-- All edges start from existing nodes
prop_ValidEdges :: Graph gr => gr a b -> Bool
prop_ValidEdges g =
  all (\(a, _, _) -> a `elem` ns) (labEdges g)
  where
    ns = nodes g

-- All nodes lie within the produced range
prop_ValidRange :: Graph gr => gr a b -> Bool
prop_ValidRange g =
  all (`elem` [fst range .. snd range]) (nodes g)
  where
    range = nodeRange g

-- The number of nodes is correct
prop_ValidNodes :: Graph gr => gr a b -> Bool
prop_ValidNodes g =
  length (nodes g) == noNodes g

-- Empty graphs are empty
prop_ValidEmpty :: forall gr a b. Graph gr => gr a b -> Bool
prop_ValidEmpty _ =
  null (nodes emp) && isEmpty emp
  where
    emp = empty :: gr a b

-- We can combine these basic tests into one validity property
prop_Valid :: Graph gr => gr a b -> Bool
prop_Valid g =
  all
    (\f -> f g)
    [ prop_ValidEdges,
      prop_ValidRange,
      prop_ValidNodes,
      prop_ValidEmpty
    ]

-- * Section 2: Postconditions on Creations of Graphs

-- mkGraph uses all (and only) the nodes that we input, with the last value for a key
-- taking precedence over any duplicates (so we `reverse ns`).
prop_MkGraphNodes :: forall gr a b. (Graph gr, Eq a) => gr a b -> [LNode a] -> [LEdge b] -> Bool
prop_MkGraphNodes _ ns es =
  labNodes g =~= nubBy (\(x, _) (y, _) -> x == y) (reverse ns)
  where
    g = mkGraph ns es :: gr a b

-- mkGraph uses all of the edges (and only those edges) that we input as long as they
-- originate from a node in nodes
prop_MkGraphEdges :: forall gr a b. (Graph gr, Eq b) => gr a b -> [LNode a] -> [LEdge b] -> Bool
prop_MkGraphEdges _ ns es =
  labEdges g =~= filter (\(x, _, _) -> x `gelem` g) es
  where
    g = mkGraph ns es :: gr a b

-- mkGraph makes a valid graph
prop_MkGraphValid :: forall gr a b. (Graph gr) => gr a b -> [LNode a] -> [LEdge b] -> Bool
prop_MkGraphValid _ ns es =
  prop_Valid (mkGraph ns es :: gr a b)

-- * Section 3: Postconditions on Decompositions of Graphs

-- Section 3.1: Properties of the decomposed graph

-- matching on a node removes the node
prop_MatchRemovesNode :: Graph gr => gr a b -> Node -> Property
prop_MatchRemovesNode g n =
  n
    `gelem` g
    ==> n
    `notElem` nodes g'
  where
    g' = snd $ n `match` g

-- matching on a node removes the edges to and from the node
prop_MatchRemovesEdges :: Graph gr => gr a b -> Node -> Property
prop_MatchRemovesEdges g n =
  n
    `gelem` g
    ==> not
    $ any (\(a, b, _) -> n == a || n == b) (labEdges g')
  where
    g' = snd $ n `match` g

-- matching on a node which isnt in the graph doesn't change the graph
prop_MatchNotInGraph :: (Graph gr, Eq (gr a b)) => gr a b -> Node -> Property
prop_MatchNotInGraph g n =
  not (n `gelem` g)
    ==> g
    == g'
  where
    g' = snd $ n `match` g

-- the rest of the graph remains the same
-- this property engulfs prop_MatchNotInGraph
prop_MatchRetainsGraph :: (Graph gr, Eq a, Eq b) => gr a b -> Node -> Property
prop_MatchRetainsGraph g n =
  n
    `gelem` g
    ==> equalBut n g g'
  where
    g' = snd $ n `match` g

    -- checks if two graphs are equal except for node `n`
    equalBut n g g' =
      filter (\(a, b, _) -> a /= n && b /= n) (labEdges g) =~= labEdges g'
        && filter (\(a, _) -> a /= n) (labNodes g) =~= labNodes g'

-- Section 3.2: Properties of the decomposed context

-- matching on a node not in the graph returns no context
prop_MatchNotInGraph' :: (Graph gr) => gr a b -> Node -> Property
prop_MatchNotInGraph' g n =
  not (n `gelem` g)
    ==> isNothing
    $ fst (n `match` g)

-- the context takes the correct node
prop_MatchCorrectNode :: (Graph gr) => gr a b -> Node -> Property
prop_MatchCorrectNode g n =
  n
    `gelem` g
    ==> Just n
    == n'
  where
    d = fst $ n `match` g
    n' = d >>= (Just . node')

-- the context keeps the same value as the original graph
prop_MatchCorrectValue :: (Graph gr, Eq a) => gr a b -> Node -> Property
prop_MatchCorrectValue g n =
  n
    `gelem` g
    ==> v
    == v'
  where
    v = lab g n

    d = fst $ n `match` g
    v' = d >>= (Just . lab')

-- the matched context keeps the same edges as the original graph
prop_MatchCorrectEdges :: (Graph gr, Eq b) => gr a b -> Node -> Property
prop_MatchCorrectEdges g n =
  n
    `gelem` g
    ==> a
    =~= a'
  where
    a = lneighbors g n

    d = fst $ n `match` g
    a' = case d of
      Just (f, _, _, t) -> f ++ t
      Nothing -> []

-- we can collect all of the match properties into one property
prop_Match :: (Graph gr, Eq a, Eq b) => gr a b -> Node -> Property
prop_Match g n =
  conjoin $
    map
      (\p -> p g n)
      [ prop_MatchRemovesNode,
        prop_MatchRemovesEdges,
        prop_MatchRetainsGraph,
        prop_MatchCorrectNode,
        prop_MatchCorrectValue,
        prop_MatchCorrectEdges
      ]

-- matchAny passes all the properties for one of the possible nodes
-- matchAny :: (Graph gr) => gr a b -> Property
-- matchAny g = not (isEmpty g) ==>
--     any (prop_Match g) (nodes g)

-- * Section 4: Model-Based Testing of Maps

-- these tests encapsulate many other properties, which we dont need to test for
-- including:
-- map on empty -> empty
-- map retains size
-- map retains order
-- map retains shape
-- map retains in/out degrees

mapNodes :: (a -> b) -> [LNode a] -> [LNode b]
mapNodes f = fmap $ fmap f

mapEdges :: (a -> b) -> [LEdge a] -> [LEdge b]
mapEdges f = fmap $ fmap f

-- nemap gives the same results as mapping before mkGraph
prop_NEMapModel :: forall gr a b c d. (DynGraph gr, Eq c, Eq d) => gr a b -> Fun a c -> Fun b d -> [LNode a] -> [LEdge b] -> Bool
prop_NEMapModel _ (Fn (fn :: a -> c)) (Fn (fe :: b -> d)) ns es =
  equal g g'
  where
    g = nemap fn fe (mkGraph ns es :: gr a b)
    g' = mkGraph (mapNodes fn ns) (mapEdges fe es)

-- making sure nmap performs similarly
prop_NMapModel :: forall gr a b c. (DynGraph gr, Eq c, Eq b) => gr a b -> Fun a c -> [LNode a] -> [LEdge b] -> Bool
prop_NMapModel _ (Fn (fn :: a -> c)) ns es =
  equal g g'
  where
    g = nmap fn (mkGraph ns es :: gr a b)
    g' = mkGraph (mapNodes fn ns) es

-- making sure emap performs similarly
prop_EMapModel :: forall gr a b d. (DynGraph gr, Eq a, Eq d) => gr a b -> Fun b d -> [LNode a] -> [LEdge b] -> Bool
prop_EMapModel _ (Fn (fe :: b -> d)) ns es =
  equal g g'
  where
    g = emap fe (mkGraph ns es :: gr a b)
    g' = mkGraph ns (mapEdges fe es)

-- repeated maps should do the same as mapping over the composition
prop_DoubleMap ::
  forall gr a b c d e f.
  (DynGraph gr, Eq e, Eq f) =>
  gr a b ->
  Fun a c ->
  Fun c e ->
  Fun b d ->
  Fun d f ->
  [LNode a] ->
  [LEdge b] ->
  Bool
prop_DoubleMap
  _
  (Fn (fn :: a -> c))
  (Fn (fn' :: c -> e))
  (Fn (fe :: b -> d))
  (Fn (fe' :: d -> f))
  ns
  es =
    equal g g'
    where
      g = nemap (fn' . fn) (fe' . fe) (mkGraph ns es :: gr a b)
      g' = nemap fn' fe' $ nemap fn fe (mkGraph ns es :: gr a b)

-- converting functions from nemap-form to context maps should give the same results
-- NOTE: we cannot do this the other way around!
--       gmap has more information than nemap and cannot be "shrunk"
--       to expect the same results. for example, if the function passed to
--       gmap uses the Node indices themselves, there is no equivalent for nemap
prop_NEMapToGMap ::
  forall gr a b c d.
  (DynGraph gr, Eq c, Eq d) =>
  gr a b ->
  Fun a c ->
  Fun b d ->
  Bool
prop_NEMapToGMap g (Fn (fn :: a -> c)) (Fn (fe :: b -> d)) =
  equal g' g''
  where
    g' = nemap fn fe g
    g'' = gmap fc g
      where
        fes = fmap (\(b, n) -> (fe b, n))
        fc (ins, n, x, outs) = (fes ins, n, fn x, fes outs)

-- * Section 5: Metamorphic Testing of Fold

-- adding a context to a graph then folding it
-- "should" be equal to applying the fold function to the original result
-- and the new context. This is because, unlike lists, graph folds have an arbitrary
-- folding order, thus it shouldn't matter when the context is added.
--
-- this property doesn't hold, though, as these later-added contexts
-- may have different behaviors based on their dependencies in the graph
--
-- this property also doesnt hold when the `Fun` argument isn't commutative
-- (see most counterexamples given by qc)
prop_UFoldFusionWrong ::
  forall gr a b c.
  (DynGraph gr, Eq c) =>
  gr a b ->
  Context a b ->
  Fun (Context a b, c) c ->
  c ->
  Bool
prop_UFoldFusionWrong g c (Fn2 f) a =
  res == res'
  where
    res = ufold f a (c & g)
    res' = f c (ufold f a g)

-- * Section 6: Complex Functions

-- gfiltermap with no filter should reconstruct the original graph
prop_EverythingFilter ::
  forall gr a b.
  (DynGraph gr, Eq a, Eq b) =>
  gr a b ->
  Bool
prop_EverythingFilter g =
  g `equal` g'
  where
    g' = gfiltermap Just g

-- gfiltermap with all-block filter gives empty
prop_NothingFilter ::
  forall gr a b.
  (DynGraph gr, Eq a, Eq b) =>
  gr a b ->
  Bool
prop_NothingFilter g =
  (empty :: gr a b) `equal` g'
  where
    g' = gfiltermap (const Nothing) g