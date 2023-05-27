{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Lib where
-- Created by Nikhil Kamath
-- 507012

import Test.QuickCheck
import Data.Graph.Inductive
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Arbitrary
import Data.Tree
import Data.List
import Data.Maybe
import Control.Monad (forM_)

-- returns whether two lists contain the same elements with the same cardinalities
(=~=) :: Eq a => [a] -> [a] -> Bool
(=~=) xs ys = null (xs \\ ys) && null (ys \\ xs)

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
prop_Valid g = all (\f -> f g)
    [
        prop_ValidEdges,
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
prop_MatchRemovesNode g n = n `gelem` g ==>
    n `notElem` nodes g'
    where
        g' = snd $ n `match` g

-- matching on a node removes the edges to and from the node
prop_MatchRemovesEdges :: Graph gr => gr a b -> Node -> Property
prop_MatchRemovesEdges g n = n `gelem` g ==>
    not $ any (\(a, b, _) -> n == a || n == b) (labEdges g')
    where
        g' = snd $ n `match` g

-- matching on a node which isnt in the graph doesn't change the graph
prop_MatchNotInGraph :: (Graph gr, Eq (gr a b)) => gr a b -> Node -> Property
prop_MatchNotInGraph g n = not (n `gelem` g) ==>
    g == g'
    where
        g' = snd $ n `match` g

-- the rest of the graph remains the same
-- this property engulfs prop_MatchNotInGraph
prop_MatchRetainsGraph :: (Graph gr, Eq a, Eq b) => gr a b -> Node -> Property
prop_MatchRetainsGraph g n = n `gelem` g ==>
    equalBut n g g'
    where
        g' = snd $ n `match` g

        -- checks if two graphs are equal except for node `n`
        equalBut n g g' =
            filter (\(a, b, _) -> a /= n && b /= n) (labEdges g) =~= labEdges g' &&
            filter (\(a, _) -> a /= n)              (labNodes g) =~= labNodes g'

-- Section 3.2: Properties of the decomposed context

-- matching on a node not in the graph returns no context
prop_MatchNotInGraph' :: (Graph gr) => gr a b -> Node -> Property
prop_MatchNotInGraph' g n = not (n `gelem` g) ==>
    isNothing $ fst (n `match` g)

-- the context takes the correct node
prop_MatchCorrectNode :: (Graph gr) => gr a b -> Node -> Property
prop_MatchCorrectNode g n = n `gelem` g ==>
    Just n == n'
    where
        d  = fst $ n `match` g
        n' = d >>= (Just . node')

-- the context keeps the same value as the original graph
prop_MatchCorrectValue :: (Graph gr, Eq a) => gr a b -> Node -> Property
prop_MatchCorrectValue g n = n `gelem` g ==>
    v == v'
    where
        v = lab g n

        d  = fst $ n `match` g
        v' = d >>= (Just . lab')

-- the matched context keeps the same edges as the original graph
prop_MatchCorrectEdges :: (Graph gr, Eq b) => gr a b -> Node -> Property
prop_MatchCorrectEdges g n = n `gelem` g ==>
    a =~= a'
    where
        a  = lneighbors g n

        d  = fst $ n `match` g
        a' = case d of
            Just (f, _, _, t) -> f ++ t
            Nothing           -> []

-- we can collect all of the match properties into one property
prop_Match :: (Graph gr, Eq a, Eq b) => gr a b -> Node -> Property
prop_Match g n =
    conjoin $ map (\p -> p g n)
    [
        prop_MatchRemovesNode,
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
        g  = nemap fn fe (mkGraph ns es :: gr a b)
        g' = mkGraph (mapNodes fn ns) (mapEdges fe es)

-- making sure nmap performs similarly
prop_NMapModel :: forall gr a b c. (DynGraph gr, Eq c, Eq b) => gr a b -> Fun a c -> [LNode a] -> [LEdge b] -> Bool
prop_NMapModel _ (Fn (fn :: a -> c)) ns es =
    equal g g'
    where
        g  = nmap fn (mkGraph ns es :: gr a b)
        g' = mkGraph (mapNodes fn ns) es

-- making sure emap performs similarly
prop_EMapModel :: forall gr a b d. (DynGraph gr, Eq a, Eq d) => gr a b -> Fun b d -> [LNode a] -> [LEdge b] -> Bool
prop_EMapModel _ (Fn (fe :: b -> d)) ns es =
    equal g g'
    where
        g  = emap fe (mkGraph ns es :: gr a b)
        g' = mkGraph ns (mapEdges fe es)

-- repeated maps should do the same as mapping over the composition
prop_DoubleMap :: forall gr a b c d e f. (DynGraph gr, Eq e, Eq f) =>
    gr a b ->  Fun a c -> Fun c e ->
               Fun b d -> Fun d f ->
               [LNode a] -> [LEdge b] -> Bool
prop_DoubleMap _ (Fn (fn :: a -> c)) (Fn (fn' :: c -> e))
                 (Fn (fe :: b -> d)) (Fn (fe' :: d -> f))
                 ns es =
    equal g g'
    where
        g  = nemap (fn' . fn) (fe' . fe) (mkGraph ns es :: gr a b)
        g' = nemap fn' fe' $ nemap fn fe (mkGraph ns es :: gr a b)

-- converting functions from nemap-form to context maps should give the same results
-- NOTE: we cannot do this the other way around!
--       gmap has more information than nemap and cannot be "shrunk"
--       to expect the same results. for example, if the function passed to
--       gmap uses the Node indices themselves, there is no equivalent for nemap
prop_NEMapToGMap :: forall gr a b c d. (DynGraph gr, Eq c, Eq d) =>
    gr a b -> Fun a c -> Fun b d -> Bool
prop_NEMapToGMap g (Fn (fn :: a -> c)) (Fn (fe :: b -> d)) =
    equal g' g''
    where
        g'  = nemap fn fe g
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
prop_UFoldFusionWrong :: forall gr a b c. (DynGraph gr, Eq c) =>
    gr a b -> Context a b -> Fun (Context a b, c) c -> c -> Bool
prop_UFoldFusionWrong g c (Fn2 f) a =
    res == res'
    where
        res  = ufold f a (c & g)
        res' = f c (ufold f a g)


-- * Section 6: Complex Functions

-- gfiltermap with no filter should reconstruct the original graph
prop_EverythingFilter :: forall gr a b. (DynGraph gr, Eq a, Eq b) =>
    gr a b -> Bool
prop_EverythingFilter g =
    g `equal` g'
    where
        g' = gfiltermap Just g

-- gfiltermap with all-block filter gives empty
prop_NothingFilter :: forall gr a b. (DynGraph gr, Eq a, Eq b) =>
    gr a b -> Bool
prop_NothingFilter g =
    (empty :: gr a b) `equal` g'
    where
        g' = gfiltermap (const Nothing) g

-- * Section 7: Cross-Module Properties
-- we should test that multiple implementations of Graph
-- have the same results when we call various functions on them.

-- wrapper around the list type which allows for checking
-- if two lists contain the same elements
newtype Set a = Set [a]
    deriving Show

instance Eq a => Eq (Set a) where
    (==) :: Set a -> Set a -> Bool
    (Set xs) == (Set ys) = xs =~= ys

-- convert the second graph into an instance of the first
-- to compare 2 different implementations
equal' :: (Eq a, Eq b, Graph gr, Graph gr') => gr a b -> gr' a b -> Bool
equal' g g' =
    g `equal` g''
    where
        ns = labNodes g'
        es = labEdges g'
        g'' = mkGraph ns es

convert :: forall gr gr2 a b. (Graph gr, Graph gr2) => gr a b -> gr2 a b -> gr a b
convert _ g =
  mkGraph (labNodes g) (labEdges g) :: gr a b

data Equivs gr gr' a b = gr a b :?=: gr' a b deriving Show

instance (Graph gr, Graph gr', Arbitrary (gr a b), Num b) => Arbitrary (Equivs gr gr' a b) where
    arbitrary :: Gen (Equivs gr gr' a b)
    arbitrary = do
        g <- arbitrary :: Gen (gr a b)
        let ns  = labNodes g
            -- es  = labEdges g
            es  = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- POSITIVE WEIGHTS
            -- es  = map (\(a, b, x) -> (a, b, abs x)) (labEdges g) -- NEGATIVE WEIGHTS
            es'  = es ++ [(b, a, x) | (a, b, x) <- es] -- UNDIRECTED
            g'  = mkGraph ns es' :: gr a b
            g'' = mkGraph ns es' :: gr' a b
        return (g' :?=: g'')

    shrink :: Equivs gr gr' a b -> [Equivs gr gr' a b]
    shrink (g :?=: _) =
        let gs = shrink g in
            map (\j -> j :?=: convert j) gs
        where
            convert :: gr a b -> gr' a b
            convert x = mkGraph (labNodes x) (labEdges x)


prop_Equivs :: (Eq a, Eq b, Graph gr, Graph gr') => Equivs gr gr' a b -> Bool
prop_Equivs (g :?=: g') = g `equal'` g'

prop_CrossAp :: (DynGraph gr, DynGraph gr0) => Equivs gr gr0 a b -> Property
prop_CrossAp (g :?=: g') = not (isEmpty g)  ==>
    a === a'
    where
        a  = Set $ ap g
        a' = Set $ ap g'

prop_CrossBFS :: (Graph gr2, Graph gr1) => Equivs gr1 gr2 a b -> Property
prop_CrossBFS (g :?=: g') = not (isEmpty g) ==>
    b === b'
    where
        n = head $ nodes g
        b  = Set $ bfs n g
        b' = Set $ bfs n g'

prop_CrossDom :: (Graph gr2, Graph gr1) => Equivs gr1 gr2 a b -> Property
prop_CrossDom (g :?=: g') = not (isEmpty g) ==>
    d =~= d'
    where
        n = head $ nodes g
        d  = dom g n
        d' = dom g' n

prop_CrossIDom :: (Graph gr2, Graph gr1) => Equivs gr1 gr2 a b -> Property
prop_CrossIDom (g :?=: g') = not (isEmpty g) ==>
    d =~= d'
    where
        n = head $ nodes g
        d  = iDom g n
        d' = iDom g' n

prop_CrossGVDOut :: (Graph gr2, Graph gr1, Real b, Show b) => Equivs gr1 gr2 a b -> Property
prop_CrossGVDOut (g :?=: g') = not (isEmpty g) ==>
    -- whenFail
    v === v'
    where
        roots = [head $ nodes g]
        v  = Set $ gvdOut roots g
        v' = Set $ gvdOut roots g'


prop_CrossBCC :: (DynGraph gr1, DynGraph gr2, Eq (gr1 a b), Show (gr1 a b)) => Equivs gr1 gr2 a b -> Property
prop_CrossBCC (g :?=: g') = not (isEmpty g) ==>
  b === b'
  where
    b  = Set $ bcc g
    b' = Set $ map (convert g) (bcc g')


prop_CrossBFSAll :: (Graph gr2, Graph gr1) => Equivs gr1 gr2 a b -> Property
prop_CrossBFSAll (g :?=: g') = not (isEmpty g) ==>
  bs === bs'
  where
    ns = nodes g
    bs  = map (Set . flip bfs g)  ns
    bs' = map (Set . flip bfs g') ns

prop_CrossLevel :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossLevel (g :?=: g') = not (isEmpty g) ==>
  ls === ls'
  where
    ns = nodes g
    ls  = map (Set . flip level g)  ns
    ls' = map (Set . flip level g') ns

prop_CrossBFE :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossBFE (g :?=: g') = not (isEmpty g) ==>
  es === es'
  where
    ns  = nodes g
    es  = map (Set . flip bfe g)  ns
    es' = map (Set . flip bfe g') ns


prop_CrossBFT :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossBFT (g :?=: g') = not (isEmpty g) ==>
  ts === ts'
  where
    ns  = nodes g
    ts  = map (Set . flip bft g)  ns
    ts' = map (Set . flip bft g') ns

prop_CrossESP :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossESP (g :?=: g') = not (isEmpty g) ==>
  ps === ps'
  where
    ns  = nodes g
    es  = [(n, n') | n <- ns, n' <- ns]
    ps  = map (flip (uncurry esp) g)  es
    ps' = map (flip (uncurry esp) g') es

prop_CrossDFS :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossDFS (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  ds === ds'
  where
    ns' = filter (flip elem $ nodes g) ns
    ds  = Set $ dfs ns' g
    ds' = Set $ dfs ns' g'

prop_CrossDFS' :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossDFS' (g :?=: g') = not (isEmpty g) ==>
  ds === ds'
  where
    ds  = Set $ dfs' g
    ds' = Set $ dfs' g'

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


prop_CrossDFF :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossDFF (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  ds === ds'
  where
    ns' = filter (flip elem $ nodes g) ns
    ds  = LayerSet $ dff ns' g
    ds' = LayerSet $ dff ns' g'

prop_CrossUDFS :: forall gr gr1 a b. (Graph gr, Graph gr1) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossUDFS (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==> conjoin
  [
    ugdfs === g'udfs,
    gudfs === ug'dfs
  ]
  where
    ns'    = filter (flip elem $ nodes g) ns
    ug     = mkGraph (labNodes g)  ([(b, a, x) | (a, b, x) <- labEdges g] ++ labEdges g) :: gr a b
    ug'    = mkGraph (labNodes g') ([(b, a, x) | (a, b, x) <- labEdges g'] ++ labEdges g') :: gr1 a b
    ugdfs  = Set $ dfs ns' ug
    ug'dfs = Set $ dfs ns' ug'
    gudfs  = Set $ udfs ns' g
    g'udfs = Set $ udfs ns' g'

-- this test isn't actually reasonable; graphs have multiple valid topsorts
-- TODO: update this so that it checks the validity of the topsorts?
prop_CrossTS :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossTS (g :?=: g') =
  topsort g === topsort g'

prop_CrossSCC :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossSCC (g :?=: g') =
  s === s'
  where
    s  = Set $ map Set (scc g)
    s' = Set $ map Set (scc g')

prop_CrossReach :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossReach (g :?=: g') =
  rs === rs'
  where
    ns  = nodes g
    rs  = map (Set . flip reachable g) ns
    rs' = map (Set . flip reachable g') ns

prop_CrossComps :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossComps (g :?=: g') =
  cs === cs'
  where
    cs  = Set $ map Set (components g)
    cs' = Set $ map Set (components g')

prop_CrossNoComps :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossNoComps (g :?=: g') =
  noComponents g === noComponents g'

prop_CrossIsConn :: (Graph gr, Graph gr1) => Equivs gr gr1 a b -> Property
prop_CrossIsConn (g :?=: g') =
  isConnected g === isConnected g'

prop_CrossCondense :: (DynGraph gr, DynGraph gr1) => Equivs gr gr1 a b -> Property
prop_CrossCondense (g :?=: g') =
  property $ cg `equal'` cg'
  where
    cg  = nmap Set (condensation g)
    cg' = nmap Set (condensation g')

prop_CrossVoronoiSet :: (DynGraph gr, DynGraph gr1, Real b) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossVoronoiSet (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  rss === rss'
  where
    ns'  = filter (flip elem $ nodes g) ns
    v    = gvdIn ns' g
    v'   = gvdIn ns' g'
    rss  = map (Set . flip voronoiSet v) ns'
    rss' = map (Set . flip voronoiSet v') ns'

prop_CrossVoronoiSet' :: (DynGraph gr, DynGraph gr1, Real b) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossVoronoiSet' (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  rss === rss'
  where
    ns'  = filter (flip elem $ nodes g) ns
    v    = gvdOut ns' g
    v'   = gvdOut ns' g'
    rss  = map (Set . flip voronoiSet v) ns'
    rss' = map (Set . flip voronoiSet v') ns'

prop_CrossNearestNode :: (DynGraph gr, DynGraph gr1, Real b) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossNearestNode (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  nns === nns'
  where
    ns'  = filter (flip elem $ nodes g) ns
    v    = gvdOut ns' g
    v'   = gvdOut ns' g'
    nns  = map (`nearestNode` v) ns'
    nns' = map (`nearestNode` v') ns'


prop_CrossNearestDist :: (DynGraph gr, DynGraph gr1, Real b, Show b) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossNearestDist (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  nns === nns'
  where
    ns'  = filter (flip elem $ nodes g) ns
    v    = gvdOut ns' g
    v'   = gvdOut ns' g'
    nns  = map (`nearestDist` v) ns'
    nns' = map (`nearestDist` v') ns'

prop_CrossNearestPath :: (DynGraph gr, DynGraph gr1, Real b, Show b) => Equivs gr gr1 a b -> [Node] -> Property
prop_CrossNearestPath (g :?=: g') ns = not (isEmpty g) && not (null $ intersect (nodes g) ns) ==>
  nns === nns'
  where
    ns'  = filter (flip elem $ nodes g) ns
    v    = gvdOut ns' g
    v'   = gvdOut ns' g'
    nns  = map (`nearestPath` v) ns'
    nns' = map (`nearestPath` v') ns'

-- Those previous tests discard the majority of their cases
-- Let's create a new typeclass which includes a subset of the nodes
-- so that we don't need to include it as a precondition.

data NEquivs gr gr' a b = NE (gr a b) (gr' a b) [Node] deriving Show

instance (Graph gr, Graph gr', Arbitrary (gr a b), Num b) => Arbitrary (NEquivs gr gr' a b) where
    arbitrary :: Gen (NEquivs gr gr' a b)
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


prop_CrossNearestNode' :: (DynGraph gr, DynGraph gr1, Real b) => NEquivs gr gr1 a b -> Property
prop_CrossNearestNode' (NE g g' ns) = not (isEmpty g) ==>
  nns === nns'
  where
    v    = gvdOut ns g
    v'   = gvdOut ns g'
    nns  = map (`nearestNode` v)  ns
    nns' = map (`nearestNode` v') ns


prop_CrossNearestDist' :: (DynGraph gr, DynGraph gr1, Real b, Show b) => NEquivs gr gr1 a b -> Property
prop_CrossNearestDist' (NE g g' ns) = not (isEmpty g) ==>
  nns === nns'
  where
    v    = gvdOut ns g
    v'   = gvdOut ns g'
    nns  = map (`nearestDist` v)  ns
    nns' = map (`nearestDist` v') ns

prop_CrossNearestPath' :: (DynGraph gr, DynGraph gr1, Real b, Show b) => NEquivs gr gr1 a b -> Property
prop_CrossNearestPath' (NE g g' ns) = not (isEmpty g) ==>
  nns === nns'
  where
    v    = gvdOut ns g
    v'   = gvdOut ns g'
    nns  = map (`nearestPath` v)  ns
    nns' = map (`nearestPath` v') ns

prop_CrossIndep :: (DynGraph gr, DynGraph gr1) => Equivs gr gr1 a b -> Property
prop_CrossIndep (g :?=: g') = not (isEmpty g) ==> 
  is === is' 
  where 
    is  = Set $ indep g 
    is' = Set $ indep g'

prop_CrossMSTree :: (Graph gr, Graph gr1, Real b, Show b) => Equivs gr gr1 a b -> Property
prop_CrossMSTree (g :?=: g') = 
  m === m' 
  where 
    m  = msTree g 
    m' = msTree g'

prop_CrossMSPath :: (Graph gr, Graph gr1, Real b, Show b) => NEquivs gr gr1 a b -> Property
prop_CrossMSPath (NE g g' ns) = length ns >= 2 ==>  
  p === p' 
  where
    a:b:_ = ns 
    m  = msTree g 
    m' = msTree g'
    p  = msPath m  a b 
    p' = msPath m' a b

prop_CrossTRC :: (DynGraph gr, DynGraph gr1, Eq a, Eq b) => Equivs gr gr1 a b -> Property
prop_CrossTRC (g :?=: g') = 
  property $ t `equal'` t'
  where 
    t  = trc g 
    t' = trc g'

prop_CrossTC :: (DynGraph gr, DynGraph gr1, Eq a, Eq b) => Equivs gr gr1 a b -> Property
prop_CrossTC (g :?=: g') = 
  property $ t `equal'` t'
  where 
    t  = tc g 
    t' = tc g'

prop_CrossRC :: (DynGraph gr, DynGraph gr1, Eq a, Eq b) => Equivs gr gr1 a b -> Property
prop_CrossRC (g :?=: g') = 
  property $ t `equal'` t'
  where 
    t  = rc g 
    t' = rc g'



-- * Running our test suite
type G0 = Data.Graph.Inductive.Gr
type G1 = Data.Graph.Inductive.Tree.Gr
type GraphPair = Equivs G0 G1 Int Int
type NGraphPair = NEquivs G0 G1 Int Int

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs{maxSuccess=1000}

props :: [Property]
props = [
    label "prop_Equivs"            (prop_Equivs :: GraphPair -> Bool),
    label "prop_CrossAp"           (prop_CrossAp :: GraphPair -> Property),
    label "prop_CrossBFS"          (prop_CrossBFS :: GraphPair -> Property),
    label "prop_CrossDom"          (prop_CrossDom :: GraphPair -> Property),
    label "prop_CrossIDom"         (prop_CrossIDom :: GraphPair -> Property),
    label "prop_CrossGVDOut"       (prop_CrossGVDOut :: GraphPair -> Property),
    label "prop_CrossBCC"          (prop_CrossBCC :: GraphPair -> Property),
    label "prop_CrossBFSAll"       (prop_CrossBFSAll :: GraphPair -> Property),
    label "prop_CrossLevel"        (prop_CrossLevel :: GraphPair -> Property),
    label "prop_CrossBFE"          (prop_CrossBFE :: GraphPair -> Property),
    label "prop_CrossBFT"          (prop_CrossBFT :: GraphPair -> Property),
    label "prop_CrossESP"          (prop_CrossESP :: GraphPair -> Property),
    label "prop_CrossDFS"          (prop_CrossDFS :: GraphPair -> [Node] -> Property),
    label "prop_CrossDFS'"         (prop_CrossDFS'  :: GraphPair -> Property),
    label "prop_CrossDFF"          (prop_CrossDFF :: GraphPair -> [Node] -> Property),
    label "prop_CrossUDFS"         (prop_CrossUDFS :: GraphPair -> [Node] -> Property),
    label "prop_CrossTS"           (prop_CrossTS :: GraphPair -> Property),
    label "prop_CrossSCC"          (prop_CrossSCC :: GraphPair -> Property),
    label "prop_CrossReach"        (prop_CrossReach :: GraphPair -> Property),
    label "prop_CrossComps"        (prop_CrossComps :: GraphPair -> Property),
    label "prop_CrossNoComps"      (prop_CrossNoComps :: GraphPair -> Property),
    label "prop_CrossIsConn"       (prop_CrossIsConn :: GraphPair -> Property),
    label "prop_CrossCondense"     (prop_CrossCondense :: GraphPair -> Property),
    label "prop_CrossVoronoiSet"   (prop_CrossVoronoiSet :: GraphPair -> [Node] -> Property),
    label "prop_CrossVoronoiSet'"  (prop_CrossVoronoiSet' :: GraphPair -> [Node] -> Property),
    label "prop_CrossNearestNode"  (prop_CrossNearestNode :: GraphPair -> [Node] -> Property),
    label "prop_CrossNearestDist"  (prop_CrossNearestDist :: GraphPair -> [Node] -> Property),
    label "prop_CrossNearestPath"  (prop_CrossNearestPath :: GraphPair -> [Node] -> Property),
    label "prop_CrossNearestNode'" (prop_CrossNearestNode' :: NGraphPair -> Property),
    label "prop_CrossNearestDist'" (prop_CrossNearestDist' :: NGraphPair -> Property),
    label "prop_CrossNearestPath'" (prop_CrossNearestPath' :: NGraphPair -> Property),
    -- this test takes WAY too long to run for some reason
    -- label "prop_CrossIndep"        (prop_CrossIndep :: GraphPair -> Property),
    label "prop_CrossMSTree"       (prop_CrossMSTree :: GraphPair -> Property),
    -- this test doesn't work if there isn't a path between the randomly generated nodes
    -- label "prop_CrossMSPath"       (prop_CrossMSPath :: NGraphPair -> Property)
    label "prop_CrossTRC"          (prop_CrossTRC :: GraphPair -> Property),
    label "prop_CrossTC"           (prop_CrossTC :: GraphPair -> Property),
    label "prop_CrossRC"           (prop_CrossRC :: GraphPair -> Property)
    ]

suite :: IO ()
suite = do
    forM_ props qc
