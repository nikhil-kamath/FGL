{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Lib where
-- Created by Nikhil Kamath

import Test.QuickCheck
import Data.Graph.Inductive
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Arbitrary
import Data.List
import Data.Maybe
import Control.Monad (forM_)

import Util
import Types

-- * Section 7: Cross-Module Properties
-- we should test that multiple implementations of Graph
-- have the same results when we call various functions on them.

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

setup :: Testable prop => String -> prop -> Property
setup s =
  counterexample s . label s

props :: [Property]
props = [
    setup "prop_Equivs"            (prop_Equivs :: GraphPair -> Bool),
    setup "prop_CrossAp"           (prop_CrossAp :: GraphPair -> Property),
    setup "prop_CrossBFS"          (prop_CrossBFS :: GraphPair -> Property),
    setup "prop_CrossDom"          (prop_CrossDom :: GraphPair -> Property),
    setup "prop_CrossIDom"         (prop_CrossIDom :: GraphPair -> Property),
    setup "prop_CrossGVDOut"       (prop_CrossGVDOut :: GraphPair -> Property),
    setup "prop_CrossBCC"          (prop_CrossBCC :: GraphPair -> Property),
    setup "prop_CrossBFSAll"       (prop_CrossBFSAll :: GraphPair -> Property),
    setup "prop_CrossLevel"        (prop_CrossLevel :: GraphPair -> Property),
    setup "prop_CrossBFE"          (prop_CrossBFE :: GraphPair -> Property),
    setup "prop_CrossBFT"          (prop_CrossBFT :: GraphPair -> Property),
    setup "prop_CrossESP"          (prop_CrossESP :: GraphPair -> Property),
    setup "prop_CrossDFS"          (prop_CrossDFS :: GraphPair -> [Node] -> Property),
    setup "prop_CrossDFS'"         (prop_CrossDFS'  :: GraphPair -> Property),
    setup "prop_CrossDFF"          (prop_CrossDFF :: GraphPair -> [Node] -> Property),
    setup "prop_CrossUDFS"         (prop_CrossUDFS :: GraphPair -> [Node] -> Property),
    setup "prop_CrossTS"           (prop_CrossTS :: GraphPair -> Property),
    setup "prop_CrossSCC"          (prop_CrossSCC :: GraphPair -> Property),
    setup "prop_CrossReach"        (prop_CrossReach :: GraphPair -> Property),
    setup "prop_CrossComps"        (prop_CrossComps :: GraphPair -> Property),
    setup "prop_CrossNoComps"      (prop_CrossNoComps :: GraphPair -> Property),
    setup "prop_CrossIsConn"       (prop_CrossIsConn :: GraphPair -> Property),
    setup "prop_CrossCondense"     (prop_CrossCondense :: GraphPair -> Property),
    setup "prop_CrossVoronoiSet"   (prop_CrossVoronoiSet :: GraphPair -> [Node] -> Property),
    setup "prop_CrossVoronoiSet'"  (prop_CrossVoronoiSet' :: GraphPair -> [Node] -> Property),
    setup "prop_CrossNearestNode"  (prop_CrossNearestNode :: GraphPair -> [Node] -> Property),
    setup "prop_CrossNearestDist"  (prop_CrossNearestDist :: GraphPair -> [Node] -> Property),
    setup "prop_CrossNearestPath"  (prop_CrossNearestPath :: GraphPair -> [Node] -> Property),
    setup "prop_CrossNearestNode'" (prop_CrossNearestNode' :: NGraphPair -> Property),
    setup "prop_CrossNearestDist'" (prop_CrossNearestDist' :: NGraphPair -> Property),
    setup "prop_CrossNearestPath'" (prop_CrossNearestPath' :: NGraphPair -> Property),
    -- this test takes WAY too long to run for some reason
    -- setup "prop_CrossIndep"        (prop_CrossIndep :: GraphPair -> Property),
    setup "prop_CrossMSTree"       (prop_CrossMSTree :: GraphPair -> Property),
    -- this test doesn't work if there isn't a path between the randomly generated nodes
    -- setup "prop_CrossMSPath"       (prop_CrossMSPath :: NGraphPair -> Property)
    setup "prop_CrossTRC"          (prop_CrossTRC :: GraphPair -> Property),
    setup "prop_CrossTC"           (prop_CrossTC :: GraphPair -> Property),
    setup "prop_CrossRC"           (prop_CrossRC :: GraphPair -> Property)
    ]

suite :: IO ()
suite = do
    forM_ props qc
