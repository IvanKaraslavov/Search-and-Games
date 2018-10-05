-- Inf2d Assignment 1 2017-2018
-- Matriculation number: s1632798
-- {-# OPTIONS -Wall #-}


module Inf2d1 where

import Data.List (sortBy, nub)
import Debug.Trace
import ConnectFour

gridLength_search::Int
gridLength_search = 6
gridWidth_search :: Int
gridWidth_search = 6

{- NOTES:

-- DO NOT CHANGE THE NAMES OR TYPE DEFINITIONS OF THE FUNCTIONS!
You can write new auxillary functions, but don't change the names or type definitions
of the functions which you are asked to implement.

-- Comment your code.

-- You should submit this file, and only this file, when you have finished the assignment.

-- The deadline is the 3pm Tuesday 13th March 2018.

-- See the assignment sheet and document files for more information on the predefined game functions.

-- See the README for description of a user interface to test your code.

-- See www.haskell.org for haskell revision.

-- Useful haskell topics, which you should revise:
-- Recursion
-- The Maybe monad
-- Higher-order functions
-- List processing functions: map, fold, filter, sortBy ...

-- See Russell and Norvig Chapters 3 for search algorithms,
-- and Chapter 5 for game search algorithms.

-}

-- Section 1: Uniform Search

-- 6 x 6 grid search states

-- The Node type defines the position of the robot on the grid.
-- The Branch type synonym defines the branch of search through the grid.
type Node = (Int,Int)
type Branch = [(Int,Int)]


-- The next function should return all the possible continuations of input search branch through the grid.
-- Remember that the robot can only move up, down, left and right, and can't move outside the grid.
-- The current location of the robot is the head of the input branch.
-- Your function should return an empty list if the input search branch is empty.
-- This implementation of next function does not backtrace branches.

next::Branch-> [Branch]
next branch
     | branch == [] = []
     | otherwise = concat [[branch ++ [(x - 1, y)]|x - 1 > 0, allDifferent (branch ++ [(x - 1, y)])],
        [branch ++ [(x + 1, y)] |x + 1 <= gridWidth_search, allDifferent (branch ++ [(x + 1, y)])],
        [branch ++ [(x, y - 1)] |y - 1 > 0, allDifferent (branch ++ [(x, y - 1)])],
        [branch ++ [(x, y + 1)] |y + 1 <= gridLength_search, allDifferent (branch ++ [(x, y + 1)])]]
        where (x,y) = last branch

-- |The checkArrival function should return true if the current location of the robot is the destination, and false otherwise.
checkArrival::Node-> Node-> Bool
checkArrival (d1,d2) (c1,c2) = d1 == c1 && d2 == c2

-- Section 3 Uniformed Search
-- | Breadth-First Search
-- The breadthFirstSearch function should use the next function to expand a node,
-- and the checkArrival function to check whether a node is a destination position.
-- The function should search nodes using a breadth first search order.

breadthFirstSearch::Node-> (Branch-> [Branch])-> [Branch]->[Node]-> Maybe Branch
breadthFirstSearch destination next [] exploredList = Nothing
breadthFirstSearch destination next (b:bs) exploredList =
    if checkArrival destination(last b)
        then Just b
    else do
        if (not ((last b) `elem` exploredList))
            then do
            -- first expands the old nodes before the new ones
            breadthFirstSearch destination next (bs ++ next b) (exploredList ++ [(last b)])
        else do
            breadthFirstSearch destination next bs exploredList


-- | Depth-First Search
-- The depthFirstSearch function is similiar to the breadthFirstSearch function,
-- except it searches nodes in a depth first search order.

depthFirstSearch::Node-> (Branch-> [Branch])-> [Branch]-> [Node]-> Maybe Branch
depthFirstSearch destination next  [] exploredList = Nothing
depthFirstSearch destination next (d:ds) exploredList =
        if checkArrival destination(last d)
            then Just d
        else do
            if (not ((last d) `elem` exploredList))
                then do
                -- first expands the new nodes before the old ones
                depthFirstSearch destination next ((next d) ++ ds) (exploredList ++ [(last d)])
            else do
                depthFirstSearch destination next ds exploredList

-- | Depth-Limited Search
-- The depthLimitedSearch function is similiar to the depthFirstSearch function,
-- except its search is limited to a pre-determined depth, d, in the search tree..

depthLimitedSearch::Node-> (Branch-> [Branch])-> [Branch]-> Int-> [Node]-> Maybe Branch
depthLimitedSearch destination next [] n exploredList = Nothing
depthLimitedSearch destination next (d:ds) n exploredList  =
        if checkArrival destination(last d)
            then Just d
        else do
            if (length d) <= n
                then do
                -- first expands the new nodes before the old ones
                depthLimitedSearch destination next ((next d) ++ ds) n []
            else do
                depthLimitedSearch destination next ds n []


-- | Iterative-deepening search
-- The iterDeepSearch function should initially search nodes using depth-first to depth d,
-- and should increase the depth by d if search is unsuccessful.
-- This process should be continued until a solution is found.
-- Each time a solution is not found, the depth should be increased.

iterDeepSearch:: Node-> (Branch-> [Branch])-> Node-> Int-> Maybe Branch
iterDeepSearch destination next initialNode d
    | depthLimitedSearch destination next  [[initialNode]] d [] == Nothing = iterDeepSearch destination next initialNode (d+1)
    | otherwise = depthLimitedSearch destination next  [[initialNode]] d []

-- | Section 4: Informed search

-- Manhattan distance heuristic
-- This function should return the manhattan distance between the current position and the destination position.
manhattan::Node-> Node-> Int
manhattan (p1,p2) (d1,d2) = abs(p1 - d1) + abs(p2 - d2)

-- | Best-First Search
-- The bestFirstSearch function uses the checkArrival function to check whether a node is a destination position,
-- and the heuristic function (of type Node->Int) to determine the order in which nodes are searched.
-- Nodes with a lower heuristic value should be searched before nodes with a higher heuristic value.
bestFirstSearch:: Node-> (Branch-> [Branch])-> (Node->Int)-> [Branch]-> [Node]-> Maybe Branch
bestFirstSearch destination next heuristic [] exploredList = Nothing
bestFirstSearch destination next heuristic (d:ds) exploredList =
        if checkArrival destination(last d)
            then Just d
        else do
            if (not ((last d) `elem` exploredList))
                then do
                -- sorting the nodes by their manhattan distance
                bestFirstSearch destination next (manhattan destination) (sortBy (sortHeuristic manhattan destination)[ x | x <- (ds ++ next d)])(exploredList ++ [(last d)])
            else do
                bestFirstSearch destination next (manhattan destination)(sortBy (sortHeuristic manhattan destination)[ x | x <- (ds ++ next d)]) exploredList


-- | A* Search
-- The aStarSearch function is similar to the bestFirstSearch function
-- except it includes the cost of getting to the state when determining the value of the node.

aStarSearch:: Node-> (Branch-> [Branch])-> (Node->Int)-> (Branch-> Int)-> [Branch]-> [Node]-> Maybe Branch
aStarSearch destination next heuristic cost [] exploredList = Nothing
aStarSearch destination next heuristic cost (d:ds) exploredList =
        if checkArrival destination(last d)
            then Just d
        else do
            if (not ((last d) `elem` exploredList))
                then do
                -- sorting the nodes by their manhattan distance + their cost so far
                aStarSearch destination next (manhattan destination) cost (sortBy (sortAStar manhattan destination)[ x | x <- (ds ++ next d)])(exploredList ++ [(last d)])
            else do
                aStarSearch destination next (manhattan destination) cost (sortBy (sortAStar manhattan destination)[ x | x <- (ds ++ next d)]) exploredList


-- | The cost function calculates the current cost of a trace, where each movement from one state to another has a cost of 1.
cost :: Branch-> Int
cost branch = (length branch)

-- In this section, the function determines the score of a terminal state, assigning it a value of +1, -1 or 0:
eval :: Game-> Int
eval game =
    if terminal game
        then if checkWin game maxPlayer
            then 1
        else if checkWin game minPlayer
            then (-1)
        else 0
    else 0


-- | The minimax function should return the minimax value of the state (without alphabeta pruning).
-- The eval function should be used to get the value of a terminal state.

minimax:: Role-> Game-> Int
minimax player game =
    if terminal game
        then eval game
    else if player == maxPlayer
        then maximum([minimax (switch player) g | g <- (moves game player)])
    else
        minimum ([minimax (switch player) g | g <- (moves game player)])


-- | The alphabeta function should return the minimax value using alphabeta pruning.
-- The eval function should be used to get the value of a terminal state.

alphabeta:: Role-> Game-> Int
alphabeta player game | player == maxPlayer = maxValue player game (-2,2)
                      | otherwise           = minValue player game (-2,2)
    where maxValue player game (alpha,beta) | terminal game = eval game
                                         | otherwise  = snd $ foldr (\game' (alpha',v) ->
                                            let newV = max v (minValue (switch player) game' (alpha',beta)) in
                                            if v >= beta
                                            then (alpha',v) -- If a state with an evaluation higher than beta has been found, we don't bother
                                            -- checking any further nodes on this branch.
                                            else (max alpha' newV, newV)) -- If not, we calculate the new alpha and v values.
                                        (alpha,-2) (moves game player)
          minValue player game (alpha,beta) | terminal game = eval game
                                         | otherwise  = snd $ foldr (\game' (beta',v) ->
                                            let newV = min v (maxValue (switch player) game' (alpha,beta')) in
                                            if v <= alpha
                                            then (beta',v) -- If a state with an evaluation lower than alpha has been found, ignore the rest of
                                            -- the nodes on this branch.
                                            else (min beta' newV, newV)) -- If not, calculate the new beta and v values.
                                         (beta,2) (moves game player)



{- Auxiliary Functions
-- Include any auxiliary functions you need for your algorithms below.
-- For each function, state its purpose and comment adequately.
-- Functions which increase the complexity of the algorithm will not get additional scores
-}
-- check if all the nodes in a branch are different
allDifferent :: (Eq a) => [a] -> Bool
allDifferent []     = True
allDifferent (xs) = (last xs) `notElem` (init xs)

-- a helper function for expanding the branch with nodes which are not in the exploredList
nextWithoutInExplored:: [Branch] -> [Node] -> [Branch]
nextWithoutInExplored nextList exploredList = filter (not . null)[if (last d) `elem` exploredList then [] else d| d <- nextList]

-- a helper function for sorting using a heuristic function
sortHeuristic::(Node-> Node-> Int) -> Node -> Branch -> Branch -> Ordering
sortHeuristic heuristic destination branch1 branch2
    | (heuristic destination (last branch1)) < (heuristic destination (last branch2)) = LT
    | otherwise = GT

-- a helper function for sorting using a heuristic function and cost function
sortAStar::(Node-> Node-> Int) -> Node -> Branch -> Branch -> Ordering
sortAStar heuristic destination branch1 branch2
    | ((heuristic destination (last branch1)) + cost branch1) < ((heuristic destination (last branch2)) + cost branch2) = LT
    | otherwise = GT