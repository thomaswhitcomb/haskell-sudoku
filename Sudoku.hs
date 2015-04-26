module Sudoku
(solve ) where

import qualified Data.Map as Map 
import qualified Data.List as List 
import qualified Data.Char as Char 
import qualified Data.Set as Set 

--main = do
--  interact (unlines . (map solve) . lines )

unit_size :: Int
rows_in_quadrant :: Int
cols_in_quadrant :: Int

-- Support any sudoku grid with the following 3 parms
unit_size = 9
rows_in_quadrant = 3
cols_in_quadrant = 3

generate_sequence i = map Char.chr [Char.ord i..((Char.ord i) +unit_size-1) ]

col_ids = generate_sequence '1'
row_ids = generate_sequence 'a'

row_partitions :: [String]
row_partitions = partition rows_in_quadrant row_ids

col_partitions :: [String]
col_partitions = partition cols_in_quadrant col_ids

-- Divide a list into N sublists
partition :: Int  -> [b] -> [[b]]
partition _ [] = []
partition 0 _  = []
partition n l 
    | length l > n = hs : partition n ts
    | otherwise = [l]
    where (hs,ts) = splitAt n l

-- cross multiplies two strings/arrays
cross :: String -> String -> [String]
cross l1 l2 = [[x,y] | x <- l1,y <- l2]

-- List of all X and Y cooridinates in a grid
cells = cross row_ids col_ids

unitlist :: [[String]]
unitlist = 
    [cross row_ids [c] | c <- col_ids] ++
    [cross [r] col_ids | r <- row_ids] ++
    [cross rs cs | rs <- row_partitions , cs <- col_partitions ]

units :: [(String,[[String]])]
units = [ (s, [ u | u <- unitlist , elem s u ]) | s <- cells ]

peers :: Map.Map String [String]
peers = Map.fromList [ (s, filter (/= s) (List.nub (concat los))) | (s,los) <- units ]

gridstring2tuples :: String -> [(String,String)]
gridstring2tuples grid = tuples
    where tuples = Prelude.map (\(k,v) -> if v == "0" then (k,col_ids) else (k,v)) (zip cells (map (\c -> [c]) grid))

empty = Map.fromList $ map (\s -> (s,col_ids)) cells

remove_unconstrained_cells :: [[String]] -> [[String]]
remove_unconstrained_cells = map(\l -> filter (\lol -> length lol == 1) l ) 

uniq :: (Ord a) => [a] -> [a]
uniq l = Set.toList(Set.fromList l)

-- Return true if the input list contains unique items
is_uniq :: (Ord a) => [a] -> Bool
is_uniq l = length (uniq l) == length l 

query :: String -> Map.Map String String -> String
query k m = Map.findWithDefault "+++" k m 

my_peers :: String -> [String]
my_peers self = Map.findWithDefault ["+++"] self peers

-- Take a grid in string form and solve by pushing facts forward and then backtracking
solve :: String -> String
solve gridstring = grid2string backtrack_map
    where
        backtrack_map = backtrack (filter (\k -> length (query k forward_map) > 1) (Map.keys forward_map)) forward_map 
        forward_map = forward_ tuples
        tuples = gridstring2tuples gridstring
        
-- Push new assignments into the grid
forward :: String -> String
forward gridstring = grid2string $ forward_ (gridstring2tuples gridstring)

forward_ :: [(String,String)] -> Map.Map String String
forward_ tuples = foldl (\acc (k,v) -> assign acc k v) empty values
    where 
        values = filter (\(k,v) -> length v == 1) tuples
        
-- Take a list of cells with unconstained domains and Map of the grid and backtracks a solution returned in Map
backtrack :: [String] -> Map.Map String String -> Map.Map String String
backtrack [] grid 
    | (is_consistent grid) && (is_solved grid) = grid
    | otherwise = Map.empty

backtrack (cell : cells) grid 
    | is_solved grid && is_consistent grid = grid
    | is_consistent grid = 
        (foldl (\acc d -> if acc == Map.empty then backtrack cells (assign grid cell [d]) else acc) Map.empty (query cell grid) )
    | otherwise = Map.empty
    
-- Returns true if the assignment of a fact contracdicts the existing grid
conflict :: Map.Map String String -> String -> Char -> Bool
conflict grid cell domain = length hits /= length peers
    where hits = List.takeWhile (\p -> [domain] /= (query p grid )) peers
          peers = my_peers cell
-- Returns true if the characters in string one are a subset of the characters in string two
is_subset_of :: String -> String -> Bool
is_subset_of domain1 domain2 = domain1 /= domain2 && Set.isSubsetOf (Set.fromList domain1) (Set.fromList domain2) 

-- Returns the difference of two strings
difference :: String -> String -> String
difference domain1 domain2 = Set.toList (Set.difference (Set.fromList domain1) (Set.fromList domain2))

-- Reduce a cell to a fact and push that change through the grid as other cells are reduced to facts
reduce :: Map.Map String String -> String -> [String] ->  Map.Map String String
reduce grid _ [] = grid
reduce grid [domain] (peer:peers) 
    | is_subset_of [domain] peer_domain =
        reduce next_grid diff (my_peers peer)
    | otherwise = 
        reduce grid [domain] peers
      where 
        diff = difference peer_domain [domain]
        peer_domain = query peer grid
        next_grid = reduce (Map.insert peer diff grid) [domain] peers
reduce grid _ _ = grid

-- Assign a fact to the grid if it does not contradict the grid.
assign :: Map.Map String String -> String -> String -> Map.Map String String
assign grid cell [domain] 
    | not(conflict grid cell domain ) = reduce (Map.insert cell [domain] grid) [domain] (my_peers cell) 
    | otherwise = grid
    
-- turns a grid into a string for presentation
grid2string :: Map.Map String String -> String
--grid2string grid = foldl(\acc k -> acc++"("++(query k m)++")") "" cells
grid2string grid = foldl(\acc k -> acc++(query k m)) "" cells
    where m = Map.fromList tuples
          tuples = Map.toList grid

unify_unitlist :: Map.Map String String -> [[String]] -> [[String]]
unify_unitlist grid [] = []
unify_unitlist grid (unit : units) = (map (\k -> query k grid ) unit) : unify_unitlist grid units

-- Returns true if a grids items are fully constrained to single values
is_solved :: Map.Map String String -> Bool
is_solved grid = length unresolved_units == 0
    where unresolved_units = List.dropWhile (\(cell,domain)-> length domain == 1) (Map.toList grid)
    
-- Returns true if a grid does not have contradicting units
is_consistent :: Map.Map String String -> Bool
is_consistent grid = length x == length unitlist 
    where ll = unify_unitlist grid unitlist
          ls = remove_unconstrained_cells ll
          x = filter is_uniq ls
