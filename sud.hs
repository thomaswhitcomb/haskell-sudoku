import qualified Data.Map as Map 
import qualified Data.List as List 
import qualified Data.Char as Char 
import qualified Data.Set as Set 
import qualified Debug.Trace as Trace

trace :: String -> a ->a
--trace s f = Trace.trace s f
trace s f = f

unit_size :: Int
rows_in_quadrant :: Int
cols_in_quadrant :: Int

-- Support any sudoku grid with the following 3 parms
unit_size = 9
rows_in_quadrant = 3
cols_in_quadrant = 3

col_ids = take unit_size "123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
row_ids = take unit_size "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghi"

row_partitions :: [[Char]]
row_partitions = partition rows_in_quadrant row_ids

col_partitions :: [[Char]]
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
cross :: String -> String -> [[Char]]
cross l1 l2 = [[x,y] | x <- l1,y <- l2]

-- List of all X and Y cooridinates in a grid
cells = cross row_ids col_ids

unitlist :: [[[Char]]]
unitlist = 
    [cross row_ids [c] | c <- col_ids] ++
    [cross [r] col_ids | r <- row_ids] ++
    [cross rs cs | rs <- row_partitions , cs <- col_partitions ]

units :: [([Char],[[[Char]]])]
units = [ (s, [ u | u <- unitlist , elem s u ]) | s <- cells ]

peers :: Map.Map [Char] [[Char]]
peers = Map.fromList [ (s, filter (/= s) (List.nub (concat los))) | (s,los) <- units ]

gridstring2tuples :: [Char] -> [([Char],[Char])]
gridstring2tuples grid = tuples
    where tuples = Prelude.map (\(k,v) -> if v == "0" then (k,col_ids) else (k,v)) (zip cells (map (\c -> [c]) grid))

empty = Map.fromList $ map (\s -> (s,col_ids)) cells

remove_unconstrained_cells :: [[[Char]]] -> [[[Char]]]
remove_unconstrained_cells = map(\l -> filter (\lol -> length lol == 1) l ) 

uniq :: (Ord a) => [a] -> [a]
uniq l = Set.toList(Set.fromList l)

-- Return true if the input list contains unique items
is_uniq :: (Ord a) => [a] -> Bool
is_uniq l = length (uniq l) == length l 

query :: [Char] -> Map.Map [Char] [Char] -> [Char]
query k m = Map.findWithDefault "+++" k m 

my_peers :: [Char] -> [[Char]]
my_peers self = Map.findWithDefault ["+++"] self peers

-- Take a grid in string form and solve by pushing facts forward and then backtracking
solve :: [Char] -> [Char]
solve gridstring = grid2string backtrack_map
    where
        backtrack_map = backtrack (filter (\k -> length (query k forward_map) > 1) (Map.keys forward_map)) forward_map 
        forward_map = forward_ tuples
        tuples = gridstring2tuples gridstring
        
-- Push new assignments into the grid
forward :: [Char] -> [Char]
forward gridstring = grid2string $ forward_ (gridstring2tuples gridstring)

forward_ :: [([Char],[Char])] -> Map.Map [Char] [Char]
forward_ tuples = foldl (\acc (k,v) -> assign acc k v) empty values
    where 
        values = filter (\(k,v) -> length v == 1) tuples
        
-- Take a list of cells with unconstained domains and Map of the grid and backtracks a solution returned in Map
backtrack :: [[Char]] -> Map.Map [Char] [Char] -> Map.Map [Char] [Char]
backtrack [] grid 
    | (is_consistent grid) && (is_solved grid) = grid
    | otherwise = trace("pop end")(Map.empty)

backtrack (cell : cells) grid 
    | is_solved grid && is_consistent grid = grid
    | is_consistent grid = 
        trace("next: "++show(grid2string grid)) 
        (foldl (\acc d -> if acc == Map.empty then backtrack cells (assign grid cell [d]) else acc) Map.empty (query cell grid) )
    | otherwise = trace("inconsistent: "++show(grid2string grid))(Map.empty)
    
-- Returns true if the assignment of a fact contracdicts the existing grid
conflict :: Map.Map [Char] [Char] -> [Char] -> Char -> Bool
conflict grid cell domain = length hits /= length peers
    where hits = List.takeWhile (\p -> [domain] /= (query p grid )) peers
          peers = my_peers cell
-- Returns true if the characters in string one are a subset of the characters in string two
is_subset_of :: [Char] -> [Char] -> Bool
is_subset_of domain1 domain2 = domain1 /= domain2 && Set.isSubsetOf (Set.fromList domain1) (Set.fromList domain2) 

-- Returns the difference of two strings
difference :: [Char] -> [Char] -> [Char]
difference domain1 domain2 = Set.toList (Set.difference (Set.fromList domain1) (Set.fromList domain2))

-- Reduce a cell to a fact and push that change through the grid as other cells are reduced to facts
reduce :: Map.Map [Char] [Char] -> [Char] -> [[Char]] ->  Map.Map [Char] [Char]
reduce grid _ [] = grid
reduce grid [domain] (peer:peers) 
    | is_subset_of [domain] peer_domain =
        trace ("reducing "++peer++" by "++[domain]++" from "++peer_domain++" to "++diff) (reduce next_grid diff (my_peers peer))
    | otherwise = 
        reduce grid [domain] peers
      where 
        diff = difference peer_domain [domain]
        peer_domain = query peer grid
        next_grid = reduce (Map.insert peer diff grid) [domain] peers
reduce grid _ _ = grid

-- Assign a fact to the grid if it does not contradict the grid.
assign :: Map.Map [Char] [Char] -> [Char] -> [Char] -> Map.Map [Char] [Char]
assign grid cell [domain] 
    | not(conflict grid cell domain ) = reduce (Map.insert cell [domain] grid) [domain] (my_peers cell) 
    | otherwise = grid
    
-- turns a grid into a string for presentation
grid2string :: Map.Map [Char][Char] -> [Char]
grid2string grid = foldl(\acc k -> acc++"("++(query k m)++")") "" cells
    where m = Map.fromList tuples
          tuples = Map.toList grid


unify_unitlist :: Map.Map [Char] [Char] -> [[[Char]]] -> [[[Char]]]
unify_unitlist grid [] = []
unify_unitlist grid (unit : units) = (map (\k -> query k grid ) unit) : unify_unitlist grid units

-- Returns true if a grids items are fully constrained to single values
is_solved :: Map.Map [Char] [Char] -> Bool
is_solved grid = length unresolved_units == 0
    where unresolved_units = List.dropWhile (\(cell,domain)-> length domain == 1) (Map.toList grid)
    
-- Returns true if a grid does not have contradicting units
is_consistent :: Map.Map [Char] [Char] -> Bool
is_consistent grid = length x == length unitlist 
    where ll = unify_unitlist grid unitlist
          ls = remove_unconstrained_cells ll
          x = filter is_uniq ls
  
test9 = [
    forward "003010002850649700070002000016080070204701609030020810000500020009273086300060900"  == "(4)(9)(3)(8)(1)(7)(5)(6)(2)(8)(5)(2)(6)(4)(9)(7)(3)(1)(6)(7)(1)(3)(5)(2)(4)(9)(8)(9)(1)(6)(4)(8)(5)(2)(7)(3)(2)(8)(4)(7)(3)(1)(6)(5)(9)(7)(3)(5)(9)(2)(6)(8)(1)(4)(1)(6)(8)(5)(9)(4)(3)(2)(7)(5)(4)(9)(2)(7)(3)(1)(8)(6)(3)(2)(7)(1)(6)(8)(9)(4)(5)",
    forward "920705003600000080004600000006080120040301070071060500000004800010000002400902061" == "(9)(2)(8)(7)(4)(5)(6)(1)(3)(6)(5)(7)(2)(1)(3)(4)(8)(9)(1)(3)(4)(6)(9)(8)(2)(5)(7)(3)(9)(6)(5)(8)(7)(1)(2)(4)(8)(4)(5)(3)(2)(1)(9)(7)(6)(2)(7)(1)(4)(6)(9)(5)(3)(8)(7)(6)(2)(1)(3)(4)(8)(9)(5)(5)(1)(9)(8)(7)(6)(3)(4)(2)(4)(8)(3)(9)(5)(2)(7)(6)(1)",
    solve "900705003600000080004600000006080120040301070071060500000004800010000002400902001" == "(9)(2)(8)(7)(4)(5)(6)(1)(3)(6)(5)(7)(2)(1)(3)(4)(8)(9)(1)(3)(4)(6)(9)(8)(2)(5)(7)(3)(9)(6)(5)(8)(7)(1)(2)(4)(8)(4)(5)(3)(2)(1)(9)(7)(6)(2)(7)(1)(4)(6)(9)(5)(3)(8)(7)(6)(2)(1)(3)(4)(8)(9)(5)(5)(1)(9)(8)(7)(6)(3)(4)(2)(4)(8)(3)(9)(5)(2)(7)(6)(1)",
    solve "020007000609000008000950200035000070407000809080000120001034000700000602000100030" == "(1)(2)(8)(4)(6)(7)(3)(9)(5)(6)(5)(9)(3)(1)(2)(7)(4)(8)(3)(7)(4)(9)(5)(8)(2)(6)(1)(2)(3)(5)(8)(9)(1)(4)(7)(6)(4)(1)(7)(6)(2)(3)(8)(5)(9)(9)(8)(6)(7)(4)(5)(1)(2)(3)(5)(6)(1)(2)(3)(4)(9)(8)(7)(7)(4)(3)(5)(8)(9)(6)(1)(2)(8)(9)(2)(1)(7)(6)(5)(3)(4)",
    solve "600000084003060000001000502100074000720906035000320008305000200000050900240000007" == "(6)(5)(2)(7)(1)(9)(3)(8)(4)(4)(8)(3)(2)(6)(5)(7)(9)(1)(9)(7)(1)(4)(3)(8)(5)(6)(2)(1)(3)(8)(5)(7)(4)(6)(2)(9)(7)(2)(4)(9)(8)(6)(1)(3)(5)(5)(6)(9)(3)(2)(1)(4)(7)(8)(3)(9)(5)(8)(4)(7)(2)(1)(6)(8)(1)(7)(6)(5)(2)(9)(4)(3)(2)(4)(6)(1)(9)(3)(8)(5)(7)",
    solve "000000000000000000000000000000000000000000000000000000000000000000000000000000000" == "(1)(2)(3)(4)(5)(6)(7)(8)(9)(4)(5)(6)(7)(8)(9)(1)(2)(3)(7)(8)(9)(1)(2)(3)(4)(5)(6)(2)(1)(4)(3)(6)(5)(8)(9)(7)(3)(6)(5)(8)(9)(7)(2)(1)(4)(8)(9)(7)(2)(1)(4)(3)(6)(5)(5)(3)(1)(6)(4)(2)(9)(7)(8)(6)(4)(2)(9)(7)(8)(5)(3)(1)(9)(7)(8)(5)(3)(1)(6)(4)(2)",
    solve "100007090030020008009600500005300900010080002600004000300000010040000007007000300" == "(1)(6)(2)(8)(5)(7)(4)(9)(3)(5)(3)(4)(1)(2)(9)(6)(7)(8)(7)(8)(9)(6)(4)(3)(5)(2)(1)(4)(7)(5)(3)(1)(2)(9)(8)(6)(9)(1)(3)(5)(8)(6)(7)(4)(2)(6)(2)(8)(7)(9)(4)(1)(3)(5)(3)(5)(6)(4)(7)(8)(2)(1)(9)(2)(4)(1)(9)(3)(5)(8)(6)(7)(8)(9)(7)(2)(6)(1)(3)(5)(4)"
    ]

