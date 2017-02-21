module Ass1 where

import Prelude hiding (iterate, map)

{---- definitions ----}
data Tree a = Leaf a | Node (Tree a) (Tree a) deriving Show

unfoldr :: (s -> Maybe (a,s)) -> s -> [a]
unfoldr next x =
    case next x of
        Nothing     -> []
        Just (y,r)  -> y:unfoldr next r

unfoldTree :: (s -> Either a (s,s)) -> s -> Tree a
unfoldTree next x =
    case next x of
        Left y      -> Leaf y
        Right (l,r) -> Node (unfoldTree next l) (unfoldTree next r)


{---- 2.2.2 ----}


-- | \2.2.2 Iterate.
-- [x, f x, f f x, ...] using unfoldr
iterate :: (a -> a) -> a -> [a]
iterate f = unfoldr f' where f' x = Just $ (x,f x)

-- | \2.2.2 Map.
-- using unfoldr.
map :: (a -> b) -> [a] -> [b]
map f = unfoldr f'
    where f' []     = Nothing
          f' (x:xs) = Just $ (f x, xs)

-- | \2.2.2 balanced
-- Make a balanced tree of depth n.
balanced :: Int -> Tree ()
balanced = unfoldTree f
    where f 0 = Left  ()
          f n = Right (n-1,n-1)


-- | \2.2.2 Record type used for clarity of code in 'sized'
data SizeState = S { depth :: Int, label :: Int }

{-| \2.2.2 create a tree with N nodes 
   This function will create a tree with N nodes, each of which has at least
   one leaf. The last one has two leaves. -}
sized :: Int -> Tree Int
sized sz = unfoldTree f $ S {depth = sz, label = 0}
    where f :: SizeState -> Either Int (SizeState,SizeState)
          -- if depth=0, have a leaf with that label
          f S {depth = 0, label = l} = Left l
          -- if depth>0, let the next row have a leaf with that label, and
          -- a node that'll label its leaf with that label's successor
          f S {depth = n, label = l} = Right ( leaf, node )
              where leaf = S {depth = 0,      label = l}
                    node = S {depth = pred n, label = succ l}

{---- 2.2.5 ----}


-- |\2.2.5 Typeclass for consuming arguments and applying an accumulator function
class ConsumeArgs r where
    consumeArgs :: (Int -> Int) -> Int -> r

-- |\2.2.5 Base instance, when there are no arguments.
instance ConsumeArgs Int where
    consumeArgs fn acc = acc

-- |\2.2.5 Recursive instance, which eats the arguments one by one.
instance (ConsumeArgs r) => ConsumeArgs (a -> r) where
    -- The actual argument is ignored: its type must be able to be anything
    -- so nothing can ever actually be done with it.
    consumeArgs fn acc _ = consumeArgs fn (fn acc)


-- |\2.2.5 The first `count` starts at 0, and keeps acc constant
count :: ConsumeArgs r => r
count = consumeArgs (const 0) 0

-- |\2.2.5 `test` for the first count
test :: [Int]
test = [count, count 1 2 3, count "" [True, False] id (+)]

-- |\2.2.5 The second `count` starts at 0, and increments
count' :: ConsumeArgs r => r
count' = consumeArgs succ 0

-- |\2.2.5 `test` for the second count
test' :: [Int]
test' = [count', count' 1 2 3, count' "" [True, False] id (+)]

{---- 2.7.1 ----}

-- |\2.7.1 List type where the nodes are marked instead of the leaves, and each node
-- has a variable amount of children.
data PTree a = PRoot [PTree a]        -- unmarked root of the tree 
             | PNode a [PTree a]      -- node marked with an a
             | PLeaf                  -- unmarked leaf
             deriving Show

-- |\2.7.1 Generate a permutation tree for a list. List may include duplicates.
permutation_tree :: [a] -> PTree a
permutation_tree = PRoot . gentree
    where gentree [] = [PLeaf]
          gentree ls = [PNode x $ gentree ls' | (x,ls') <- withoutEach ls]
          -- for each element of the list, return it and the list without it
          withoutEach :: [a] -> [(a,[a])]
          withoutEach ls = map (`selectNth` ls) [0..length ls-1]

          -- get the Nth element from a list, and also remove it from the list
          selectNth :: Int -> [a] -> (a, [a])
          selectNth n ls = (item, before++after)
              where (before, (item:after)) = splitAt n ls


-- |\2.7.1 Prune the permutation tree, given a function.
prune :: (a -> a -> Bool) -> PTree a -> PTree a
prune _ PLeaf             = PLeaf
prune f (PRoot chld)      = PRoot (map (prune f) chld)
prune f (PNode nval chld) = PNode nval (map (prune f) (filter fn chld))
    where fn PLeaf           = True
          fn (PNode chval _) = f nval chval
          -- a root node somewhere in the middle of the tree should not happen
          fn (PRoot _)       = error "Root node inside the tree."

-- |\2.7.1 Turn a tree back into a list of lists
tree2lists :: PTree a -> [[a]]
tree2lists PLeaf              = [[]]
tree2lists (PRoot children)   = concatMap tree2lists children
tree2lists (PNode x children) = map (x:) $ concatMap tree2lists children 

-- |\2.7.1 Generate all smooth permutations of a list
smooth_perms :: Int -> [Int] -> [[Int]]
smooth_perms n = tree2lists . prune (smooth n) . permutation_tree
    where smooth :: Int -> Int -> Int -> Bool
          smooth n a b = abs (a-b) <= n

