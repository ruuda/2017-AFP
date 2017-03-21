{-# LANGUAGE KindSignatures, GADTs #-}

-- AFP Assignment 4, Marinus Oosters, 3370798	


import Control.Monad
import qualified Control.Applicative as A
import Data.IORef
import System.IO.Unsafe
import qualified Data.Map as M
import Prelude hiding (null, lookup)
import qualified Prelude as P
import Data.Maybe

--

-- |List of all the values in a Map
values :: M.Map a b -> [b]
values = map snd . M.toList

--

-- |\2.10.5 Running total


-- I think this is the "nice" way to do it using a reference.
runningTotal :: (Num a) => [a] -> IO [a]
runningTotal list = do
    total <- newIORef 0
    
    let rT []     = return []
        rT (a:as) = do modifyIORef total (+a)
                       a' <- readIORef total
                       rest <- rT as
                       return (a' : rest)
    
    rT list

-- This is the "asshole" way to do it
runningTotal' :: (Num a) => [a] -> [a]
runningTotal' = unsafePerformIO . rT
    where -- a reference
          ref = unsafePerformIO $ newIORef 0
          -- inner function using the reference
          rT []     = return []
          rT (a:as) = do modifyIORef ref (+a)
                         a' <- readIORef ref
                         rest <- rT as
                         return (a' : rest)
 

-- |\2.10.6 anything

-- It's not nice to use undefined, but it works (for its purpose in `cast'), 
-- and none of this is nice.
anything :: IORef a
anything = unsafePerformIO $ newIORef undefined

-- |\2.10.7 cast
cast :: a -> b
cast x = unsafePerformIO $ do
   writeIORef anything x
   readIORef anything

-- call this if you want a segfault (in GHC 7.10.3 at least)
segfault :: String
segfault = cast (2^128)


-- |\2.2.4 Tries
data Trie a = Node (Maybe a) (M.Map Char (Trie a)) deriving (Show)

-- |The empty trie
empty :: Trie a
empty = Node Nothing M.empty

-- |Is the trie empty?
null :: Trie a -> Bool
null (Node (Just _) _) = False
null (Node Nothing m)  = P.null m 

-- |Is the trie valid?
valid :: Trie a -> Bool
valid trie =    null trie    -- if whole trie is empty, it's valid,
             || valid' trie  -- if not empty, each subtrie must be nonempty
    where -- if empty node, subtries must be nonempty
          valid' (Node Nothing map)  = (not $ P.null map) && all valid' (values map)
          -- if nonempty node, map *may* be empty
          valid' (Node (Just _) map) = all valid' (values map)

-- |Insert a string into the trie.
insert :: String -> a -> Trie a -> Trie a
-- if at the end of the string, replace current value with `val'
insert []     val (Node _ s) = Node (Just val) s
-- otherwise, traverse and add "Nothing" nodes as needed
insert (c:cs) val (Node v s) = Node v s'
   where s' = M.insert c (insert cs val (M.findWithDefault empty c s)) s

-- |Lookup into the trie
lookup :: String -> Trie a -> Maybe a
-- if empty string, we're there; the value is already a Maybe
lookup []     (Node val _) = val
-- otherwise, look it up in the subtrie
lookup (c:cs) (Node _ st)  = M.lookup c st >>= lookup cs 


-- |Delete from a trie
delete :: String -> Trie a -> Trie a
delete []     (Node _ st)   = normalize $ Node Nothing st
delete (c:cs) n@(Node v st) | not (M.member c st) = n
                            | otherwise = normalize $ Node v n'
   where n' = M.insert c (normalize $ delete cs (st M.! c)) st

-- |Does a subtree has a value?
hasValue :: Trie a -> Bool
hasValue (Node (Just _) _) = True
hasValue (Node Nothing st) = any id $ M.map hasValue st  

-- |Normalize a subtree (make the invariant hold if it doesn't)
normalize :: Trie a -> Trie a
normalize (Node v xs) = Node v xs' 
   where xs' = M.filter hasValue (M.map normalize xs)


---- 2.2.6 ----------

data Partial a = Now a | Later (Partial a) deriving Show

runPartial :: Int -> Partial a -> Maybe a
runPartial _ (Now x)   = Just x
runPartial 0 (Later p) = Nothing
runPartial n (Later p) = runPartial (n-1) p

instance Functor Partial where fmap = liftM
instance Applicative Partial where (<*>) = ap; pure = return
instance Monad Partial where
    return        = Now
    Now x   >>= f = f x
    Later p >>= f = Later (p >>= f)

loop = Later loop
tick = Later $ Now ()

psum :: [Int] -> Partial Int
psum xs = liftM sum (mapM (\x -> tick >> return x) xs)

instance A.Alternative Partial where empty = loop; (<|>) = merge
instance MonadPlus Partial where mzero = loop; mplus = merge


merge :: Partial a -> Partial a -> Partial a
merge = unfairMerge 2 -- argument chosen to make the examples work

-- Unfair merge: if the first argument can be evaluated in N steps, return it and discard
-- the rest. 
-- this is probably cheating but I don't see how to guarantee being able to discard the rest
-- of the list another way (necessary for infinite lists)
unfairMerge :: Int -> Partial a -> Partial a -> Partial a
unfairMerge n p         _         | isJust p_rslt = Now $ fromJust p_rslt 
    where p_rslt = runPartial n p
unfairMerge n (Now x)   q         = Now x
unfairMerge n p         (Now x)   = Now x
unfairMerge n (Later p) (Later q) = Later $ unfairMerge n p q

-- Return the first evaluated sum
firstsum :: [[Int]] -> Partial Int
firstsum = foldr mplus mzero . map psum

-- returns "Just 9"
just_9 = runPartial 100 $ firstsum [repeat 1, [1,2,3], [4,5], [6,7,8], cycle [5,6]]
just_9_cycle = runPartial 200 $ firstsum $ cycle [repeat 1, [1,2,3], [4,5], [6,7,8], cycle [5,6]]

-- returns "just 1"
just_1 = runPartial 200 $ firstsum (replicate 100 (repeat 1) ++ [[1]] ++ repeat (repeat 1))

--------- 2.6.1 ----------

data Contract :: * -> * where
   Pred :: (a -> Bool) -> Contract a
   DFun :: Contract a -> (a -> Contract b) -> Contract (a -> b)
   List :: Contract a -> Contract [a]


assert :: Contract a -> a -> a
assert (Pred p)        x  = if p x then x else error "Contract violation"
assert (DFun pre post) f  = \x -> assert (post x) $ f $ assert pre x
assert (List c)        xs = map (assert c) xs


-- |Combinator expressing the old `Fun` constructor
(-->) :: Contract a -> Contract b -> Contract (a -> b)
pre --> post = DFun pre (const post)

pos :: (Num a, Ord a) => Contract a
pos = Pred (>0)

-- |Contract that always holds
true :: Contract a
true = Pred (const True)

-- Proof that this works:
--     assert true x
-- ==  assert (Pred (const True)) x         | def. of true
-- ==  if (const True) x then x else error  | def. of assert
-- ==  if True then x else error            | def. of const
-- ==  x                                    | def. of if
-- Q.E.D.

-- |Contract that checks whether an index int a list is valid.
validIndex :: Contract ([a] -> Int -> a)
validIndex = DFun true (\ls -> (Pred (\n -> n>=0 && n<length ls)) --> true)


-- |Preserves

preserves :: Eq b => (a -> b) -> Contract (a -> a)
preserves fn = DFun true (\x -> Pred (\y -> fn x == fn y))


-- preservesPos
preservesPos  = preserves (>0)
preservesPos' = pos --> pos

-- These are different, for example, this gives zero:
zero = assert preservesPos negate 0
-- whereas this gives a contract violation:
contractViolation = assert preservesPos' negate 0
-- preservesPos' mandates that the contract holds both before and after running
-- the function, preservesPos merely mandates that the function is invariant under
-- (>0).
-- This means that "assert preservesPos negate 0" returns zero, as neither 0
-- nor (negate 0) are positive so (>0) gives False both times; however 
-- "assert preservesPos' negate 0" will fail because 0 isn't positive. 

-- allPos
allPos  :: (Ord a, Num a) => Contract [a]
allPos  = List pos

allPos' :: (Ord a, Num a) => Contract [a]
allPos' = Pred (all (>0))

{--

The difference between using List and using `all` in a predicate is as follows:
`List` validates the elements of the list one by one, returning them lazily until
one is invalid, whereas `Pred . all` would process the entire list at once, requiring
all elements of the list to be valid before anything is returned.

For example:
    
     take 3 $ assert allPos [1,2,3,-4,5]
  == take 3 $ assert (List pos) [1,2,3,-4,5]
  == take 3 $ map (assert pos) [1,2,3,-4,5]
  == (assert pos 1) : take 2 $ map (assert pos) [2,3,-4,5]
  == 1 : (assert pos 2) : take 1 $ map (assert pos) [3,-4,5]
  == 1 : 2 : (assert pos 3) : take 0 $ map (assert pos) [-4,5]
  == 1 : 2 : 3 : []
  == [1,2,3]

     take 3 $ assert allPos' [1,2,3,-4,5]
  == take 3 $ assert (Pred (all (>0))) [1,2,3,-4,5]
  == take 3 $ if (all (>0) [1,2,3,-4,5]) then [1,2,3,-4,5] else error
  == error

This also means that using `List` will work on infinite lists, whereas using `Pred`
will not necessarily. 

--}
