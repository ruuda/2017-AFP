{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, FunctionalDependencies #-}

-- Assignment 2, Marinus Oosters, 3370798

-- For the Monad exercise, part of it is to choose what to export,
-- however I also need to export everything else pertaining to the other
-- exercises so they can be tested, therefore this section is a bit of a
-- mess.

module Ass2 (
   -- 2.2.8
   GP (..), run, gp_fn, addGP, accumGP, simulate, addM, accumM,
    
   -- 2.2.9
   stop, add, mul, binf, store, start, p1, p2, p3,
   stop', add', mul', binf', store', start', p1', p2', -- no p3', it would be rejected
   emptyL, pushL, peekL, binfL,

   -- 2.3 ----------
      -- This is the one for which it matters, so I've also explained why
      
      module Control.Monad.State, -- the user will want to have get, put etc
      annotate, diagnostics,      -- functions for annotation
      loadState, saveState,       -- functions for state history
      runStateMonadPlus,          -- to actually run the state monad

      -- The user should not need anything else, as they are implementation
      -- details. E.g., the history stack is currently just a list, but the
      -- user doesn't need to know. The constructor function `runSMP`'s type
      -- does rely on the fact that the history is a list and the annotations
      -- are a map, so if this were exported, those things could not be changed
      -- in possible later versions. If you are writing a library that's
      -- important. Similarly, `addAnn` and `showAnn` give implementation
      -- details.

      -- What follows should NOT be exported normally, but for ease of testing:
      -- here are the given examples, predefined so you can run them,
      diag1, diag2, history,
      -- and here are some QuickCheck properties that I've defined
      prop_Put, prop_Get, prop_LoadEmptyFails, prop_StoreLoad,
       

   -- 3.3.X, foldable --
   Rose (..), foldMap, fsum, fproduct
      
      
) where


import Control.Monad.State
import Prelude hiding (foldMap)
import qualified Data.Map.Lazy as Map
import Data.List



{---- 2.2.8 ----}
-- |a GP program
data GP a = End a
          | Get (Int -> GP a)
          | Put Int (GP a)

-- |run a GP program
run :: GP a -> IO a
run (End a)   = return a
run (Get f)   = putStr "? " >> getLine >>= run . f . read
run (Put i p) = putStrLn (show i) >> run p
 
-- |construct a GP program applying a function to two integers
gp_fn :: (Int -> Int -> Int) -> GP ()
gp_fn f = Get (\a -> 
          Get (\b -> 
          Put (f a b) 
          (End ())))

-- |addition
addGP :: GP ()
addGP = gp_fn (+)


-- |accumulate, expressed using the constructors
accumGP :: GP a
accumGP = acc' 0
    where 
    acc' a =  Get (\n -> 
               if n==0 
                then (Put a $ acc' a)
                else acc' (a+n))


-- |simulate a GP program using a possibly infinite list
simulate :: GP a -> [Int] -> (a, [Int])
simulate (End a)   _      = (a, [])
simulate (Get f)   []     = error "Out of input"
simulate (Get f)   (x:xs) = simulate (f x) xs
simulate (Put i p) xs     = (a, i:out)
    where (a, out) = simulate p xs


instance Functor GP where
    fmap f (End x)   = End (f x)
    fmap f (Get g)   = Get (fmap f . g)
    fmap f (Put n x) = Put n (fmap f x)

instance Applicative GP where pure = return; (<*>) = ap

instance Monad GP where
    return a        = End a

    (End a)   >>= f = f a
    (Get g)   >>= f = Get (\n -> g n >>= f)
    (Put i p) >>= f = Put i (p >>= f)

instance MonadState Int GP where
    get   = Get (\x -> End x) 
    put i = Put i (End ())

-- the two functions defined using the monad, hopefully proving my definitions
-- "reasonable"

-- |Add two numbers, expressed using the monad
addM :: GP ()
addM = do 
    x <- get
    y <- get
    put (x+y)
    return ()

-- |Accumulate, expressed using the monad
accumM :: GP ()
accumM = acc' 0 
    where acc' a = 
            do 
               n <- get
               if n==0
                  then put a >> acc' a
                  else acc' (a+n)



-- The question also asked me to say what the difference is. The normal State
-- monad only stores one state, which can be set using `put` and retrieved
-- using `get`. In this monad, `get` instead consumes an item from the input
-- list, while `put` appends an item to the output list. 
-------------------
    
{---- 2.2.9 ----}

-- I've not quite gotten the syntax correct without typeclasses. Therefore, this
-- one uses continuation-passing style and requires an `$` in between the operations.

-- (`start` would need to be variadic, which I don't know how to do without typeclasses).

-- I have provided two implementations, one which fails at runtime
-- and one which rejects wrong programs using typechecking.


-- |Stack continuation
type StackCont a = [a] -> a

-- |Stop: returns the value
stop :: StackCont a
stop (x:_) = x

-- |binf: apply a binary function to the top two values of the stack
binf :: (a -> a -> a) -> StackCont a -> StackCont a
binf f k (x:y:stack) = k $ f x y:stack

-- |Add: add the top two values of the stack
add :: Num a => StackCont a -> StackCont a
add = binf (+)

-- |Mul: multiply the top two values of the stack
mul = binf (*)

-- |Store: push a value to the stack
store :: a -> StackCont a -> StackCont a
store n k stack = k $ n:stack

-- |Start: initialize with an empty stack.
start :: StackCont a -> a
start k = k []
 

-- |p1, example 1.
p1 :: Int
p1 = start $ store 3 $ store 5 $ add $ stop
-- |p2, example 2.
p2 :: Int
p2 = start $ store 3 $ store 6 $ store 2 $ mul $ add $ stop
-- |p3, example 3. Fails at runtime.
p3 :: Int
p3 = start $ store 2 $ add $ stop




-- |Peano numbers can be used to have the type system keep track of the stack. 
data Zero
data Succ a

-- This can probably be done by storing the actual values in the types, but this works.

-- |A type-bounded stack
type TypeStack a n = ([a], n) 

-- |A type-bounded stack with at least one value
type TypeStack1 a n = TypeStack a (Succ n)

-- |A type-bounded stack with at least two values
type TypeStack2 a n = TypeStack a (Succ (Succ n))

-- |The empty type-bounded stack
emptyL :: TypeStack a Zero
emptyL = ([], undefined)

-- |Push onto the type-bounded stack
pushL :: a -> TypeStack a n -> TypeStack1 a n
pushL a (as, _) = (a:as, undefined)

-- |Peek at the type-bounded stack
peekL :: TypeStack1 a n -> a
peekL (a, _) = head a

-- |Pop two numbers from the type-bounded stack, apply a binary function, and push the result
binfL :: (a -> a -> a) -> TypeStack2 a n -> TypeStack1 a n
binfL f ((a:b:as), _) = (f a b:as, undefined)
 

-- |Stack continuation with type-bounded stack
type StackCont' a n = ([a], n) -> a

-- |Stack continuation with type-bounded stack and at least one value
type StackCont1' a n = StackCont' a (Succ n)

-- |Stack continuation with type-bounded stack and at least two values
type StackCont2' a n = StackCont' a (Succ (Succ n)) 

-- |stop': return the topmost value; stack must have a value on it
stop' :: StackCont1' a n 
stop' x = peekL x

-- |binf': apply a function to the topmost two values
binf' :: (a -> a -> a) -> StackCont1' a n -> StackCont2' a n 
binf' f k stack = k $ binfL f stack

-- |add': sum the topmost two values
add' :: Num a => StackCont1' a n -> StackCont2' a n
add' = binf' (+)

-- |mul': multiply the topmost two values
mul' :: Num a => StackCont1' a n -> StackCont2' a n
mul' = binf' (*)

-- |store': push a value to the stack
store' :: a -> StackCont1' a n -> StackCont' a n 
store' a k stack = k $ pushL a stack

-- |start': start out with the empty stack
start' :: StackCont' a Zero -> a
start' k = k emptyL

-- |p1': the first example implemented using the typed stack
p1' :: Int
p1' = start' $ store' 3 $ store' 5 $ add' $ stop'

-- |p2': the second example implemented using the typed stack
p2' :: Int
p2' = start' $ store' 3 $ store' 6 $ store' 2 $ mul' $ add' $ stop'

-- p3' would be rejected at compile time if uncommented.
{-
p3' :: Int
p3' = start' $ store' 2 $ add' $ stop'
-- -}


{---- 2.3 ----}

type Ann = Map.Map String Int -- use a map for annotations

-- |add an annotation
addAnn :: String -> Ann -> Ann
addAnn str = Map.insertWith (+) str 1

-- |show the annotations as a string in the required format
showAnn :: Ann -> String
showAnn ann = 
    "[" ++ intercalate ", " [s++"="++show v | (s,v) <- Map.toList ann] ++ "]"

newtype StateMonadPlus s a = 
    StateMonadPlus { runSMP :: s -> [s] -> Ann -> Either String (a, s, [s], Ann) }

instance Functor (StateMonadPlus s) where fmap = liftM
instance Applicative (StateMonadPlus s) where pure = return; (<*>) = ap

instance Monad (StateMonadPlus s) where
    -- return a fixed value
    return a = annotate "return" $ StateMonadPlus $ \s hist ann -> Right (a, s, hist, ann)  
 
    -- fail with a given message
    fail msg = annotate "fail" $ StateMonadPlus $ \_ _ _ -> Left msg

    -- bind
    (StateMonadPlus m) >>= f = annotate "bind" $ StateMonadPlus m'
        where m' s h ann = case m s h ann of
                            (Left msg) -> Left msg        -- failure
                            (Right (a, s', h', ann')) ->  -- success
                                let (StateMonadPlus g) = f a
                                in  g s' h' ann'

instance MonadState s (StateMonadPlus s) where
    get   = annotate "get" $ StateMonadPlus $ \s h ann -> Right (s,s,h,ann)
    put s = annotate "put" $ StateMonadPlus $ \_ h ann -> Right ((),s,h,ann)

-- |StoreState: save and load states
class MonadState s m => StoreState s m | m -> s where
    saveState :: m ()
    loadState :: m ()

-- |StoreState instance for 
instance StoreState s (StateMonadPlus s) where
    -- |save the state by pushing it onto the history list
    saveState = annotate "saveState" $ StateMonadPlus m
        where m s h ann = Right ((), s, s:h, ann)
 
    -- |load the state by popping from the list, fail if empty
    loadState = annotate "loadState" $ StateMonadPlus m
        where -- empty history list: fail
              m _ []    _   = Left "empty state stack" 
              -- nonempty history list: its first item is the new state
              m _ (s:h) ann = Right ((), s, h, ann)

-- |Run a StateMonadPlus.
runStateMonadPlus :: StateMonadPlus s a -> s -> Either String (a,s)
runStateMonadPlus m s = 
    case runSMP m s [] Map.empty of
       (Left msg)        -> Left msg
       (Right (a,s,_,_)) -> Right (a,s)
     

-- |Annotate a computation.
annotate :: String -> StateMonadPlus s a -> StateMonadPlus s a
annotate ann (StateMonadPlus m) = 
    StateMonadPlus $ \s h ann' -> m s h $ addAnn ann ann'
 

-- |Get a string describing the annotations on all previous computations.
diagnostics :: StateMonadPlus s String
diagnostics = StateMonadPlus m
   where m s h ann = let ann' = addAnn "diagnostics" ann 
                     in  Right (showAnn ann', s, h, ann')



-- |Diagnostic example 1
diag1, diag2 :: StateMonadPlus a String
diag1 = do return 3 >> return 4
           return 5
           diagnostics

-- |Diagnostic example 2
diag2 = do annotate "A" (return 3 >> return 4)
           return 5
           diagnostics



-- |History example
history :: StateMonadPlus Int (Int,Int,Int,Int,Int)
history = do i1 <- get; saveState
             modify (*2)
             i2 <- get; saveState
             modify (*2)
             i3 <- get; loadState
             i4 <- get; loadState
             i5 <- get
             return (i1, i2, i3, i4, i5)


----- QuickCheck properties for StateMonadPlus.



-- |Test that if you put something, the state is set to it.
prop_Put :: Int -> Int -> Bool
prop_Put a b = case runStateMonadPlus (put b) a of
                   (Left _)       -> False   -- shouldn't fail
                   (Right (_, s)) -> s == b  -- the state should be set to b
          
-- |Test that `get` gives you the state.
prop_Get :: Int -> Bool
prop_Get a = case runStateMonadPlus get a of
                   (Left _)       -> False   -- shouldn't fail
                   (Right (r, _)) -> r == a  -- get should give the state


-- |Test that `loadState` fails if there is no state stored.
prop_LoadEmptyFails :: Bool
prop_LoadEmptyFails = either (const True) (const False) $ runStateMonadPlus loadState () 

-- |Test that `loadState` gets back what's put there using `saveState` 
prop_StoreLoad :: (Int,Int,Int,Int) -> Bool
prop_StoreLoad ss@(s,s1,s2,s3) = case runStateMonadPlus m s of
                                     (Left _)        -> False    -- shouldn't fail
                                     (Right (rr, _)) -> ss == rr -- we should get the same states back
    where m = do saveState; put s1
                 saveState; put s2 
                 saveState; put s3
                 r3 <- get; loadState
                 r2 <- get; loadState
                 r1 <- get; loadState
                 r <- get
                 return (r, r1, r2, r3)
 
 

-------- definitions from the assignments ------------------------

-- |Rose datatype.
data Rose a = a :> [Rose a] deriving (Eq, Show)

-- |`fmap` over a Rose.
instance Functor Rose where
    fmap f (x :> []) = (f x :> [])
    fmap f (x :> xs) = (f x :> fmap (fmap f) xs)

-- |List instance for `foldable'`
instance Foldable' [] where
    fold = foldr mappend mempty

------------------------------------------------------------------

{---- 3.3.3 ----}
-- |`fold` over a Rose.
instance Foldable' Rose where
    fold (x :> []) = mappend x mempty
    fold (x :> xs) = mappend x $ foldr mappend mempty $ map fold xs
    

{---- 3.3.4 ----}
-- |`Foldable'` class, something you can fold over.
class Functor f => Foldable' f where
    fold :: Monoid m => f m -> m

    -- |Default `foldMap` implementation. 
    foldMap :: Monoid m => (a -> m) -> f a -> m
    foldMap f = fold . fmap f  

{---- 3.3.5 ----}
newtype Sum     a = Sum     {unSum :: a}     deriving (Eq,Show)
newtype Product a = Product {unProduct :: a} deriving (Eq,Show)

-- |Numbers form a monoid using addition as composition and `0` as the identity.
instance Num a => Monoid (Sum a) where
    mempty                    = Sum 0
    mappend (Sum n1) (Sum n2) = Sum (n1 + n2)

-- |Numbers also form a monoid using multiplication as composition and `1` as the identity.
instance Num a => Monoid (Product a) where
    mempty                            = Product 1
    mappend (Product n1) (Product n2) = Product (n1 * n2)

-- |Sum a foldable of numbers.
fsum :: (Foldable' f, Num a) => f a -> a
fsum = unSum . foldMap Sum 

-- |Get the product of a foldable of numbers.
fproduct :: (Foldable' f, Num a) => f a -> a
fproduct = unProduct . foldMap Product


