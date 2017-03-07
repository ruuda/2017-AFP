{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}

module AFPAssignment2 where

import Prelude hiding (Foldable, foldMap)
import Control.Monad.State
import qualified Data.Tree as T
import qualified Data.Map as M

--------------------------------------------------------------------------------
-- Assignment 2.3: Monads

type FunctionName = String
type Table        = M.Map FunctionName Int
type Error        = String
type IVal a       = Either Error a -- Intermediate Value
type Stack a      = [a]

type Initial s   = (s, Table, Stack s)
type Return  s a = (s, IVal a, Table, Stack s)

newtype SMP s a = SMP { runIt :: Initial s -> Return s a }

{- Better:
 -
 - type SMP s a = StateT (Record s a) (Either Error) s
 -
 - data Record s a = Record
 -   { table :: M.Map FunctionName Int
 -   , stack :: [s]
 -   , value :: a
 -   }
 -
 - And enable -XRecordWildcards
 -
 - But that defies the point of the exercise i guess.
 -}

-- Monad receives an inital state, consisting of an initial state for the
-- computation and a tracking table for the function calls. It returns a new
-- state, an intermediate (or final) value and an updated table.
--
-- The IVal encodes a value of type a and an optional Error

instance Functor (SMP s) where
  f `fmap` (SMP g) =
    SMP $ \ ini ->
      let (s, val, table, stack) = g ini
          val' = f <$> val
      in (s, val', table, stack)

-- `decorator` for pure or return to get the diagnostics right
pureOrReturn str f x =
  SMP $ \ (s, table, stack) ->
    (s, f x, putFunc str table, stack)

instance Applicative (SMP s) where
  pure x = pureOrReturn "pure" pure x
  (<*>)  = ap -- O.o surprised that this works because today Monad is a subclass
              -- of Applicative

-- Given the name of a function, put it in the table or increment it if it's
-- already there. Could be more abstract with -XTemplateHaskell for automatic
-- function name detection
putFunc :: FunctionName -> Table -> Table
putFunc s t = M.insertWith (+) s 1 t

instance Monad (SMP s) where
  return x = pureOrReturn "return" return x
  (SMP f) >>= g =
    SMP $ \ ini ->
      let (s, val, table, stack) = f ini
          (SMP h)                 = either fail g val
          table'                  = putFunc ">>=" table
      in h (s, table', stack)

  fail str =
    SMP $ \ (s, table, stack) ->
      (s, Left str, putFunc "fail" table, stack)

instance MonadState s (SMP s) where
  get   = SMP $ \ (s, table, stack) -> (s, Right s, putFunc "get" table, stack)
  put s = SMP $ \ (_, table, stack) -> (s, Right (), putFunc "put" table, stack)

diagnostics :: SMP s String
diagnostics =
  SMP $ \ (s, table, stack) ->
    let table' = putFunc "diagnostics" table
        str = pretty (M.toAscList table')
    in (s, Right str, table', stack)

diagnosticsTest = printRight $ runStateMonadPlus diagnosticsTest' 0
  where
    diagnosticsTest' = do
      return 3 >> return 4
      return 5
      diagnostics

-- Some pretty printing functionality for the diagnostics
data Align = L | R

-- Fill a string up with spaces to a certain length, choice of align left or
-- align right
fill :: String -> Int -> Align -> String
fill str n a =
  let n' = n - length str
      s  = replicate n' ' '
  in case a of
    L -> str ++ s
    R -> s ++ str

-- Make a pretty table
pretty :: Show b => [(String, b)] -> String
pretty xs =
  let sf = maximum . map (length .        fst) $ xs
      ss = maximum . map (length . show . snd) $ xs
  in unlines ((\ (str, v) -> fill str sf L ++ " " ++ fill (show v) ss R) <$> xs)

-- unboxing of the either for nice printing...
printRight (Right (x, _)) = putStrLn x

-- `Annotation` in the sense that the computation in the second argument is
-- added to the table under the specified name.
annotate :: String -> SMP s a -> SMP s a
annotate str (SMP f) =
  SMP $ \ ini ->
    let (s, val, table, stack) = f ini
    in (s, val, putFunc str table, stack)

class MonadState s m => StoreState s m | m -> s where
  saveState :: m ()
  loadState :: m ()

instance StoreState s (SMP s) where
  saveState =
    annotate "saveState" . SMP $ \ (s, table, stack) ->
      (s, Right (), table, s:stack)

  loadState =
    annotate "loadState" . SMP $ \ (s, table, stack) ->
      case stack of
        []   -> (s, Left "Popped empty stack", table, stack)
        x:xs -> (x, Right (), table, xs)

storeStateTest' :: Either Error ((Int, Int, Int, Int, Int), Int)
storeStateTest' = flip runStateMonadPlus 1 $ do
  i1 <- get; saveState
  modify (*2)
  i2 <- get; saveState
  modify (*2)
  i3 <- get; loadState
  i4 <- get; loadState
  i5 <- get
  return (i1, i2, i3, i4, i5)

runStateMonadPlus :: SMP s a -> s -> Either String (a, s)
runStateMonadPlus mc s =
  let (s', val, table', stack) = runIt mc (s, M.empty, [])
  in case val of
    Left exc -> Left  exc
    Right v  -> Right (v, s')

--------------------------------------------------------------------------------
-- Assignment 3.3.(3|4|5): Foldable

data Rose a = a :> [Rose a]
  deriving Eq

instance Show a => Show (Rose a) where
  show = let convert (v :> []) = T.Node (show v) []
             convert (v :> cs) = T.Node (show v) (convert <$> cs)
         in T.drawTree . convert

instance Functor Rose where
  f `fmap` (v :> cs) = f v :> map (f `fmap`) cs

class Functor f => Foldable f where
  fold :: Monoid m => f m -> m
  foldMap :: Monoid m => (a -> m) -> f a -> m

  foldMap f = fold . fmap f

instance Foldable [] where
  fold = foldr mappend mempty

instance Foldable Rose where
  fold (v :> cs) = v `mappend` foldMap fold cs

newtype Sum     a = Sum     { unSum     :: a } deriving (Eq, Show)
newtype Product a = Product { unProduct :: a } deriving (Eq, Show)

instance Num a => Monoid (Sum a) where
  mempty                    = Sum 0
  (Sum x) `mappend` (Sum y) = Sum (x + y)

instance Num a => Monoid (Product a) where
  mempty                            = Product 1
  (Product x) `mappend` (Product y) = Product (x * y)

fsum, fproduct :: (Foldable f, Num a) => f a -> a
fsum     = unSum     . foldMap Sum
fproduct = unProduct . foldMap Product

--------------------------------------------------------------------------------
-- Assignment 2.2.8: Teletype IO

data GP a
  = End a
  | Get (Int -> GP a)
  | Put Int (GP a)

echo :: GP ()
echo = Get $ \ n -> Put n echo

run :: GP a -> IO a
run (End x)   = return x
run (Put x c) = print x >> run c
run (Get f)   = putStr "? " >> readLn >>= run . f

adder :: GP ()
adder =
  Get $ \ x ->
    Get $ \ y ->
      Put (x + y) $ End ()

accum = accum' 0
  where
    accum' n =
      Get $ \ x ->
        if x == 0
        then End n
        else Put (x + n) (accum' (x + n))

simulate :: GP a -> [Int] -> (a, [Int])
simulate (End x)    ys  = (x, ys)
simulate (Put _ c)  ys  = simulate c ys
simulate (Get f) (y:ys) = simulate (f y) ys

instance Functor GP where
  f `fmap` (End x)   = End (f x)
  f `fmap` (Get g)   = Get (fmap f . g)
  f `fmap` (Put n x) = Put n (fmap f x)

instance Applicative GP where
  pure x = End x
  (<*>)  = ap

instance Monad GP where
  (End x)   >>= f = f x
  (Get g)   >>= f = Get $ \ i -> g i >>= f
  (Put n x) >>= f = Put n (x >>= f)

-- functional dependency s -> a, so for s : Int
instance MonadState Int GP where
  get = Get $ \x -> End x
  put = flip Put (End ())

-- The behaviour is different in that you work with higher order funcion in the
-- state as well as in the value. In the statemonad the function is hidden away
-- in the type of the monad.

--------------------------------------------------------------------------------
-- Assignment 2.2.9: Stacks

data Nat = Z | S Nat
data Vec n a where
  VNil  :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

type Cont a r = (a -> r) -> r
type CStack n = Vec n Int

start :: Cont (CStack Z) r
start = ($ VNil)

store :: CStack n -> Int -> Cont (CStack (S n)) r
store xs i c = c (VCons i xs)

stop :: CStack (S n) -> Int
stop (VCons x _) = x

add :: CStack (S(S n)) -> Cont (CStack (S n)) r
add (VCons x (VCons y xs)) c = c $ VCons (x + y) xs

mul :: CStack (S(S n)) -> Cont (CStack (S n)) r
mul (VCons x (VCons y xs)) c = c $ VCons (x * y) xs

p1, p2 :: Int
p1 = start store 3 store 5 add stop
p2 = start store 3 store 6 store 2 mul add stop
-- p3 :: Int
--p3 = start store 2 add stop
