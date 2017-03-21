{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeSynonymInstances #-}

module AFPSet3 where

import qualified Data.Tree as T
import Control.Monad.Reader hiding (fix)
import System.Random

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving (Eq, Show)

drawTree =
  let convert (Leaf a)   = T.Node (show a) []
      convert (Node l r) = T.Node "+" [convert l, convert r]
  in T.drawTree . convert

splitleft :: Tree a -> (a, Maybe (Tree a))
splitleft (Leaf a)   = (a, Nothing)
splitleft (Node l r) =
  case splitleft l of
    (a, Nothing) -> (a, Just r)
    (a, Just l') -> (a, Just (Node l' r))

splitLeftTR :: Tree a -> (a, Maybe (Tree a))
splitLeftTR =
  let sl m (Leaf a)   = (a, m)
      sl m (Node l r) =
        case m of
          Nothing -> sl (Just r) l
          Just x -> sl (Just (Node x r)) l
  in sl Nothing

tree = Node ( Node ( Node (Leaf 1) (Leaf 2)) ( Node (Leaf 3) (Leaf 4))) ( Node
       (Node (Leaf 5) (Leaf 6)) ( Node (Leaf 7) (Leaf 8)))

--------------------------------------------------------------------------------
-- 2.2.3 Fix

fix :: (a -> a) -> a
fix f = f (fix f)

-- the first argument of fix is (r -> r)
-- r = [a] -> b to make it work
foldrfix :: (a -> b -> b) -> b -> [a] -> b
foldrfix f e =
  fix $ \g xs ->
    case xs of
      []   -> e
      y:ys -> f y (g ys)

--------------------------------------------------------------------------------
-- 2.4.(1 - 3) Nested Types

{- Doesn't work even with explicit type annotation. Infinite type
y :: (r -> r) -> r
y = \ f -> ( \ x -> f (x x) ) (\ x -> f (x x) )
-}

newtype F a = F { unF :: F a -> a }

y = \f -> (\x -> f (unF x x)) (F (\x -> f (unF x x)))

type Square      = Square' Nil
data Square' t a = Zero (t (t a))
                 | Succ (Square' (Cons t) a)

data Nil    a = Nil
data Cons t a = Cons a (t a)

matrix1 :: Square Int
matrix1 =
  let row1 = Cons 1 (Cons 0 Nil)
      row2 = Cons 0 (Cons 1 Nil)
  in Succ $ Succ (Zero (Cons row1(Cons row2 Nil)))

matrix2 :: Square Int
matrix2 =
  let row1 = Cons 1 (Cons 2 (Cons 3 Nil))
      row2 = Cons 4 (Cons 5 (Cons 6 Nil))
      row3 = Cons 7 (Cons 8 (Cons 9 Nil))
  in Succ $
      Succ (
        Succ (
          Zero (Cons row1 (Cons row2 (Cons row3 Nil)))))

eqNil :: (a -> a -> Bool) -> (Nil a -> Nil a -> Bool)
eqNil eq Nil Nil = True

eqCons
  :: (forall b. (b -> b -> Bool) -> (t b -> t b -> Bool))
  -> (a -> a -> Bool)
  -> (Cons t a -> Cons t a -> Bool)
eqCons eq1 eq2 (Cons x xs) (Cons y ys) = eq2 x y && eq1 eq2 xs ys

eqSquare'
  :: (forall b. (b -> b -> Bool) -> (t b -> t b -> Bool))
  -> (a -> a -> Bool)
  -> (Square' t a -> Square' t a -> Bool)
eqSquare' eq1 eq2 (Zero xs) (Zero ys) = let r = eq1 eq2 in eq1 r xs ys
eqSquare' eq1 eq2 (Succ xs) (Succ ys) = eqSquare' (eqCons eq1) eq2 xs ys
eqSquare' eq1 eq2 _         _         = False

{- Without the forall you get a type error because the type of the function
 - changes. eq1 does not necesarrily match eq2, or more specifically a in (a ->
 - a -> Bool) and b in (b -> b -> Bool) does not necessarily unify.
 -}

eqSquare :: (a -> a -> Bool) -> Square a -> Square a -> Bool
eqSquare = eqSquare' eqNil

instance Eq a => Eq (Square a) where
    (==) = eqSquare (==)

mapNil :: (a -> b) -> Nil a -> Nil b
mapNil mapA Nil = Nil

mapCons
  :: (forall a b. (a -> b) -> t a -> t b)
  -> (c -> d)
  -> Cons t c
  -> Cons t d
mapCons map1 map2 (Cons x xs) = Cons (map2 x) (map1 map2 xs)

mapSquare'
  :: (forall c d. (c -> d) -> t c -> t d)
  -> (a -> b)
  -> Square' t a
  -> Square' t b
mapSquare' map1 map2 (Zero xs) = Zero $ map1 (map1 map2) xs
mapSquare' map1 map2 (Succ xs) = Succ $ mapSquare' (mapCons map1) map2 xs

mapSquare :: (a -> b) -> Square a -> Square b
mapSquare = mapSquare' mapNil

--------------------------------------------------------------------------------
-- 2.5.3 Evidence Translations

one :: Int
one = 1

two :: Int
two = 2

randomN :: (RandomGen g) => Int -> g -> Int
randomN n g = (fst (next g) `mod` (two * n + one)) - n

-- The most general type (deduced by GHC) is the given one, which has a non
-- type-variable argument on the constraint of MonadReader, namely Int.
sizedInt ::
  (RandomGen g, MonadReader Int (t m), MonadReader g m, MonadTrans t) =>
  t m Int
sizedInt =
  do
    n <- ask
    g <- lift ask
    return (randomN n g)

-- Evidence translated monad because it keeps whining when i use normal monad.
data MonadF m = MonadF
  { freturn :: forall a. a -> m a
  , fbind   :: forall a b. m a -> (a -> m b) -> m b
  }

-- perform evidence translation on randomN and sizedInt. type signatures for the
-- relevant functions are stolen from hoogle
newtype RandomGenF   g   = RandomGenF   { fnext :: g -> (Int, g) }
newtype MonadReaderF m r = MonadReaderF { fask  :: m r }
newtype MonadTransF  t   =
  MonadTransF  { flift :: forall m a. MonadF m -> m a -> t m a }

-- basically a clone of randomN but then one that works on the datatype instead
-- of the class
randomNF :: RandomGenF g -> Int -> g -> Int
randomNF rg i g =
  let (x, _) = fnext rg g
  in x `mod` (two * i + one) - i

sizedIntF
  :: MonadF m
  -> MonadF (t m)
  -> RandomGenF g
  -> MonadTransF t
  -> MonadReaderF (t m) Int
  -> MonadReaderF m g
  -> t m Int
sizedIntF mM mTM rgen trans readerint readerrand =
  fbind mTM (fask readerint) ( \q ->
    fbind mTM (flift trans mM (fask readerrand))
      (freturn mTM . randomNF rgen q))

