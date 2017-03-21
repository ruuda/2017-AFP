{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

{- Marinus Oosters - 3370798 - AFP Assignment 3 -}

module Ass3 where

import Prelude hiding (foldr)
import Control.Monad.Reader hiding (fix)
import System.Random
import Data.Maybe
 
data Tree a = Leaf a | Node (Tree a) (Tree a) deriving (Eq, Show)

-- |\2.2.1 Tail recursion

-- It said "remember that functions can be used as parameters" so I used a continuation.
splitleft :: Tree a -> (a, Maybe (Tree a))
splitleft tree = sl' tree id
    where sl' :: Tree a -> ((a, Maybe (Tree a)) -> b) -> b 
          sl' (Leaf a)   cont = cont (a, Nothing)
          sl' (Node l r) cont = sl' l $ \(a, x) -> cont (a, Just $ case x of 
                                                                     Nothing   ->  r
                                                                     (Just l') -> Node l' r)
 
-- |\2.2.3 foldr using fix

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z = fix (\f' ls -> case ls of []     -> z 
                                      (x:xs) -> f x $ f' xs)

-- |\2.4.1 Fixpoint

data F a = F {unF :: F a -> a}
y :: (a -> a) -> a
y = \f -> (\x -> f (x $ F x)) (\x -> f (unF x x))

-- prove that it works by using this as the `fix` function in the other assignment
fix :: (a -> a) -> a
fix = y

-- |\2.4.2 Nested datatype

type Square     = Square' Nil 
data Square' t a = Zero (t (t a)) | Succ (Square' (Cons t) a)
data Nil a       = Nil
data Cons t a    = Cons a (t a)

-- |2x2 identity matrix (Am I doing this right?)
idmat2_2 :: Square Integer
idmat2_2 = Succ $ Succ $ Zero ( Cons (Cons 1 $ Cons 0 Nil)
                              $ Cons (Cons 0 $ Cons 1 Nil) Nil)

-- |2x2 matrix [[2,1],[1,2]], which if everything works correctly is equal to fmap succ idmat2_2
succ_idmat2_2 :: Square Integer
succ_idmat2_2 = Succ $ Succ $ Zero ( Cons (Cons 2 $ Cons 1 Nil)
                                   $ Cons (Cons 1 $ Cons 2 Nil) Nil)

-- |3x3 matrix containing 1..9
mat3_3 :: Square Integer
mat3_3 = Succ $ Succ $ Succ $ Zero ( Cons (Cons 1 $ Cons 2 $ Cons 3 Nil)
                                   $ Cons (Cons 4 $ Cons 5 $ Cons 6 Nil)
                                   $ Cons (Cons 7 $ Cons 8 $ Cons 9 Nil) Nil)

-- |\2.4.3 functor on square matrices

-- Given definitions for equality ----------------------------------
eqNil :: (a -> a -> Bool) -> (Nil a -> Nil a -> Bool)
eqNil _ Nil Nil = True

eqCons :: (forall b. (b -> b -> Bool) -> (t b -> t b -> Bool)) ->
          (a -> a -> Bool) -> (Cons t a -> Cons t a -> Bool)
eqCons eqT eqA (Cons x xs) (Cons y ys) = eqA x y && eqT eqA xs ys


eqSquare' :: (forall b. (b -> b -> Bool) -> (t b -> t b -> Bool)) ->
             (a -> a -> Bool) -> (Square' t a -> Square' t a -> Bool)
eqSquare' eqT eqA (Zero xs) (Zero ys) = eqT (eqT eqA) xs ys
eqSquare' eqT eqA (Succ xs) (Succ ys) = eqSquare' (eqCons eqT) eqA xs ys
eqSquare' eqT eqA _         _         = False


eqSquare :: (a -> a -> Bool) -> Square a -> Square a -> Bool
eqSquare = eqSquare' eqNil


instance Eq a => Eq (Square a) where (==) = eqSquare (==)

-- Definition for map over square ----------------------------------

-- Nil remains Nil, obviously
mapNil :: (a -> b) -> (Nil a -> Nil b)
mapNil _ Nil = Nil 

-- for Cons, map the `a->b` function over the inner values
mapCons :: (forall x. (x -> b) -> t x -> t b) -> (a -> b) -> Cons t a -> Cons t b
mapCons mapT mapA (Cons x xs) = Cons (mapA x) (mapT mapA xs)

-- for the square, if it's Zero we need to map over the inner argument,
-- and if it's Succ we need to recurse a level deeper
mapSquare' :: (forall x y. (x -> y) -> (t x -> t y)) -> (a -> b) -> (Square' t a -> Square' t b)
mapSquare' mapT mapA (Zero xs) = Zero $ mapT (mapT mapA) xs
mapSquare' mapT mapA (Succ xs) = Succ $ mapSquare' (mapCons mapT) mapA xs

-- finally, a map function over the `Square` type
mapSquare :: (a -> b) -> Square a -> Square b
mapSquare = mapSquare' mapNil

instance Functor Square where fmap = mapSquare
 

-- to prove that it works, this gives true
fmapSquareWorks :: Bool
fmapSquareWorks = fmap succ idmat2_2 == succ_idmat2_2


