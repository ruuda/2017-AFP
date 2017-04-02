module Exercise where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits.

If you have any questions, don't hesitate to email me or ask in class.

Exercises by Jasper Robeer (3802337).
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat -> Nat -> Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

-- Natural number equality, taken from agda.readthedocs.io/en/latest/built-ins.html#natural-numbers
-- ≡ is '\=='
_≡_ : Nat -> Nat -> Bool
Zero   ≡ Zero   = True
Succ n ≡ Succ m = n ≡ m
_      ≡ _      = False

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Changed to be identical to the builtin equality, to be able to use the `rewrite` abstraction
-- agda.readthedocs.io/en/latest/language/built-ins.html#built-in-equality
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  Refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL     Refl #-}

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero}   x = Nil
pure {Succ n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil       <*> _         = Nil
Cons f fs <*> Cons x xs = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f xs = pure f <*> xs

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Define matrix addition

-- Matrix addition works by adding all the elements in each index.
-- To make this easier we define a helper function which does the same, but for a vector.
-- We lift the addition into each element of the vector `xs` by partial application, and
-- then use composition <*> to perform the addition with each element of the second vector.
-- Matrix addition then follows in the same manner, but uses the vector addition `vadd`
-- instead of the addition `+` on natural numbers.
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd xs ys = vmap (_+_) xs <*> ys

madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xss yss = vmap vadd xss <*> yss

-- Define the identity matrix

-- The identity matrix has only ones on the diagional, and zeroes on all the other indices.
-- To make this easier we define a helper function which creates a vector of length n,
-- and sets the element at index k to 1. Filling the rest with zeroes.
-- The equality of natural numbers ≡ is taken from the offical Agda documentation and
-- provided in the prelude above.
idVector : (n k : Nat) -> Vec Nat n
idVector Zero     k = Nil
idVector (Succ n) k with (k ≡ n)
idVector (Succ n) k | True  = Cons 1 (idVector n k)
idVector (Succ n) k | False = Cons 0 (idVector n k)

diagonalMatrix : (n m : Nat) -> Matrix Nat n m
diagonalMatrix n Zero     = Nil
diagonalMatrix n (Succ m) = Cons (idVector n m) (diagonalMatrix n m)

-- TODO: this gives some type error???
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {n} = diagonalMatrix n n

-- Define matrix transposition

-- Transposing matrices is switches rows and columns. We can take the head of each row,
-- and concatenate each element of the row to the head of the transposed sub-matrix.
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil         = pure Nil
transpose (Cons x xs) = vmap Cons x <*> transpose xs

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero}   = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz     = Zero
forget (Fs f) = Succ (forget f)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz     = Fz
embed (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz     = Refl
correct (Fs f) = cong Succ (correct f)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- Show that there is a 'covering function'

cmp₀ : {n m : Nat} -> Compare n m -> Compare (Succ n) (Succ m)
cmp₀ (LessThan k)    = LessThan k
cmp₀ Equal           = Equal
cmp₀ (GreaterThan k) = GreaterThan k

cmp : (n m : Nat) -> Compare n m
cmp Zero     Zero     = Equal
cmp Zero     (Succ m) = LessThan m
cmp (Succ n) Zero     = GreaterThan n
cmp (Succ n) (Succ m) = cmp₀ (cmp n m)

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.

-- Agda is actually able to figure this out all by itself, how awesome!
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k    = k
difference m .m            | Equal         = m
difference .(m + Succ k) m | GreaterThan k = k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

-- Let's introduce the notation from the lectures in a more fancy way.
-- How to input the symbols: ≡ '\=='; ⟨ '\<'; ⟩ '\>'; ∎ '\qed';
infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : {a : Set} -> (x : a) -> {y z : a} -> x == y -> y == z -> x == z
x ≡⟨ p ⟩ y = trans p y

_∎ : {a : Set} (x : a) -> x == x
_∎ x = Refl

-- As done in the demo
plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero     = Refl
plusZero (Succ n) =
  (Succ n) + 0
    ≡⟨ Refl ⟩
  Succ (n + 0)
    ≡⟨ cong Succ (plusZero n) ⟩
  Succ n
    ∎

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero     m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero     m = sym (plusZero m)
plusCommutes (Succ n) m =
  (Succ n) + m
    ≡⟨ cong Succ (plusCommutes n m) ⟩
  plusSucc m n
  -- We cannot use the ∎ here, as the proof is completed by the `plusSucc`...

-- The distributivity is left-distributive
distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero     m k = Refl
distributivity (Succ n) m k =
  -- (m + k) + (n * (m + k)) == (m + (n * m)) + (k + (n * k))
  ((m + k) + (n * (m + k)))
    ≡⟨ cong (λ x → (m + k) + x) (distributivity n m k) ⟩
  -- rewrite the right term by using distributivity again...
  (m + k) + ((n * m) + (n * k))
    ≡⟨ {!!} ⟩
  -- we have to use the associativity of * or + here..?
  {!(m + (n * m)) + (k + (n * k))!}

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil}       = Base
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base      ys        = ys
SubListTrans (Keep xs) (Keep ys) = Keep (SubListTrans xs ys)
SubListTrans xs        (Drop ys) = Drop (SubListTrans xs ys)
SubListTrans (Drop xs) (Keep ys) = Drop (SubListTrans xs ys)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base      Base      = Refl
SubListAntiSym (Keep xs) (Keep ys) = cong (Cons _) (SubListAntiSym xs ys)
SubListAntiSym (Keep xs) (Drop ys) = {!!}
SubListAntiSym (Drop xs) (Keep ys) = {!!}
SubListAntiSym (Drop xs) (Drop ys) = {!!}


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : Nat -> Nat -> Set where
  LEQBase : {n : Nat} -> LEQ Zero n
  LEQStep : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)
  -- The given definition is similar to the one given by the Agda standard lib

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero     = LEQBase
leqRefl (Succ n) = LEQStep (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQBase      ys           = LEQBase
leqTrans (LEQStep xs) (LEQStep ys) = LEQStep (leqTrans xs ys)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQBase     LEQBase     = Refl
leqAntiSym (LEQStep l) (LEQStep r) = cong Succ (leqAntiSym l r)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQBase     = Refl
leq<= (LEQStep l) = leq<= l

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero     m        l = LEQBase
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) l = LEQStep (<=leq n m l)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP = λ {P} y z → z y

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle = λ {P} z → z (Inr (λ x → z (Inl x)))
-- This is what agda figured out by itself...

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


step1 : doubleNegation -> excludedMiddle
step1 dn = dn notNotExcludedMiddle

step2 : excludedMiddle -> impliesToOr
step2 em = {!!}

step3 : impliesToOr -> doubleNegation
step3 ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

----------------------
----- Exercise 9 -----
----------------------

-- Given the following data type for expressions

data Expr : Set where
  Add : Expr -> Expr -> Expr
  Val : Nat -> Expr

-- We can write a simple evaluator as follows
eval : Expr -> Nat
eval (Add l r) = eval l + eval r
eval (Val x)   = x

-- We can also compile such expressions to stack machine code
data Cmd : Set where
  -- stop execution and return the current stack
  HALT : Cmd
  -- push a new number on the stack
  PUSH : Nat -> Cmd -> Cmd
  -- replace the top two elements of the stack with their sum
  ADD : Cmd -> Cmd

Stack : Set
Stack = List Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...

exec : Cmd -> Stack -> Stack
exec HALT       s                   = s
exec (PUSH x c) s                   = exec c (Cons x s)
exec (ADD c)    Nil                 = Nil
exec (ADD c)    (Cons x Nil)        = Nil
exec (ADD c)    (Cons x (Cons y s)) = exec c (Cons (x + y) s)

-- Define a compiler from expresions to instructions

-- The final instruction should be an `HALT` instruction. Therefore we introduce
-- an intermediate compilation which passes around the commands.
compile₀ : Expr -> Cmd -> Cmd
compile₀ (Add e₀ e₁) c = compile₀ e₁ (compile₀ e₀ (ADD c))
compile₀ (Val x)     c = PUSH x c

compile : Expr -> Cmd
compile e = compile₀ e HALT

-- And prove your compiler correct

-- To prove the correctness of the compilation, we have to take the final `HALT`
-- instruction into account as well. Therefore, we have to prove the correctness
-- of `compile₀` first.
-- To account for the correct order, `compile₀ (Add e₀ e₁) ...` should compile
-- the left-hand side expression as the inner argument. Otherwise, e₀ and e₁
-- get switched around inside the proof.
correctness₀ : (e : Expr) (s : Stack) (c : Cmd) ->
  exec c (Cons (eval e) s) == exec (compile₀ e c) s
correctness₀ (Add e₀ e₁) s c =      -- exec c (Cons (eval e₀ + eval e₁) s) == exec (compile₀ e₀ (compile₀ e₁ (ADD c))) s
  exec c (Cons (eval e₀ + eval e₁) s)
    ≡⟨ correctness₀ e₀ (Cons (eval e₁) s) (ADD c) ⟩
  exec (compile₀ e₀ (ADD c)) (Cons (eval e₁) s)
    ≡⟨ correctness₀ e₁ s (compile₀ e₀ (ADD c)) ⟩
  exec (compile₀ e₁ (compile₀ e₀ (ADD c))) s
    ∎
correctness₀ (Val x) s c = Refl -- exec c (Cons x s) == exec c (Cons x s)

correctness : (e : Expr) (s : Stack) ->
  Cons (eval e) s == exec (compile e) s
correctness e s = correctness₀ e s HALT

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
