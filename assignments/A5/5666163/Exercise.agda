module Exercise where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits.

If you have any questions, don't hesitate to email me or ask in class.
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True  : Bool
  False : Bool

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ  #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
Zero   + m = m
Succ k + m = Succ (k + m)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
Zero     * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil  : List a
  Cons : a → List a → List a

data Vec (a : Set) : ℕ → Set where
  Nil  : Vec a 0
  Cons : {n : ℕ} → (x : a) → (xs : Vec a n) → Vec a (Succ n)

head : {a : Set} {n : ℕ}→ Vec a (Succ n) → a
head (Cons x xs) = x

append : {a : Set} {n m : ℕ} → Vec a n → Vec a m → Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

infixr 5 _++_
_++_ : {a : Set} {n m : ℕ} → Vec a n → Vec a m → Vec a (n + m)
_++_ = append

infix 4 _≡_
data _≡_ {a : Set} (x : a) : a → Set where
  Refl : x ≡ x

cong : {a b : Set} {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} → Empty → a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a → b → Pair a b

data Fin : ℕ → Set where
  Fz : ∀ {n} → Fin (Succ n)
  Fs : ∀ {n} → Fin n → Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a → Maybe a
  Nothing : Maybe a

exfalso : { a : Set} -> Empty -> a
exfalso ()

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x
sym Refl = Refl

trans : {a : Set} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
trans Refl Refl = Refl

-- Function extensionality
postulate fun-ext : {a b : Set} {f g : a → b} → (∀ x → f x ≡ g x) → f ≡ g

infixr 2 _<_>_
_<_>_ : {a : Set} -> (x : a) -> {y z : a} -> x ≡ y -> y ≡ z -> x ≡ z
x < p > q = trans p q

_QED : {a : Set} (x : a) -> x ≡ x
_QED x = Refl

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : ℕ} {a : Set} → a → Vec a n
pure {Zero}   x = Nil
pure {Succ _} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : ℕ} → Vec (a → b) n → Vec a n → Vec b n
Nil <*> Nil = Nil
(Cons f fs) <*> (Cons x xs) = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : ℕ} → (a → b) → Vec a n → Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

infixl 4 _<$>_
_<$>_ = vmap

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set → ℕ → ℕ → Set
Matrix a n m = Vec (Vec a n) m

zipWith : {a b c : Set} {n : ℕ} → (a → b → c) → Vec a n → Vec b n → Vec c n
zipWith f Nil Nil = Nil
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys)

-- Define the identity matrix
idMatrix : {n : ℕ} → Matrix ℕ n n
idMatrix {Zero}   = Nil
idMatrix {Succ _} = pure (pure 1)

-- Define matrix transposition
transpose : {n m : ℕ} {a : Set} → Matrix a m n → Matrix a n m
transpose Nil = pure Nil
transpose (Cons xs xss) = vmap Cons xs <*> (transpose xss)

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : ℕ} → Vec (Fin n) n
plan {Zero}   = Nil
plan {Succ _} = pure Fz

-- Define a forgetful map, mapping Fin to ℕ
forget : {n : ℕ} → Fin n → ℕ
forget Fz     = Zero
forget (Fs n) = forget n

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : ℕ} → Fin n → Fin (Succ n)
embed Fz     = Fs Fz
embed (Fs n) = Fs (Fs n)

correct : {n : ℕ} → (i : Fin n) → forget i ≡ forget (embed i)
correct Fz     = Refl
correct (Fs s) = Refl

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : ℕ → ℕ → Set where
  LessThan    : ∀ {n} k → Compare n (n + Succ k)
  Equal       : ∀ {n}   → Compare n n
  GreaterThan : ∀ {n} k → Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : ℕ) → Compare n m
cmp Zero     Zero     = Equal
cmp (Succ n) Zero     = GreaterThan n
cmp Zero     (Succ m) = LessThan m
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k    = LessThan k
cmp (Succ m) (Succ .m)            | Equal         = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : ℕ) → ℕ
difference Zero m = m
difference (Succ x) y with cmp x y
difference (Succ n) .(n + Succ k) | LessThan k    = k
difference (Succ y) .y            | Equal         = Zero
difference (Succ .(y + Succ k)) y | GreaterThan k = k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

plusZero : ∀ (n : ℕ ) → (n + 0) ≡ n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : ∀ (n m : ℕ ) → Succ (n + m) ≡ (n + Succ m)
plusSucc Zero     _ = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : ∀ (n m : ℕ ) → (n + m) ≡ (m + n)
plusCommutes Zero m     = sym (plusZero m)
plusCommutes (Succ n) m =
  let ih = plusCommutes n m
  in trans (cong Succ ih) (plusSucc m n)

plusAssoc : ∀ (n m k : ℕ ) → (n + m) + k ≡ n + (m + k)
plusAssoc Zero m k     = Refl
plusAssoc (Succ n) m k =
  let ih = plusAssoc n m k
  in cong Succ ih

exchange : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
exchange a b c d = trans                           (plusAssoc a b (c + d))
                  (trans (cong (a +_)              (sym (plusAssoc b c d)))
                  (trans (cong (λ x → a + (x + d)) (plusCommutes b c))
                  (trans (cong (a +_)              (plusAssoc c b d))
                                                   (sym (plusAssoc a c (b + d))))))

distributivity : (n m k : ℕ) → (n * (m + k)) ≡ ((n * m) + (n * k))
distributivity Zero     m k = Refl
distributivity (Succ n) m k =
  let ih = distributivity n m k
  in
  (Succ n) * (m + k)
    < Refl >
  (m + k) + (n * (m + k))
    < cong (((m + k) +_)) ih >
  m + k + (n * m + n * k)
    < exchange m k (n * m) (n * k) >
  m + n * m + (k + n * k)
    < Refl >
  ((((Succ n) * m) + ((Succ n) * k)) QED)

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a → List a → Set where
  Base : SubList Nil Nil
  Keep : ∀ {x xs ys} → SubList xs ys → SubList (Cons x xs) (Cons x ys)
  Drop : ∀ {y zs ys} → SubList zs ys → SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} → SubList xs xs
SubListRefl {xs = Nil}       = Base
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} → SubList xs ys → SubList ys zs → SubList xs zs
SubListTrans Base            yz  = yz
SubListTrans (Keep xy) (Keep yz) = Keep (SubListTrans xy yz)
SubListTrans (Drop xy) (Keep yz) = Drop (SubListTrans xy yz)
SubListTrans xy (Drop yz) = Drop (SubListTrans xy yz)

{-# TERMINATING #-}
KeepDrop-abs : {a : Set} {x : a} {xs ys : List a} → SubList xs ys → SubList (Cons x ys) xs → Empty
KeepDrop-abs Base ()
KeepDrop-abs (Keep p) (Keep q) = KeepDrop-abs p q
KeepDrop-abs (Keep p) (Drop q) = KeepDrop-abs (Drop p) q
KeepDrop-abs (Drop p) (Keep q) = KeepDrop-abs SubListRefl (SubListTrans (Drop p) q)
KeepDrop-abs (Drop p) (Drop q) = KeepDrop-abs (Drop SubListRefl) (SubListTrans (Drop q) p)

SubListAntiSym : {a : Set} {xs ys : List a} →  SubList xs ys → SubList ys xs → xs ≡ ys
SubListAntiSym Base ys = Refl
SubListAntiSym (Keep {x = x} xy) (Keep yz) = cong (Cons x) (SubListAntiSym xy yz)
SubListAntiSym (Keep xy) (Drop {y = x} yz) = magic (KeepDrop-abs xy yz)
SubListAntiSym (Drop xy) (Keep yz) = magic (KeepDrop-abs SubListRefl (SubListTrans xy yz))
SubListAntiSym (Drop xy) (Drop yz) = magic (KeepDrop-abs SubListRefl (SubListTrans (Drop yz) xy))


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : ℕ → ℕ → Set where
  leq-zero : {  n : ℕ } → LEQ Zero n
  leq-succ : {m n : ℕ } → LEQ m n → LEQ (Succ m) (Succ n)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : ℕ ) → LEQ n n
leqRefl Zero     = leq-zero
leqRefl (Succ n) = leq-succ (leqRefl n)

leqTrans : {n m k : ℕ } → LEQ n m → LEQ m k → LEQ n k
leqTrans leq-zero _ = leq-zero
leqTrans (leq-succ n) (leq-succ m) = leq-succ (leqTrans n m)

leqAntiSym : {n m : ℕ } → LEQ n m → LEQ m n → n ≡ m
leqAntiSym leq-zero leq-zero = Refl
leqAntiSym (leq-succ n) (leq-succ m) =
  let ih = leqAntiSym
  in cong Succ (ih n m)

-- Given the following function:
_<=_ : ℕ → ℕ → Bool
Zero <= y        = True
Succ x <= Zero   = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : ℕ } → LEQ n m → (n <= m) ≡ True
leq<= leq-zero     = Refl
leq<= (leq-succ i) = leq<= i

<=leq : (n m : ℕ ) → (n <= m) ≡ True → LEQ n m
<=leq Zero m proof = leq-zero
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) proof = leq-succ (<=leq n m proof)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set → Set
Not P = P → Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} → P → Not (Not P)
notNotP x y = y x

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a → Or a b
  Inr : b → Or a b

orCase : {a b c : Set} → (a → c) → (b → c) → Or a b → c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} → Not (Not (Or P (Not P)))
notNotExcludedMiddle x = x (Inr (\y → x (Inl y)))

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.

doubleNegation = {P : Set} → Not (Not P) → P
excludedMiddle = {P : Set} → Or P (Not P)
impliesToOr    = {P Q : Set} → (P → Q) → Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

step1 : doubleNegation → excludedMiddle
step1 dn = dn notNotExcludedMiddle

step2 : excludedMiddle → impliesToOr
step2 x = {!!}

step3 : impliesToOr → doubleNegation
step3  ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw : {P Q : Set} → ((P → Q) → P) → P
piercesLaw = {!!}

----------------------
----- Exercise 9 -----
----------------------

-- Given the following data type for expressions

data Expr : Set where
  Add : Expr → Expr → Expr
  Val : ℕ → Expr

-- We can write a simple evaluator as follows
eval : Expr → ℕ
eval (Add l r) = eval l + eval r
eval (Val x) = x

Stack : Set
Stack = List ℕ

-- We can also compile such expressions to stack machine code
data Cmd : Set where
  -- stop execution and return the current stack
  HALT : Cmd
  -- push a new number on the stack
  PUSH : ℕ → Cmd → Cmd
  -- replace the top two elements of the stack with their sum
  ADD : Cmd → Cmd
  

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...


-- I had an idea of how to make it work but in the end i couldn't make it work:
-- 1) make the Cmd carry around a ℕ that refers to the amount of numbers on the stack
-- 2) Make a new function called `stacksize` to compute the size of the stack depending on the command AND current stack
-- 3) have an exec function with approximate type {n : ℕ} → (c : Cmd n) → Stack n → Stack (stacksize c)
-- 4) ensure statically that
--    - HALT returns a stack, for any size of the stack
--    - PUSH increases the stack size by 1, for any size of the stack
--    - ADD reduces the stack size by 1 for any stack size >= 2
-- 5) be happy because this stack will never fail
exec : Cmd → Stack → Maybe Stack
exec HALT xs                      = Just xs
exec (PUSH x c) xs                = exec c (Cons x xs)
exec (ADD c) Nil                  = Nothing
exec (ADD c) (Cons x Nil)         = Nothing
exec (ADD c) (Cons x (Cons y xs)) = exec c (Cons (x + y) xs)


infixr 5 _+++_
_+++_ : Cmd -> Cmd -> Cmd
HALT      +++ ds = ds
PUSH x cs +++ ds = PUSH x (cs +++ ds)
ADD cs    +++ ds = ADD (cs +++ ds)


-- Define a compiler from expresions to instructions
compile : {n : ℕ} → Expr → Cmd
compile (Val x  ) = PUSH x HALT
compile (Add x y) = PUSH {!!} {!!}

fromJust : {a : Set} → Maybe a → a
fromJust (Just x) = x
fromJust Nothing = {!!}
{-
-- And prove your compiler correct
correctness : (e : Expr) (s : Stack) → Cons (eval e) s ≡ fromJust (exec (compile e) s)
correctness (Add e es) = {!!}
correctness (Val Zero) = {!!}
correctness (Val (Succ x)) = {!!}
-}

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
