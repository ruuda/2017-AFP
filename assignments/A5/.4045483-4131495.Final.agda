module Final where

{-

4045483
4131495

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

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

appendList : {a : Set} -> List a -> List a -> List a
appendList Nil ys = ys
appendList (Cons x xs) ys = Cons x (appendList xs ys)

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

-- A bounded natural number (lower than n)
data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

-- Moved here from exercise 5
sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

-- Taken from the lectures
infixr 2 _<_>_
_<_>_ : {a : Set} -> (x : a) -> {y z : a} -> x == y -> y == z -> x == z
x < p > q = trans p q

_QED : {a : Set} (x : a) -> x == x
_QED x = Refl

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {a : Set} -> a -> Vec a 1
pure x = Cons x Nil 

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f fs <*> Cons x xs = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs)= Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons ((vmap _+_ xs) <*> ys) (madd xss yss) 

-- Define the identity matrix
zeroes : {n : Nat} -> Vec Nat n
zeroes {Zero} = Nil
zeroes {Succ _} = Cons 0 zeroes

idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ _} = Cons (Cons (Succ Zero) zeroes) (vmap (Cons Zero) idMatrix)

-- Define matrix transposition
nilLine : {m : Nat} {a : Set} -> Matrix a Zero m
nilLine {Zero} = Nil
nilLine {Succ _} = Cons Nil nilLine

transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = nilLine
transpose (Cons xs xss) = vmap Cons xs <*> (transpose xss)

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs f) = Succ (forget f)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
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
incr : {n m : Nat} -> Compare n m -> Compare (Succ n) (Succ m)
incr (LessThan k) = LessThan k
incr Equal = Equal
incr (GreaterThan k) = GreaterThan k
cmp : (n m : Nat) -> Compare n m
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) = incr (cmp n m)

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difcmp : {n m : Nat} -> Compare n m -> Nat
difcmp (LessThan k) = Succ k
difcmp Equal = Zero
difcmp (GreaterThan k) = Succ k
difference : (n m : Nat) -> Nat
difference n m = difcmp (cmp n m)

-- Verify that our difference function works properly
differenceGT : difference 5 2 == 3
differenceGT = Refl
differenceLT : difference 2 5 == 3
differenceLT = Refl
differenceEQ : difference 2 2 == 0
differenceEQ = Refl

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n') m = cong Succ (plusSucc n' m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes n Zero = plusZero n
-- n' + m == m + n' (by plusCommutes n' m)
-- Succ (n' + m) == Succ (m + n') (by cong Succ)
-- Succ (n' + m) == (m + Succ n') (by trans (plusSucc m n'))
plusCommutes (Succ n') m = trans (cong Succ (plusCommutes n' m)) (plusSucc m n')

mulByZero : (n : Nat) -> (n * Zero) == Zero
mulByZero Zero = Refl
mulByZero (Succ n') = mulByZero n'

plusMulByZero : (n m : Nat) -> ((n * Zero) + m) == m
plusMulByZero Zero m = Refl
-- n * Zero == Zero (by mulByZero n)
-- (n * Zero) + Zero == Zero (by trans (plusZero (n * Zero)))
plusMulByZero n Zero = trans (plusZero (n * Zero)) (mulByZero n)
plusMulByZero (Succ n') m = plusMulByZero n' m 

plusAssoc : (x y z : Nat) -> (x + (y + z)) == ((x + y) + z)
plusAssoc Zero y z = Refl
plusAssoc (Succ x') y z = cong Succ (plusAssoc x' y z)

plusCommutesHelper : (x y z : Nat) -> (x + (y + z)) == (x + (z + y))
plusCommutesHelper Zero y z = plusCommutes y z
plusCommutesHelper (Succ x') y z = cong Succ (plusCommutesHelper x' y z)

plusLemma : (a b c d : Nat) -> ((a + b) + (c + d)) == ((a + c) + (b + d))
-- (b + (c + d)) == ((b + c) + d) (by plusAssoc b c d)
--               == (d + (b + c)) (by trans (plusCommutes (b + c) d))
--               == ((d + b) + c) (by trans (plusAssoc d b c))
--               == (c + (d + b)) (by trans (plusCommutes (d + b) c))
--               == (c + (b + d)) (by trans (plusCommutsHelper c d b))
plusLemma Zero b c d =
  trans (plusAssoc b c d)
  (trans (plusCommutes (b + c) d)
  (trans (plusAssoc d b c)
  (trans (plusCommutes (d + b) c)
  (trans (plusCommutesHelper c d b)
  Refl)))) 
plusLemma (Succ a') b c d = cong Succ (plusLemma a' b c d)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
-- (n * k) == (n * k)
-- (n * k) == ((n * Zero) + (n * k)) (by trans(plusMulByZero n (n * k)))
distributivity n Zero k = trans Refl (sym (plusMulByZero n (n * k)))
-- (n' * (m + k)) == ((n' * m) + (n' * k))
-- (m + k) + (n' * (m + k)) == (m + k) + ((n' * m) + (n' * k)) (by cong (_+_ (m + k))
-- ((m + k) + (n' * (m + k))) == ((m + (n' * m)) + (k + (n' * k))) (by trans plusLemma)
distributivity (Succ n') m k = trans (cong (_+_ (m + k)) (distributivity n' m k)) (plusLemma m k (n' * m) (n' * k))

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

-- SubList means that the first list is contained in the second one, with all its elements
data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil} = Base
SubListRefl {xs = Cons _ _} = Keep SubListRefl

SubListFromNil : {a : Set} (xs : List a) -> SubList Nil xs
SubListFromNil Nil = Base
SubListFromNil (Cons x xs) = Drop (SubListFromNil xs)

SubListWeakenLeft : {a : Set} {xs ys : List a} {x : a} -> SubList (Cons x xs) ys -> SubList xs ys
SubListWeakenLeft (Keep sl) = Drop sl
SubListWeakenLeft (Drop sl) = Drop (SubListWeakenLeft sl)

SubListMalformed : {a b : Set} {x : a} {xs : List a} -> SubList (Cons x xs) xs -> b
SubListMalformed {xs = Nil} ()
SubListMalformed {xs = Cons _ xs} (Keep sl) = SubListMalformed sl
SubListMalformed {xs = Cons y xs} (Drop sl) = SubListMalformed (SubListWeakenLeft sl)

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans {xs = Nil} {Nil} {Nil} sl1 sl2 = sl2
SubListTrans {xs = Nil} {Nil} {Cons x zs} sl1 sl2 = sl2
SubListTrans {xs = Nil} {Cons x ys} {Nil} sl1 sl2 = Base
SubListTrans {xs = Nil} {Cons x₁ ys} {Cons .x₁ zs} (Drop sl1) (Keep sl2) = Drop (SubListTrans sl1 sl2)
SubListTrans {xs = Nil} {Cons x ys} {Cons x₁ zs} (Drop sl1) (Drop sl2) = Drop (SubListFromNil zs)
SubListTrans {xs = Cons x xs} {Nil} {Nil} sl1 sl2 = sl1
SubListTrans {xs = Cons x xs} {Nil} {Cons x₁ zs} () sl2
SubListTrans {xs = Cons x₁ xs} {Cons .x₁ ys} {Nil} (Keep sl1) ()
SubListTrans {xs = Cons x xs} {Cons x₁ ys} {Nil} (Drop sl1) ()
SubListTrans {xs = Cons x₂ xs} {Cons .x₂ ys} {Cons .x₂ zs} (Keep sl1) (Keep sl2) = Keep (SubListTrans sl1 sl2)
SubListTrans {xs = Cons x₁ xs} {Cons .x₁ ys} {Cons x₂ zs} (Keep sl1) (Drop sl2) = Drop (SubListTrans (Keep sl1) sl2)
SubListTrans {xs = Cons x xs} {Cons x₂ ys} {Cons .x₂ zs} (Drop sl1) (Keep sl2) = Drop (SubListTrans sl1 sl2)
SubListTrans {xs = Cons x xs} {Cons x₁ ys} {Cons x₂ zs} (Drop sl1) (Drop sl2) = Drop (SubListTrans sl1 (SubListWeakenLeft sl2))

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base sl2 = Refl
SubListAntiSym (Keep {x} sl1') (Keep sl2') = cong (Cons x) (SubListAntiSym sl1' sl2')
SubListAntiSym (Keep {x} sl1') (Drop sl2') = cong (Cons x) (SubListAntiSym sl1' (SubListWeakenLeft sl2'))
SubListAntiSym (Drop {x} sl1') (Keep sl2') = cong (Cons x) (SubListAntiSym (SubListWeakenLeft sl1') sl2')
SubListAntiSym (Drop sl1') (Drop sl2') = SubListMalformed (SubListTrans sl1' (SubListWeakenLeft sl2'))

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
-- Note: the data type is defined in such a way that only valid instances
-- are possible (e.g. it is impossible to construct LEQ 5 4)
data LEQ : Nat -> Nat -> Set where
  Base : forall {n} -> LEQ Zero n
  Step : forall {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

leqRefl : {n : Nat} -> LEQ n n
leqRefl {Zero} = Base
leqRefl {Succ _} = Step leqRefl

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base leq2 = Base
leqTrans (Step leq1') (Step leq2') = Step (leqTrans leq1' leq2')

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step leq1')(Step leq2') = cong Succ (leqAntiSym leq1' leq2')

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl
leq<= (Step leq) = leq<= leq

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m Refl = Base
<=leq (Succ n') Zero ()
<=leq (Succ n') (Succ m') eq = Step (<=leq n' m' eq)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP x y = y x

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
notNotExcludedMiddle {P} = λ x → x (Inr (λ x₁ → x (Inl x₁)))

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
step1 dn = λ {P} → dn (λ z → z (Inr (λ x → z (Inl x))))

step2 : excludedMiddle -> impliesToOr
step2 = {!!}

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

----------------------
----- Exercise 9 -----
----------------------

data Expr : Set where
  Add : Expr -> Expr -> Expr
  Val : Nat -> Expr

-- We can write a simple evaluator as follows
eval : Expr -> Nat
eval (Add l r) = eval l + eval r
eval (Val x) = x

-- We can also compile such expressions to stack machine code
data Cmd : (i o : Nat) -> Set where
  -- stop execution and return the current stack
  HALT : forall {i} -> Cmd i i
  -- push a new number on the stack and continue execution on the next Cmd
  PUSH : forall {i o} -> Nat -> Cmd (Succ i) o -> Cmd i o
  -- replace the top two elements of the stack with their sum and continue execution on the next Cmd
  ADD : forall {i o} -> Cmd (Succ i) o -> Cmd (Succ (Succ i)) o

Stack : Nat -> Set
Stack = Vec Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...

sum : forall {n} -> Stack (Succ (Succ n)) -> Stack (Succ n)
sum (Cons x (Cons y s)) = Cons (x + y) s

exec : forall {i o} -> Cmd i o -> Stack i -> Stack o
exec HALT s = s
exec (PUSH n c) s = exec c (Cons n s)
exec (ADD c) xs = exec c (sum xs)

appendCmd : forall {n m k} -> Cmd n m -> Cmd m k -> Cmd n k
appendCmd HALT c2 = c2
appendCmd (PUSH x c1) c2 = PUSH x (appendCmd c1 c2)
appendCmd (ADD c1) c2 = ADD (appendCmd c1 c2)

-- Define a compiler from expresions to instructions
compile : forall {n} -> Expr -> Cmd n (Succ n)
compile (Val x) = PUSH x HALT
compile (Add e1 e2) = let c1 = compile e1
                          c2 = compile e2
                      in appendCmd (appendCmd c1 c2) (ADD HALT)

sumCommutes : {n : Nat} -> (x y : Nat) (ys : Stack n) ->
  sum (Cons x (Cons y ys)) == sum (Cons y (Cons x ys))
sumCommutes x y ys = cong (λ k -> Cons k ys) (plusCommutes x y)

addHaltLemma : forall {n} {s : Stack n} -> (cmd : Cmd n (Succ (Succ n))) ->
  exec (appendCmd cmd (ADD HALT)) s == sum (exec (appendCmd cmd HALT) s)
addHaltLemma {s = s} (PUSH x cmd) = {!!}
addHaltLemma {s = s} (ADD cmd) = {!!}

appendHaltLemma : forall {n m} -> (cmd : Cmd n m) ->
  appendCmd cmd HALT == cmd
appendHaltLemma HALT = Refl
appendHaltLemma (PUSH x cmd) = cong (PUSH x) (appendHaltLemma cmd)
appendHaltLemma (ADD cmd) = cong ADD (appendHaltLemma cmd)

execAppendLemma' : forall {n} {s : Stack n} (e1 e2 : Expr) ->
  sum (exec (appendCmd (compile e1) (compile e2)) s) == sum (exec (compile e1) (exec (compile e2) s))
execAppendLemma' (Add e1 e2) e3 = {!!}
execAppendLemma' (Val x) (Add e1 e2) = {!!}
execAppendLemma' {s = s} (Val x) (Val y) = cong (λ k -> Cons k s) (plusCommutes y x)

execAppendLemma : forall {n} {s : Stack n} (cmd : Cmd n (Succ (Succ n))) ->
  exec (appendCmd cmd (ADD HALT)) s == sum (exec cmd s)
execAppendLemma {s = s} (PUSH x cmd) =
  exec (appendCmd (PUSH x cmd) (ADD HALT)) s
    < addHaltLemma (PUSH x cmd) >
  sum (exec (appendCmd cmd HALT) (Cons x s))
    < cong (λ c -> sum (exec c (Cons x s))) (appendHaltLemma cmd) >
  sum (exec cmd (Cons x s))
    < Refl >
  sum (exec (PUSH x cmd) s)
    QED
execAppendLemma {s = s} (ADD cmd) = {!!}
--  exec (ADD (appendCmd cmd (ADD HALT))) s
--    < execAppendLemma {!!}  >
  --sum (exec (appendCmd cmd (ADD HALT)) s)
  --  < ? >
--  sum (exec (ADD cmd) s)
 --   QED

-- And prove your compiler correct
correctness : forall {n} -> (e : Expr) (s : Stack n) -> Cons (eval e) s == exec (compile e) s
correctness (Val x) s = Refl
correctness (Add e1 e2) s =
  sum (Cons (eval e1) (Cons (eval e2) s))
    < cong sum (correctness e1 (Cons (eval e2) s)) >
  sum (exec (compile e1) (Cons (eval e2) s))
    < cong (λ x -> sum (exec (compile e1) x)) (correctness e2 s) >
  sum (exec (compile e1) (exec (compile e2) s))
    < sym (execAppendLemma' e1 e2) >
  sum (exec (appendCmd (compile e1) (compile e2)) s)
    < sym (execAppendLemma (appendCmd (compile e1) (compile e2))) >
  exec (appendCmd (appendCmd (compile e1) (compile e2)) (ADD HALT)) s
    QED

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
