-- Arian van Putten - 4133935
-- Tim Baanen       - 4134524

module Exercise where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.
-}


---------------------
------ Prelude ------
---------------------

data 𝟚 : Set where
  True : 𝟚
  False : 𝟚

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : ℕ → ℕ → ℕ
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a → List a → List a

data Vec (a : Set) : ℕ → Set where
  Nil : Vec a 0
  Cons : {n : ℕ} → (x : a) → (xs : Vec a n) → Vec a (Succ n)

head : {a : Set} {n : ℕ} → Vec a (Succ n) → a
head (Cons x xs) = x

append : {a : Set} {n m : ℕ} → Vec a n → Vec a m → Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _≡_ {a : Set} (x : a) : a → Set where
  Refl : x ≡ x

cong : {a b : Set} {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
cong f Refl = Refl

cong₂ : {a b c : Set} {x y : a} {w z : b} → (f : a → b → c) → x ≡ y → w ≡ z → f x w ≡ f y z
cong₂ f Refl Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} → Empty → a
magic ()

So : 𝟚 -> Set
So True = Unit
So False = Empty

data Pair (a b : Set) : Set where
  _,_ : a → b → Pair a b

data Fin : ℕ → Set where
  Fz : ∀ {n} → Fin (Succ n)
  Fs : ∀ {n} → Fin n → Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a → Maybe a
  Nothing : Maybe a

-- Casting operator.
the : (a : Set) → a → a
the _ a = a

id : {a : Set} → a → a
id x = x

-- Let's introduce function composition
infixr 25 _∘_
_∘_ : {a b c : Set} → (b → c) → (a → b) → (a → c)
(g ∘ f) x = g (f x)

----------------------
----- Exercise 1 -----
----------------------

vmap : {a b : Set} {n : ℕ} → (a → b) → Vec a n → Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

--- Prove the identity law of functors
vec-functor-id : {n : ℕ} {a : Set} →  (xs : Vec a n) →
  vmap id xs ≡ id xs
vec-functor-id Nil = Refl
vec-functor-id (Cons x xs) = cong (Cons x) (vec-functor-id xs)

-- prove that vmap composes (Functor law 2)
vec-functor-comp : ∀{a b c g f n} → (xs : Vec a n) →
  (vmap g ∘ vmap f) xs ≡ vmap (g ∘ f) xs
vec-functor-comp Nil = Refl
vec-functor-comp {g = g} {f} (Cons x xs) =
  cong (Cons ((g ∘ f) x)) (vec-functor-comp xs)

--Show that the Vec a n type is applicative
η : {n : ℕ} {a : Set} → a → Vec a n
η {Zero} a = Nil
η {Succ n} a = Cons a (η a)

infixl 26 _⊙_
_⊙_ : {a b : Set} {n : ℕ} → Vec (a → b) n → Vec a n → Vec b n
Nil ⊙ xs = Nil
Cons f vf ⊙ Cons x xs = Cons (f x) (vf ⊙ xs)

-- Applicative Identity
vec-app-id : {a : Set } {n : ℕ} (v : Vec a n) →
  η id ⊙ v ≡ v
vec-app-id Nil = Refl
vec-app-id (Cons x v) = cong (Cons (id x)) (vec-app-id v)

-- Applicative Composition
vec-app-comp : {a b c : Set} {n : ℕ} (u : Vec (b → c) n) → (v : Vec (a → b) n) → (w : Vec a n) →
  (η (_∘_) ⊙ u ⊙ v ⊙ w) ≡ u ⊙ (v ⊙ w)
vec-app-comp Nil v w = Refl
vec-app-comp (Cons x u) (Cons x₁ v) (Cons x₂ w) = cong₂ Cons Refl (vec-app-comp u v w)

-- Applicative Homomorphism
vec-app-homo : {a b : Set} (n : ℕ) → (f : a → b) → (x : a) →
  (η {n} f) ⊙ (η x) ≡ η (f x)
vec-app-homo Zero f x = Refl
vec-app-homo (Succ n) f x = cong (Cons (f x)) (vec-app-homo n f x)

-- Applicative Interchange
vec-app-inter : {a b : Set} {y : a} {n : ℕ} (u : Vec (a → b) n) →
  (u ⊙ η y) ≡ (η (λ (f : (a → b)) → f y) ⊙ u)
vec-app-inter Nil = Refl
vec-app-inter {y = y} (Cons f u) = cong (Cons (f y)) (vec-app-inter u)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set → ℕ → ℕ → Set
Matrix a n m = Vec (Vec a n) m

-- Matrix instance for Applicative
mmap : ∀ {a b m n} → (a → b) → Matrix a m n → Matrix b m n
mmap f Nil = Nil
mmap f (Cons xs xss) = Cons (vmap f xs) (mmap f xss)

_ⓜ_ : ∀ {a b m n} → Matrix (a → b) m n → Matrix a m n → Matrix b m n
Nil ⓜ Nil = Nil
Cons fs fss ⓜ Cons xs xss = Cons (fs ⊙ xs) (fss ⓜ xss)

-- Define matrix addition
madd : {n m : ℕ} → Matrix ℕ m n → Matrix ℕ m n → Matrix ℕ m n
madd xss yss = (mmap _+_ xss) ⓜ yss

-- Define matrix transposition
transpose : {n m : ℕ} {a : Set} → Matrix a m n → Matrix a n m
transpose Nil = η Nil
transpose (Cons xs xss) = vmap Cons xs ⊙ transpose xss

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : ℕ} → Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to ℕ
forget : {n : ℕ} → Fin n → ℕ
forget Fz = Zero
forget (Fs i) = Succ (forget i)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : ℕ} → Fin n → Fin (Succ n)
embed Fz = Fz
embed (Fs i) = Fs (embed i)

correct : {n : ℕ} → (i : Fin n) → forget i ≡ forget (embed i)
correct Fz = Refl
correct (Fs i) = cong Succ (correct i)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : ℕ → ℕ → Set where
  LessThan : ∀ {n} k → Compare n (n + Succ k)
  Equal : ∀ {n} → Compare n n
  GreaterThan : ∀ {n} k → Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : ℕ) → Compare n m
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ m) (Succ .m)            | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : ℕ) → ℕ
difference n m  with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference m .m            | Equal = 0
difference .(m + Succ k) m | GreaterThan k = Succ k 

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x
sym Refl = Refl

trans : {a : Set} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
trans Refl Refl = Refl

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : {a : Set} → (x : a) → {y z : a} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {a : Set} (x : a) → x ≡ x
_∎ x = Refl

plusZero : (n : ℕ) → (n + 0) ≡ n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : ℕ) → Succ (n + m) ≡ (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : ℕ) → (n + m) ≡ (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m =
    ((Succ n) + m)
    ≡⟨ cong Succ (plusCommutes n m) ⟩
    Succ (m + n)
    ≡⟨ plusSucc m n ⟩
    (m + (Succ n))
    ∎

plusAssociates : (n m k : ℕ) → ((n + m) + k) ≡ (n + (m + k))
plusAssociates Zero m k = Refl
plusAssociates (Succ n) m k = cong Succ (plusAssociates n m k)

plusDistributes : (n m k l : ℕ) → ((n + m) + (k + l)) ≡ ((n + k) + (m + l))
plusDistributes n m k l =
    ((n + m) + (k + l))
    ≡⟨ plusAssociates n m (k + l) ⟩
    (n + (m + (k + l)))
    ≡⟨ cong (_+_ n) (sym (plusAssociates m k l)) ⟩
    (n + ((m + k) + l))
    ≡⟨ cong (λ x → n + (x + l)) (plusCommutes m k) ⟩
    (n + ((k + m) + l))
    ≡⟨ cong (_+_ n) (plusAssociates k m l) ⟩
    (n + (k + (m + l)))
    ≡⟨ sym (plusAssociates n k (m + l)) ⟩
    ((n + k) + (m + l))
    ∎

distributivity : (n m k : ℕ) → (n * (m + k)) ≡ ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
    ((m + k) + (n * (m + k)))
    ≡⟨ cong (_+_ (m + k)) (distributivity n m k) ⟩
    ((m + k) + ((n * m) + (n * k)))
    ≡⟨ plusDistributes m k (n * m) (n * k) ⟩
    ((m + (n * m)) + (k + (n * k)))
    ∎

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a → List a → Set where
  Base : SubList Nil Nil
  Keep : ∀ {x xs ys} → SubList xs ys → SubList (Cons x xs) (Cons x ys)
  Drop : ∀ {y zs ys} → SubList zs ys → SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} → SubList xs xs
SubListRefl {a} {Nil} = Base
SubListRefl {a} {Cons x xs} = Keep SubListRefl

SublistCons : {a : Set} {xs ys : List a} {x : a} → SubList (Cons x xs) ys → SubList xs ys
SublistCons {a} {xs} {Nil} {x} ()
SublistCons {a} {xs} {Cons x ys} {.x} (Keep x<y) = Drop x<y
SublistCons {a} {xs} {Cons x₁ ys} {x} (Drop x<y) = Drop (SublistCons x<y)

SubListTrans : {a : Set} {xs ys zs : List a} → SubList xs ys → SubList ys zs → SubList xs zs
SubListTrans Base y<z = y<z
SubListTrans (Keep x<y) (Keep y<z) = Keep (SubListTrans x<y y<z)
SubListTrans (Keep x<y) (Drop y<z) = Drop (SubListTrans (Keep x<y) y<z)
SubListTrans (Drop x<y) (Keep y<z) = Drop (SubListTrans x<y y<z)
SubListTrans (Drop x<y) (Drop y<z) = Drop (SubListTrans x<y (SublistCons y<z))

-- Note that this function doesn't seem to terminate,
-- but since we have to show absurdity, we can't actually terminate!
ConsNotSubList : {a : Set} {xs : List a} {x : a} → SubList (Cons x xs) xs → Empty
ConsNotSubList {a} {Cons x ys} {.x} (Keep xx<x) = ConsNotSubList xx<x
ConsNotSubList {a} {Cons y ys} {x} (Drop xx<x) = ConsNotSubList (SublistCons xx<x)

SubListAntiSym : {a : Set} {xs ys : List a} →  SubList xs ys → SubList ys xs → xs ≡ ys
SubListAntiSym {a} {.Nil} {.Nil} Base Base = Refl
SubListAntiSym {a} {(Cons x _)} {.(Cons x _)} (Keep x<y) (Keep y<x) = cong (Cons x) (SubListAntiSym x<y y<x)
SubListAntiSym {a} {.(Cons _ _)} {.(Cons _ _)} (Keep x<y) (Drop y<x) = magic (ConsNotSubList (SubListTrans y<x x<y))
SubListAntiSym {a} {xs} {.(Cons _ _)} (Drop x<y) y<x = magic (ConsNotSubList (SubListTrans y<x x<y))

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data _≤_ : ℕ → ℕ → Set where
  0≤n : ∀ {n} → Zero ≤ n
  n+1≤m+1 : ∀ {n m} → n ≤ m → (Succ n) ≤ (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

≤-refl : (n : ℕ) → n ≤ n
≤-refl Zero = 0≤n
≤-refl (Succ n) = n+1≤m+1 (≤-refl n)

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans 0≤n b = 0≤n
≤-trans (n+1≤m+1 a) (n+1≤m+1 b) = n+1≤m+1 (≤-trans a b)

≤-antiSym : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-antiSym 0≤n 0≤n = Refl
≤-antiSym (n+1≤m+1 a) (n+1≤m+1 b) = cong Succ (≤-antiSym a b)

-- Given the following function:
_≤?_ : ℕ → ℕ → 𝟚
Zero ≤? y = True
Succ x ≤? Zero = False
Succ x ≤? Succ y = x ≤? y

-- Now show that this function behaves as the LEQ data type

soundness≤ : {n m : ℕ} → n ≤ m → So (n ≤? m)
soundness≤ 0≤n = unit
soundness≤ (n+1≤m+1 n≤m) = soundness≤ n≤m

completeness≤ : (n m : ℕ) → So (n ≤? m) → n ≤ m
completeness≤ Zero m n≤m = 0≤n
completeness≤ (Succ n) Zero ()
completeness≤ (Succ n) (Succ m) n≤m = n+1≤m+1 (completeness≤ n m n≤m)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
¬_ : Set → Set
¬ P = P → Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} → P → ¬ (¬ P)
notNotP p notP = notP p

-- The reverse does not hold: ¬ (¬ P) does not imply P

-- Similarly, P or ¬ P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data _∨_ (a b : Set) : Set where
  Inl : a → a ∨ b
  Inr : b → a ∨ b

orCase : {a b c : Set} → (a → c) → (b → c) → (a ∨ b) → c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} → ¬ ¬ (P ∨ (¬ P))
notNotExcludedMiddle notExcludedMiddle =
    let notP p = notExcludedMiddle (Inl p)
     in notExcludedMiddle (Inr notP)

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.

proofByContradiction = {P : Set} → ¬ ¬ P → P
excludedMiddle = {P : Set} → P ∨ (¬ P)
impliesToOr = {P Q : Set} → (P → Q) → (¬ P) ∨ Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


step1 : proofByContradiction → excludedMiddle
step1 dn = dn notNotExcludedMiddle

step2 : excludedMiddle → impliesToOr
step2 em pToQ = orCase (λ p → Inr (pToQ p)) Inl em

step3 : impliesToOr → proofByContradiction
step3 ito {P} h =
    let excludedMiddle = ito (λ p → p)
    in orCase (λ nP → magic (h nP)) (λ p → p) excludedMiddle

-- HARDER: show that these are equivalent to Peirce's law:
peircesLaw = {P Q : Set} → ((P → Q) → P) → P

peirceToContradiction : peircesLaw → proofByContradiction
peirceToContradiction pl nnP = pl (λ nP → magic (nnP nP))

excludedMiddleToPeirce : excludedMiddle → peircesLaw
excludedMiddleToPeirce em pToQToP = orCase
    (λ p → p)
    (λ nP → pToQToP (λ p → magic (nP p)))
    em

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

-- We can also compile such expressions to stack machine code
-- The arguments to Cmd represent:
-- the number of elements in the input stack (modified by ADD)
-- the number of elements in the output stack (modified by PUSH and ADD)
data Cmd : (i o : ℕ) → Set where
  -- stop execution and return the current stack
  HALT : {i : ℕ} → Cmd i i
  -- push a new number on the stack
  PUSH : {i o : ℕ} → ℕ → Cmd (Succ i) o → Cmd i o
  -- replace the top two elements of the stack with their sum
  ADD : {i o : ℕ} → Cmd (Succ i) o → Cmd (Succ (Succ i)) o

Stack : ℕ → Set
Stack = Vec ℕ

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...

exec : {i o : ℕ} → Cmd i o → Stack i → Stack o
exec HALT xs = xs
exec (PUSH x c) xs = exec c (Cons x xs)
exec (ADD c) (Cons x₀ (Cons x₁ xs)) = exec c (Cons (x₀ + x₁) xs)

compile' : {i o : ℕ} → Cmd (Succ i) (Succ o) → Expr → Cmd i (Succ o)
compile' c (Add e₀ e₁) = compile' (compile' (ADD c) e₀) e₁
compile' c (Val x) = PUSH x c

-- Define a compiler from expresions to instructions
compile : {n : ℕ} → Expr → Cmd n (Succ n)
compile = compile' HALT

correctness' : {i o : ℕ} (c : Cmd (Succ i) (Succ o)) (e : Expr) (s : Stack i) →
  exec c (Cons (eval e) s) ≡ exec (compile' c e) s
correctness' c (Add e₀ e₁) s =
    exec c (Cons (eval e₀ + eval e₁) s)
    ≡⟨ correctness' (ADD c) e₀ (Cons (eval e₁) s) ⟩
    exec (compile' (ADD c) e₀) (Cons (eval e₁) s)
    ≡⟨ correctness' (compile' (ADD c) e₀) e₁ s ⟩
    exec (compile' (compile' (ADD c) e₀) e₁) s
    ∎
correctness' c (Val x) s = Refl

-- And prove your compiler correct
correctness : {n : ℕ} (e : Expr) (s : Stack n) →
  Cons (eval e) s ≡ exec (compile e) s
correctness = correctness' HALT

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
