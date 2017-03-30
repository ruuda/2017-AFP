

Generics:

Though you made a nice generic Read.  The exercise states that you
should implement a proper Read. That is the inverse of Show. 
We know that this is a lot of work, so you could decide to make
some compromises like not supporting Records, or swap out the
special tuple and list syntax ( (a,b) , [a,b,c]) with explicit
constructors.

We think at least getting constructor names out of the type information
is a relevant part of the exercise, which is missing here. How this
is done, could have been extracted from the hint in the exercise,
namely look at the Generic.Deriving.Show module.  (See the
Constructor typeclass in GHC.Generics)

In practice, this means your instance(s) for the M1 constructor
should be more interesting.


Partial:

Too bad you were not able to find a monoid-abiding merge. We think
it _is_ possible though. (at least, quickcheck agrees with us):


```haskell
instance Alternative Partial where
  empty = Later empty
  (Now x) <|> _ = Now x
  (Later p) <|> q = Later $
    case q of
      Now q -> Now q
      Later q -> p <|> q

assoc_prop :: Partial Int -> Partial Int -> Partial Int -> Property
assoc_prop x y z = ((x<|>y)<|>z)===(x<|>(y<|>z))
```

Trie:

The following test case is true. it should be false because the trie contains
no values, but is not equal to Trie.empty. But the assignment itself is wrong
in this as well, so we do not deduct points for it:

```haskell
    it "topkek" $ do
      Trie.valid  (Trie.Node Nothing (Map.singleton 'a' Trie.empty)) `shouldBe` True
```


You forgot to do the UnsafeIO exercise!!


Final Score:

8.5
