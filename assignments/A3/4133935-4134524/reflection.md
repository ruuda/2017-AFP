Evidence translation:
We forgot to put the Monad constraint in the MonadReader dict
Similarly we forgot to put the Functor constraint in the Applicative dict.

Though finally, the result is the same, it is not so tidy (and not a direct evidence translation)


Tail recursion:
OK

Fix:
OK

Nested:

2.4.1: Wouter said it was correct, eventhough the compiler crashed! Fixed with {-#NOINLINE#-}
2.4.2: Correct
2.4.3: Apparently our solution is too complex. Compared to the one we graded.  We could've left out the lift constructions


We would grade ourselves: 8.5
