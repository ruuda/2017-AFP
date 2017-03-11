## Foldable

Foldable looks good overall everything works as expected.

you could have implemented fold like

  fold (a :> as) = v `mappend` foldMap fold as

it's equivalent, but a little nicer.

---
## Stacks

Stack based language looks good too. I used GADT's to encode vectors on the type
level but i see that this works too.

---
## Teletype IO

Everything looks good and works as expected.

You need the explicit applicative instance because applicative is now a
superclass of monad, it used to be the other way around.

---
## StateMonadPlus

Implementing all the code to make the statemonadplus work is messy by its very
nature. Everything does seem to work and i could not discover any bugs. You even
answered some bonus questions although i don't know how to reward any points for
that because you already have the maximum points.

breakdown
Foldable       : 30 /  30
Stacks         : 10 /  10
Teletype IO    : 25 /  25
StateMonadPlus : 35 /  35
(bonus ques...):  3 /   4
                -------- +
                100 / 100 + 3 bonus questions

