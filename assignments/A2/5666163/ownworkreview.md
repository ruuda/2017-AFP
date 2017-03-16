---
## Monads

The code looks very messy but i believe that this kind of code is very messy by
its nature. Because the purpose is to abstract away patterns and messy code, you
write it down somewhere, in a module, provide documentation, and then people
don't have to write messy code anymore.

Considering the review i got from the others, there is a bug in my implementaion
of annotate, i think this has to do with lazy evaluation(?)
- 5 pt

i did not do any bonus questions. These assignments already cost enough time as
is.
+ 0

---
## Foldable
No remarks, i don't really agree with having to implement fold = foldMap id as
well because there is a default implementation that takes care of that.

---
## Teletype IO

I missed the specification that simulate has to return output values of the
program instead of unconsumed input values. I don't know exectly why i missed it
(probably because i tried to implement _something_ by looking only at the type)
- 5 pt

MonadState law of get . put does not hold so when i think about it now this is
really wrong.
- 5 pt

---
## Stacks
Everything works, no remarks.

Final

Monads     : 30 / 35
Foldable   : 30 / 30
Stacks     : 10 / 10
TeletypeIO : 15 / 25
             ------- +
             85 / 100
