# PER model for System T
This repository contains a mechanized PER model for Gödel's System T
(call-by-name variant) in Coq. The relational model is more powerful
than the predicate model since it allows one to prove that $\lambda
x. x$ and $\lambda x . x + 0$ are logically equivalent functions from
`Nat` to `Nat`.

I find it slightly trickier to mechanize call-by-name version than the
call-by-value version since the base case for the `Nat` type becomes
slightly more complicated.
