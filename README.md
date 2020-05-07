# ternary.agda

This library adds an hierachy of algebraic structures on ternary relations.
The focus of the library are /proof relevant separation algebras/, which are partial commutative monoids.
We define separating conjunction and magic wand and program with it!

On top of the ternary relations hierarchy we define monads that are strong over the separating conjunction.
This enables programming with linear state, for example.

## Publications

[Talk](https://www.youtube.com/watch?v=9WmOmpyz_qo) 

In [Typed interpreters of linear, session-typed languages using proof relevant separation logic in Agda](https://dl.acm.org/doi/pdf/10.1145/3372885.3373818)
we describe how we can avoid the bookkeeping for the interpretation of languages with linear state using this library
for programming with separation logic. We show how to type and 
[interpret](https://github.com/ajrouvoet/sessions.agda/blob/master/src/Sessions/Semantics/Expr.agda) a linear, session-typed language as a case study.
