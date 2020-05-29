# ternary.agda

This library adds an hierachy of algebraic structures on ternary relations.
The focus of the library are /proof relevant separation algebras/, which are partial commutative monoids.
We define separating conjunction and magic wand and program with it!

On top of the ternary relations hierarchy we define monads that are strong over the separating conjunction.
This enables programming with linear state, and we get nice types for their operations.
For a linear session-typed language we implement for example: 

```
  newChan  : ε[ State? Channels (Endptr α ✴ Endptr (α ⁻¹)) ]
  receive? : ∀[ Endptr (a ¿ β) ⇒ State? Channels (Val a ✴ Endptr β) ]
  send!    : ∀[ Endptr (a ! β) ⇒ Val a ─✴ State? Channels (Endptr β) ]
```

To get an idea of what this contains and how to use it, see `Everything.agda`.

## Publications

*Talk*: [at Edinburgh seminar](https://www.youtube.com/watch?v=9WmOmpyz_qo) 

*Paper*: In [Typed interpreters of linear, session-typed languages using proof relevant separation logic in Agda](https://dl.acm.org/doi/pdf/10.1145/3372885.3373818)
we describe how we can avoid the bookkeeping for the interpretation of languages with linear state using this library
for programming with separation logic. We show how to type and 
[interpret](https://github.com/ajrouvoet/sessions.agda/blob/master/src/Sessions/Semantics/Expr.agda) a [linear, session-typed language](https://github.com/ajrouvoet/sessions.agda/blob/master/src/Sessions/Syntax/Expr.agda) as a case study.
