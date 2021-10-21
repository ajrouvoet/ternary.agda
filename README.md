# ternary.agda

This library adds an hierachy of algebraic structures on ternary relations.
The focus of the library are *proof relevant separation algebras* and the induced
(separation) logic on PRSA-indexed Sets. We have used this setup to develop
*resource-aware* version of various commonplace data-structures, as well as
resource-aware computational structures (e.g., monads). The aim of the library
is to make programming with these well-known structures as familiar as possible,
despite the fact that our programs must preserve the invariants of the resource.

What exactly can be treated as a "resource" in this setting is up for debate and experiment.
In traditional separation logic it is usually (locations in) memory. We personally like
to treat contexts in syntax typing as a resource. This has enabled us to give very
elegant typing rules for languages with linearity constraints. But also computation costs could
perhaps be captured as a resource, or probabilistic independence, or...

To get an idea of what this contains and how to use it, see `Everything.agda`.

## Taks and publications

- [Thesis](https://ajrouvoet.github.io/files/thesis.pdf)
- [Talk at Edinburgh seminar](https://www.youtube.com/watch?v=9WmOmpyz_qo)
- [Talk at POPL 21](https://www.youtube.com/watch?v=LqudAqCmecQ&list=PLNQG1JKYIPeQFNlJNKT9EmbzCdbdK-br_&index=2)

- In [Typed interpreters of linear, session-typed languages using proof relevant separation logic in Agda](https://dl.acm.org/doi/pdf/10.1145/3372885.3373818)
we describe how we can avoid the bookkeeping for the interpretation of languages with linear state using this library. 
We show how to type and [interpret](https://github.com/ajrouvoet/sessions.agda/blob/master/src/Sessions/Semantics/Expr.agda) a [linear, session-typed language](https://github.com/ajrouvoet/sessions.agda/blob/master/src/Sessions/Syntax/Expr.agda) as a case study.

- In [Intrinsically Typed Compilation with Nameless Labels](https://ajrouvoet.github.io/files/popl-21-preprint.pdf) we show how to intrinsically type and compile to bytecode with labels in a compositional manner. That is, compiling without the usual state to generate labels, and capturing label uniqueness in bytecode compositionally.
