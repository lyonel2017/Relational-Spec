#  Coq formalization of relational properties in a *While* Language

This repository contains a **Coq** formalization of relational properties and
their proof using verification condition generator. A state of the art *While* language
is used as a basis.

The project structure is a follows:

* [Sigma.v]() defines the memory state of a program
* [Loc.v]()  defines locations
* [Proc.v]() defines procedure names
* [Aexp.v]() defines arithmetic expressions
* [Bexp.v]() defines boolean expresisons
* [Com.v]() defines command
* [Inliner.v]() defines inliner for procedure
* [Hoare_Triple.v]() defines Hoare Triples
* [Vcg.v]() and [Vcg_Opt.v]() defines respectively a verification condition genrator
  and a optimized version.
* [Correct.v]() defines that a Hoare Triples can be verified using  verification
  condition generator.
* [Rela.v]() defines relational properties and that relational properties can
  be verified using verification condition generator.

# TODO

* Formalization of frame rule
* Formalization of contruct `\at` in assertions (in branch history)
* Modular memory model of the verification condition generator
