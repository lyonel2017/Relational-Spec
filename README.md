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
* [Vcg.v]() and [Vcg_Opt.v]() defines respectively a naive verification condition genrator
  and a optimized version.
* [Correct.v]() defines that a Hoare Triples can be verified using  verification
  condition generator.
* [Rela.v]() defines relational properties and that relational properties can
  be verified using verification condition generator.
* [Examples.v]() defines some examples


# TODO
* Formalization of contruct `\at` in assertions (in branch history)

<!-- "la" est une list de tuple label*sigma: les duplications sont autorisé et il est laissé a -->
<!-- l'utilisateur de ne pas mettre de label double pour qu'il puisse sans sortir. -->
<!-- Voire sans label, qui sont la juste pour nous aidé, cela régle aussi le problem d'unisité -->

<!-- Finalement pas de label. Une assertion est une fonction list sigma -> Prop -->
<!-- Precondition est une fonction sigma  -> Prop -->
<!-- Postcondition est une fonction sigma -> sigma -> Prop -->

<!-- Une régle de décomposition sur la sequence n'est probablement pas possible -->
<!-- car l'historique est connecté -->

* Formalization of frame rules
* Command Goto and Labels
* Modular memory model for the verification condition generator
