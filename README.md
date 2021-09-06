#  Coq formalization of Relational Properties in a *While* Language

This repository contains a [Coq](https://coq.inria.fr/) formalization of relational properties and
their proof using verification condition generator. A state of the art *While* language
is used as a basis.

The project structure is a follows:

* **Loc.v**:  definition of locations
* **Sigma.v**: definition of memory state
* **Proc.v**: definition of procedure names
* **Aexp.v**: definition of arithmetic expressions
* **Bexp.v**: definition of boolean expressions
* **Com.v**: definition of commands
* **Inliner.v**: definintion of inliner for procedures
* **Hoare_Triple.v**: definintion of Hoare Triples
* **Vcg.v** and **Vcg_Opt.v**: definition of respectively a naive verification condition genrator
  and a optimized version.
* **Correct.v**: proof that Hoare Triples can be verified using verification condition generator.
* **Rela.v**: definition of relational properties.
* **Vcg_Rela.v**: definition of a verification condition generator for Relational Properties using
  the verification condition generator define in **Vcg.v**
* **Corect_Vcg.v**: proofs that Relational Properties can be verified using verification condition generator.
* **Examples.v**: some examples


# Extended formalization

Branch *history* contain a verification condition generator allowing
to refer to previouse states.

<!-- * Formalization of frame rules -->
<!-- * Command Goto and Labels -->
<!-- * Modular memory model for the verification condition generator -->
