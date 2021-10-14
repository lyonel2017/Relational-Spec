#  Coq formalization of the verification of Relational Properties

This repository contains a [Coq](https://coq.inria.fr/) formalization and proof of soundness for :

* recursive Hoare triple verification with a verification condition generator on a simple language with procedures and aliasing;
* a method for verifying relational properties using a verification condition generator, without relying on code transformation (such as
  self-composition) or making additional separation hypotheses in case of aliasing;

## The project structure

* **Loc.v**:  definition of locations.
* **Sigma.v**: definition of memory state.
* **Proc.v**: definition of procedure names.
* **Aexp.v**: definition of arithmetic expressions.
* **Bexp.v**: definition of boolean expressions.
* **Com.v**: definition of commands and proof of useful property.
* **Inliner.v**: definintion of inliner for procedures and proof of useful property.
* **Hoare_Triple.v**: definintion of Hoare Triples and proof of useful property.
* **Vcg.v** and **Vcg_Opt.v**: definition of respectively a naive verification condition genrator and a optimized version and proof of useful property.
* **Correct.v**: proof that Hoare Triples can be verified using verification condition generator.
* **Rela.v**: definition of relational properties and proof of useful property.
* **Vcg_Rela.v**: definition of a verification condition generator for Relational Properties using the verification condition generator define in **Vcg.v**
                  and proof of useful property.
* **Correct_Rela.v**: proofs that Relational Properties can be verified using verification condition generator.
* **Examples.v**: some examples.
