Isabelle Formalization of a Nondeterministic and Abstract 
Algorithm for Translating Hierarchical Block Diagrams

These files contain the theories for "A Nondeterministic and Abstract 
Algorithm for Translating Hierarchical Block Diagrams"

The files are for Isabelle 2016-1. 
To see the files open them in Isabelle jedit. 
The folder contains the following files:

AbstractOperations.thy - the axioms of HBD algebra and also 
  many properties. The general switch is also defined here.

Model.thy - constructive function model for the HBD algebra
  Theorem 1 from the paper is proved in this file: search for "interpretation func".

Abstract.thy - proves the main results for the correctness of the
  nondeterministic and feedbackless algorithms. The main results are:

  Lemma 4 of the paper is proved in:
    - lemma in_out_equiv_refl
    - lemma in_out_equiv_sym
    - lemma in_out_equiv_tran
    - lemma in_out_equiv_Parallel
    - lemma in_out_equiv_FB

  Theorem 2 of the paper is proved in:
    - theorem FeedbackSerial
    - theorem FB_idemp
	
Algorithm.thy - defines the nondeterministic and abstract algorithm 
  and proves its correctness. The algorithm is defined using predicate
  transformers (defined in Refinement.thy) and its proof is done using 
  Hoare total corectness rules (defined in Hoare.thy).
  
  The algorithm:
    - definition TranslateHBD
	
  Theorem 3
	- theorem CorrectnessTranslateHBD

ListProp.thy - some definitions and properties for lists
Constructive.thy - least fixpoint for cpos
Refinement.thy - refinement calculus
Hoare.thy - Hoare rules for basic statements (assert, assume, demonic 
  update, demonic choice, if, while, sequential composition)
