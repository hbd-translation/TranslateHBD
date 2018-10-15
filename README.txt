Isabelle Formalization of Mechanically Proving Determinacy of 
Hierarchical Block Diagram Translations

These files contain the theories for "Mechanically Proving 
Determinacy of  Hierarchical Block Diagram Translations"

The files are for Isabelle 2018. 
To see the files open them in Isabelle jedit. 

 
The folder contains the following files:
  - ListProp.thy (properties about permutations and substitutions 
		on lists)

  - HBDAlgebra.thy (HBD Algebra excluding axiom 16)

  - ExtendedHBDAlgebra.thy (HBD Algebra - all axioms)
  
  - Diagrams.thy (io-diagrams and properties)
  
  - HBDTranslationProperties.thy Further properties of io-diagrams used for 
		the algorithms)
  
  - ../RefinementReactive/Refinement.thy (Refinement calculus and Hoare rules)
  
  - HBDTranslationsUsingFeedback.thy (the nondeterministic algorithm using feedback)
  
  - FeedbacklessHBDTranslation.thy (the feedbackless algorithm)
  
  - Constructive.thy (the model of constructive functions)
  
  - ConsFuncHBDModel.thy (proof that the set of constructive functions is a model 
		for the HBD Algebra)
		
  - README.txt (this file)
  
  - document.pdf (the pdf document of the theories)
  
  - session_graph.pdf (a pdf file with the theory dependency graph)
  
Next is a list of the results from the paper, and their location 
the theory files.

3.1 Constructive functions
  - file Constructive.thy
  
3.2 Refinement Calculus and Hoare Total Correctness Triples
  - files Refinement.thy
  
  Lemma 3.1 - Lemma hoare_demonic (Refinement.thy)
  Lemma 3.2 - Lemma hoare_while_a (Refinement. thy) - more general
  
5 An Abstract Algebra for Hierarchical Block Diagrams
  - files HBDAlgebra.thy and ExtendedHBDAlgebra.thy
  
  Theorem 5.1 - interpretation func: BaseOperation ... (ConsFuncHBDModel.thy)
  
6 The abstract Algorithm and its Determinacy
  - file HBDTranslationsUsingFeedback.thy with many results in other files
  
  Definition 6.1 - definition io_diagram (Diagrams.thy)
  Definition 6.2 - definition Var A B (Diagrams.thy)
  Arb(a) - definition Arb t (HBDAlgebra.thy)
  [x \leadsto y] - primrec switch (HBDAlgebra.thy)
  Definition 6.3 - definition  Comp (Diagrams.thy)
  Lemma 6.4 - lemma io_diagram_Comp (Diagrams.thy)
  Lemma 6.5 - lemma Comp_assoc_new (Diagrams.thy)
  Definition 6.6 - definition Parallel (Diagrams.thy)
  Lemma 6.7 - lemma io_diagram_Parallel and lemma Parallel_assoc_gen (Diagrams.thy)
  Definition 6.8 - definition FB (Diagrams.thy)
  Lemma 6.9 - lemma Type_ok_FB (Diagrams.thy)
  Alg. 1 - definition TranslateHBD (HBDTranslationsUsingFeedback.thy)
  Definition 6.10 -  definition in_out_equiv (Diagrams.thy)
  Lemma 6.11 - lemmas in_out_equiv_refl, in_out_equiv_sym, in_out_equiv_tran,
		in_out_equiv_Parallel (Diagrams.thy)
		in_out_equiv_FB (HBDTranslationProperties.thy)
		distinct_Par_equiv_a (HBDTranslationsUsingFeedback.thy)
  Theorem 6.12 - theorem FeedbackSerial (HBDTranslationProperties.thy)
  Theorem 6.13 - theorem CorrectnessTranslateHBD (HBDTranslationsUsingFeedback.thy)
  
  Theorem 7.1 - is not in the theory files, but it is a trivial consequence
		of Theorem 6.13.
  
  
8 Feedbackless Algorithm  
  - file FeedbacklessHBDTranslation.thy
		
  - Definition 8.1 - definition deterministic (HBDAlgebra.thy)
  - Lemma 8.2 - lemmas deterministic_switch, deterministic_comp,
		deterministic_par (HBDAlgebra.thy)
  - Definition 8.3 - definitions io_rel, IO_Rel, loop_free (Diagram.thy)
  - Lemma 8.4 - lemma deterministic_split (HBDAlgebra.thy) (only for pair)
  - Definition 8.7 - definition internal (Diagram.thy)
  - Definition 8.8 - definitions CompA, fb_less_step (Diagram.thy)
  - Lemma 8.9 - Lemma 8.9 (HBDTranslationProperties.thy) (stronger result)
  - Lemma 8.10 - lemmas ok_fbless_fb_less_step internal_fb_less_step
			(FeedbacklessHBDTranslation.thy)
  - Definition 8.11 -  primrec fb_less (Diagram.thy)
  - Theorem 8.12 - theorem fbless_correctness (FeedbacklessHBDTranslation.thy)
		(equivalent formulation)
  - Alg. 2 - definition "TranslateHBDFeedbackless (FeedbacklessHBDTranslation.thy)
  - Theorem 8.13 - theorem TranslateHBDFeedbacklessCorrectness
		(FeedbacklessHBDTranslation.thy)
	Theorem 8.14 - is not in the theories, but it is a trivial consequence
		of the other results.
  
  
