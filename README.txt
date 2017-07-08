Isabelle Formalization of Mechanically Proving Determinacy of 
Hierarchical Block Diagram Translations

These files contain the theories for "Mechanically Proving 
Determinacy of  Hierarchical Block Diagram Translations"

The files are for Isabelle 2016-1. 
To see the files open them in Isabelle jedit. 

The theories are not optimized, and require quite much
time to be processed. In batch mode, it takes about 
6 minutes to process them all on an AMD A8-5600K processor
(not very powerful).

 
The folder contains the following files:
  - ListProp.thy (properties about permutations and substitutions 
		on lists)
  - AlgebraFeedbackless.thy (HBD Algebra except axiom 16)
  - AlgebraFeedback.thy (HBD Algebra including all axioms)
  - DiagramFeedbackless.thy (io-diagrams and properties, 
		not asumming axiom 16)
  - Feedbackless.thy (Further properties of io-diagrams used for 
		the feedbackless algorithm)
  - FeedbacklessPerm.thy (Properties about the independence of the 
		order of internal variables in the final result of the 
		feedbackless algorithm)
  - Feedback.thy (Properties required for proving the nondeterministic 
		algorithm)
  - Refinement.thy (Refinement calculus)
  - Hoare.thy (Hoare rules, besed on refinement calculus)
  - AlgorithmFeedback.thy (the nondeterministic algorithm)
  - AlgorithmFeedbackless.thy (the feedbackless algorithm)
  - Constructive.thy (the model of constructive functions)
  - Model.thy (proof that the set of constructive functions is a model 
		for the HBD Algebra)
  - README.txt (this file)
  - document.pdf (the pdf document of the theories)
  - session_graph.pdf (a pdf file with the theory dependency graph)
  
Next is a list of the results from the paper, and their location 
the theory files.

3.1 Constructive functions
  - file Constructive.thy
  
3.2 Refinement Calculus and Hoare Total Correctness Triples
  - files Refinement.thy and Hoare.thy
  
  Lemma 3.1 - Lemma hoare_demonic (Hoare.thy)
  Lemma 3.2 - Lemma hoare_while_a (Hoare. thy) - more general
  
5 An Abstract Algebra for Hierarchical Block Diagrams
  - files AlgebraFeedbackless.thy and AlgebraFeedback.thy
  
  Theorem 5.1 - interpretation func: BaseOperation ... (Model.thy)
  
6 The Aabstract Algorithm and its Determinacy
  - file AlgorithmFeedback.thy with many results in other files
  
  Definition 6.1 - definition io_diagram (DiagramFeedbackless.thy)
  Definition 6.2 - definition Var A B (DiagramFeedbackless.thy)
  Arb(a) - definition Arb t (AlgebraFeedbackless.thy)
  [x \leadsto y] - primrec switch (AlgebraFeedbackless.thy)
  Definition 6.3 - definition  Comp (DiagramFeedbackless.thy)
  Lemma 6.4 - lemma io_diagram_Comp (DiagramFeedbackless.thy)
  Lemma 6.5 - lemma Comp_assoc_new (DiagramFeedbackless.thy)
  Definition 6.6 - definition Parallel (DiagramFeedbackless.thy)
  Lemma 6.7 - lemma io_diagram_Parallel and lemma Parallel_assoc_gen (DiagramFeedbackless.thy)
  Definition 6.8 - definition FB (DiagramFeedbackless.thy)
  Lemma 6.9 - lemma Type_ok_FB (DiagramFeedbackless.thy)
  Alg. 1 - definition TranslateHBD (AlgorithmFeedback.thy)
  Definition 6.10 -  definition in_out_equiv (DiagramFeedbackless.thy)
  Lemma 6.11 - lemmas in_out_equiv_refl, in_out_equiv_sym, in_out_equiv_tran,
		in_out_equiv_Parallel (DiagramFeedbackless.thy)
		in_out_equiv_FB (Feedback.thy)
		distinct_Par_equiv_a (AlgorithmFeedback.thy)
  Theorem 6.12 - theorem FeedbackSerial (Feedback.thy)
  Theorem 6.13 - theorem CorrectnessTranslateHBD (AlgorithmFeedback.thy)
  
  Theorem 7.1 - is not in the theory files, but it is a trivial consequence
		of Theorem 6.13.
  
  
8 Feedbackless Algorithm  
  - file AlgorithmFeedbackless.thy with many results in other files
		with Feedbackless in the name.
		
  - Definition 8.1 - definition "deterministic (AlgebraFeedbackless.thy)
  - Lemma 8.2 - lemmas deterministic_switch, deterministic_comp,
		deterministic_par (AlgebraFeedbackless.thy)
  - Definition 8.3 - definitions io_rel, IO_Rel, loop_free (DiagramFeedbackless.thy)
  - Lemma 8.4 - lemma deterministic_split (AlgebraFeedbackless.thy) (only for pair)
  - Definition 8.7 - definition internal (DiagramFeedbackless.thy)
  - Definition 8.8 - definitions CompA, fb_less_step (DiagramFeedbackless.thy)
  - Lemma 8.9 - Lemma 8.9 (FeedbacklessPerm.thy) (stronger result)
  - Lemma 8.10 - lemmas ok_fbless_fb_less_step internal_fb_less_step
			(AlgorithmFeedbackless.thy)
  - Definition 8.11 -  primrec fb_less (DiagramFeedbackless.thy)
  - Theorem 8.12 - theorem fbless_correctness (AlgorithmFeedbackless.thy)
		(equivalent formulation)
  - Alg. 2 - definition "TranslateHBDFeedbackless (AlgorithmFeedbackless.thy)
  - Theorem 8.13 - theorem TranslateHBDFeedbacklessCorrectness
		(AlgorithmFeedbackless.thy)
	Theorem 8.14 - is not in the theories, but it is a trivial consequence
		of the other results.
  
  