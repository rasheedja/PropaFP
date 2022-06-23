(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= (/ 0 1) x))
(assert (<= x (/ 511 1)))
(assert 
	(not 
		(<= 
			(+ x (* -1 (to_int_rna x)))
			(* 500000001 (/ 1 1000000000)))))
(check-sat)
(get-model)
(exit)
