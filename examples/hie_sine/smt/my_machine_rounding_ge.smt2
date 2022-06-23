(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= (/ 0 1) x))
(assert (<= x (/ 511 1)))
(assert 
	(not 
		(<= 
			(* (* -1 500000001) (/ 1 1000000000))
			(+ x (* -1 (to_int_rna x))))))
(check-sat)
(get-model)
(exit)
