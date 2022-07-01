(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= (/ -1 2) x))
(assert (<= x (/ 1 2)))
(assert 
	(not 
		(and 
			(or 
				(not 
					(<= 
						0
						(+ (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000))))
				(<= 
					(+ (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000))
					(* 25889 (/ 1 100000000)))) 
			(or 
				(not 
					(not 
						(<= 
							0
							(- (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000)))))
				(<= 
					(+ (* -1 (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6))))) (/ 1769513 100000000000000))
					(* 25889 (/ 1 100000000)))))))
(check-sat)
(get-model)
(exit)
