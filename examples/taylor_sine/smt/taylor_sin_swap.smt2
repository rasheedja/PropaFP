(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= (/ -1 2) x))
(assert (<= x (/ 1 2)))
(assert 
	(<= 
		1
		(cos 0)))
(assert 
	(= 
		(sin 0)
		0))
(assert 
	(<= 
		(cos (* 4.0 (atan 1.0)))
		(* -1 1)))
(assert 
	(= 
		(sin (* 4.0 (atan 1.0)))
		0))
(assert 
	(= 
		(cos (* (/ 5 10) (* 4.0 (atan 1.0))))
		0))
(assert 
	(<= 
		1
		(sin (* (/ 5 10) (* 4.0 (atan 1.0))))))
(assert 
	(not 
		(and 
			(or 
				(not 
					(<= 
						0
						(+ (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000))))
				(<= 
					(* 25889 (/ 1 100000000))
					(- (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000)))) 
			(or 
				(not 
					(not 
						(<= 
							0
							(- (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6)))) (/ 1769513 100000000000000)))))
				(<= 
					(* 25889 (/ 1 100000000))
					(- (* -1 (+ (sin x) (* -1 (- x (/ (* (* x x) x) 6))))) (/ 1769513 100000000000000)))))))
(check-sat)
(get-model)
(exit)
