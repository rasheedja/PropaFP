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
		0
		(sin 0)))
(assert 
	(<= 
		(cos (* 4.0 (atan 1.0)))
		(* -1 1)))
(assert 
	(= 
		0
		(sin (* 4.0 (atan 1.0)))))
(assert 
	(= 
		0
		(cos (* (/ 5 10) (* 4.0 (atan 1.0))))))
(assert 
	(<= 
		1
		(sin (* (/ 5 10) (* 4.0 (atan 1.0))))))
(assert 
	(not 
		(<= 
			(* (* -1 48) (/ 1 100))
			(- (- x (/ (* (* x x) x) 6)) (/ 1769513 100000000000000)))))
(check-sat)
(get-model)
(exit)
