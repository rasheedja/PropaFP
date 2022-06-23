(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= (/ -6851933 8388608) x))
(assert (<= x (/ 6851933 8388608)))
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
			(+ (+ (+ (* (+ (* (+ (* (+ (* (/ 6699511 274877906944) (* x x)) (* -1 (/ 2982539 2147483648))) (* x x)) (/ 2796199 67108864)) (* x x)) (* -1 (/ 1 2))) (* x x)) 1) (* -1 (cos x))) (/ 3518109 50000000000000))
			(/ 1 10000))))
(check-sat)
(get-model)
(exit)
