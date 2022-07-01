(set-logic QF_NRA)
(declare-fun onesin1 () Real)
(assert (<= (/ -8053065 16777216) onesin1))
(assert (<= onesin1 (/ 1006633 2097152)))
(declare-fun twosin1 () Real)
(assert (<= (/ -8053065 16777216) twosin1))
(assert (<= twosin1 (/ 1006633 2097152)))
(declare-fun x () Real)
(assert (<= (/ -1 2) x))
(assert (<= x (/ 1 2)))
(assert 
	(<= 
		(* (* -1 48) (/ 1 100))
		onesin1))
(assert 
	(<= 
		onesin1
		(* 48 (/ 1 100))))
(assert 
	(or 
		(not 
			(<= 
				0
				(+ (sin x) (* -1 onesin1))))
		(<= 
			(+ (sin x) (* -1 onesin1))
			(* 25889 (/ 1 100000000)))))
(assert 
	(or 
		(not 
			(not 
				(<= 
					0
					(+ (sin x) (* -1 onesin1)))))
		(<= 
			(* -1 (+ (sin x) (* -1 onesin1)))
			(* 25889 (/ 1 100000000)))))
(assert 
	(<= 
		(* (* -1 48) (/ 1 100))
		twosin1))
(assert 
	(<= 
		twosin1
		(* 48 (/ 1 100))))
(assert 
	(or 
		(not 
			(<= 
				0
				(+ (sin onesin1) (* -1 twosin1))))
		(<= 
			(+ (sin onesin1) (* -1 twosin1))
			(* 25889 (/ 1 100000000)))))
(assert 
	(or 
		(not 
			(not 
				(<= 
					0
					(+ (sin onesin1) (* -1 twosin1)))))
		(<= 
			(* -1 (+ (sin onesin1) (* -1 twosin1)))
			(* 25889 (/ 1 100000000)))))
(assert 
	(not 
		(and 
			(or 
				(not 
					(<= 
						0
						(+ (sin (sin x)) (* -1 twosin1))))
				(<= 
					(+ (sin (sin x)) (* -1 twosin1))
					(* 51778 (/ 1 100000000)))) 
			(or 
				(not 
					(not 
						(<= 
							0
							(+ (sin (sin x)) (* -1 twosin1)))))
				(<= 
					(* -1 (+ (sin (sin x)) (* -1 twosin1)))
					(* 51778 (/ 1 100000000)))))))
(check-sat)
(get-model)
(exit)
