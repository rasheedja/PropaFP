(set-logic QF_NRA)
(declare-fun finalresult1 () Real)
(assert (<= (/ -1 1) finalresult1))
(assert (<= finalresult1 (/ 1 1)))
(declare-fun o () Real)
(assert (<= (/ -802 1) o))
(assert (<= o (/ 802 1)))
(declare-fun r1 () Int)
(assert (<= (/ 0 1) r1))
(assert (<= r1 (/ 511 1)))
(declare-fun result__1 () Real)
(assert (<= (/ -1 1) result__1))
(assert (<= result__1 (/ 1 1)))
(declare-fun x () Real)
(assert (<= (/ -802 1) x))
(assert (<= x (/ 802 1)))
(declare-fun y () Real)
(assert (<= (/ -6851933 8388608) y))
(assert (<= y (/ 6851933 8388608)))
(assert 
	(or 
		(not 
			(< 
				x
				0))
		(= 
			(* -1 x)
			o)))
(assert 
	(or 
		(not 
			(not 
				(< 
					x
					0)))
		(= 
			x
			o)))
(assert 
	(<= 
		(* (* -1 500000001) (/ 1 1000000000))
		(+ (+ (/ o (/ 13176795 8388608)) (* -1 r1)) (/ 542101 2500000000000000000000000))))
(assert 
	(<= 
		(- (+ (/ o (/ 13176795 8388608)) (* -1 r1)) (/ 542101 2500000000000000000000000))
		(* 500000001 (/ 1 1000000000))))
(assert 
	(<= 
		(* (* -1 18) (/ 1 100000))
		(+ y (* -1 (+ o (* -1 (* (* r1 (* 4.0 (atan 1.0))) (/ 1 2))))))))
(assert 
	(<= 
		(+ y (* -1 (+ o (* -1 (* (* r1 (* 4.0 (atan 1.0))) (/ 1 2))))))
		(* 18 (/ 1 100000))))
(assert 
	(<= 
		(mod r1 4)
		3))
(assert 
	(or 
		(not 
			(or 
				(<= 
					(mod r1 4)
					0) 
				(and 
					(not 
						(<= 
							(mod r1 4)
							0)) 
					(= 
						2
						(mod r1 4)))))
		(and 
			(<= 
				(* (* -1 58) (/ 1 1000000000))
				(+ result__1 (* -1 (sin y)))) 
			(<= 
				(+ result__1 (* -1 (sin y)))
				(* 58 (/ 1 1000000000))))))
(assert 
	(or 
		(not 
			(not 
				(or 
					(not 
						(not 
							(<= 
								(mod r1 4)
								0)))
					(= 
						2
						(mod r1 4)))))
		(and 
			(<= 
				(* (* -1 14) (/ 1 100000000))
				(+ result__1 (* -1 (cos y)))) 
			(<= 
				(+ result__1 (* -1 (cos y)))
				(* 14 (/ 1 100000000))))))
(assert 
	(or 
		(not 
			(< 
				x
				0))
		(and 
			(or 
				(not 
					(<= 
						2
						(mod r1 4)))
				(= 
					result__1
					finalresult1)) 
			(or 
				(not 
					(not 
						(<= 
							2
							(mod r1 4))))
				(= 
					(* -1 result__1)
					finalresult1)))))
(assert 
	(or 
		(not 
			(not 
				(< 
					x
					0)))
		(and 
			(or 
				(not 
					(<= 
						2
						(mod r1 4)))
				(= 
					(* -1 result__1)
					finalresult1)) 
			(or 
				(not 
					(not 
						(<= 
							2
							(mod r1 4))))
				(= 
					result__1
					finalresult1)))))
(assert 
	(not 
		(<= 
			(* (* -1 19) (/ 1 100000))
			(+ finalresult1 (* -1 (sin x))))))
(check-sat)
(get-model)
(exit)
