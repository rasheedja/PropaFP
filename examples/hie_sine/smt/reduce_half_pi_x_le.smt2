(set-logic QF_NRA)
(declare-fun r1 () Int)
(assert (<= (/ 0 1) r1))
(assert (<= r1 (/ 511 1)))
(declare-fun x () Real)
(assert (<= (/ 0 1) x))
(assert (<= x (/ 802 1)))
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
	(<= 
		(* (* -1 500000001) (/ 1 1000000000))
		(+ (+ (/ x (/ 13176795 8388608)) (* -1 r1)) (/ 542101 2500000000000000000000000))))
(assert 
	(<= 
		(- (+ (/ x (/ 13176795 8388608)) (* -1 r1)) (/ 542101 2500000000000000000000000))
		(* 500000001 (/ 1 1000000000))))
(assert 
	(not 
		(<= 
			(+ (- (- (- (- x (* r1 (/ 25735 16384))) (* r1 (/ 3797 67108864))) (* r1 (/ 17453 17592186044416))) (* r1 (/ 12727493 2361183241434822606848))) (/ 1765573 10000000000))
			(/ 6851933 8388608))))
(check-sat)
(get-model)
(exit)
