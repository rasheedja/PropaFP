;; produced by aern2.drv ;;
(set-info :smt-lib-version 2.6)
(set-logic AUFBVFPDTNIRA)
;;; generated by SMT-LIB2 driver
;;; SMT-LIB2 driver: bit-vectors, common part
;;; SMT-LIB2: integer arithmetic
;;; SMT-LIB2: real arithmetic
(define-fun fp.isFinite32 ((x Float32)) Bool (not (or (fp.isInfinite x) (fp.isNaN x))))
(define-fun fp.isIntegral32 ((x Float32)) Bool (or (fp.isZero x) (and (fp.isNormal x) (= x (fp.roundToIntegral RNE x)))))
(declare-sort string 0)

(declare-datatypes ((tuple0 0))
(((Tuple0))))
(declare-sort us_private 0)

(declare-fun private__bool_eq (us_private us_private) Bool)

(declare-const us_null_ext__ us_private)

(declare-sort us_type_of_heap 0)

(declare-datatypes ((us_type_of_heap__ref 0))
(((us_type_of_heap__refqtmk (us_type_of_heap__content us_type_of_heap)))))
(declare-sort us_image 0)

(declare-datatypes ((int__ref 0))
(((int__refqtmk (int__content Int)))))
(declare-datatypes ((bool__ref 0))
(((bool__refqtmk (bool__content Bool)))))
(declare-datatypes ((us_fixed__ref 0))
(((us_fixed__refqtmk (us_fixed__content Int)))))
(declare-datatypes ((real__ref 0))
(((real__refqtmk (real__content Real)))))
(declare-datatypes ((us_private__ref 0))
(((us_private__refqtmk (us_private__content us_private)))))
(define-fun int__ref___projection ((a int__ref)) Int (int__content a))

(define-fun us_fixed__ref___projection ((a us_fixed__ref)) Int (us_fixed__content
                                                               a))

(define-fun bool__ref___projection ((a bool__ref)) Bool (bool__content a))

(define-fun real__ref___projection ((a real__ref)) Real (real__content a))

(define-fun us_private__ref___projection ((a us_private__ref)) us_private 
  (us_private__content a))

;; Abs_le
  (assert
  (forall ((x Int) (y Int))
  (=
  (or (< (ite (or (< 0 x) (= 0 x)) x (- x)) y)
  (= (ite (or (< 0 x) (= 0 x)) x (- x)) y))
  (and (or (< (- y) x) (= (- y) x)) (or (< x y) (= x y))))))

;; Abs_pos
  (assert
  (forall ((x Int))
  (or (< 0 (ite (or (< 0 x) (= 0 x)) x (- x)))
  (= 0 (ite (or (< 0 x) (= 0 x)) x (- x))))))

(declare-fun div1 (Int Int) Int)

(declare-fun mod1 (Int Int) Int)

;; Div_mod
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0)) (= x (+ (* y (div1 x y)) (mod1 x y))))))

;; Div_bound
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< 0 y))
  (and (or (< 0 (div1 x y)) (= 0 (div1 x y)))
  (or (< (div1 x y) x) (= (div1 x y) x))))))

;; Mod_bound
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0))
  (and (< (- (ite (or (< 0 y) (= 0 y)) y (- y))) (mod1 x y))
  (< (mod1 x y) (ite (or (< 0 y) (= 0 y)) y (- y)))))))

;; Div_sign_pos
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< 0 y))
  (or (< 0 (div1 x y)) (= 0 (div1 x y))))))

;; Div_sign_neg
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< x 0) (= x 0)) (< 0 y))
  (or (< (div1 x y) 0) (= (div1 x y) 0)))))

;; Mod_sign_pos
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (not (= y 0)))
  (or (< 0 (mod1 x y)) (= 0 (mod1 x y))))))

;; Mod_sign_neg
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< x 0) (= x 0)) (not (= y 0)))
  (or (< (mod1 x y) 0) (= (mod1 x y) 0)))))

;; Rounds_toward_zero
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0))
  (or
  (< (ite (or (< 0 (* (div1 x y) y)) (= 0 (* (div1 x y) y))) (* (div1 x y) y)
     (- (* (div1 x y) y))) (ite (or (< 0 x) (= 0 x)) x (- x)))
  (= (ite (or (< 0 (* (div1 x y) y)) (= 0 (* (div1 x y) y))) (* (div1 x y) y)
     (- (* (div1 x y) y))) (ite (or (< 0 x) (= 0 x)) x (- x)))))))

;; Div_1
  (assert (forall ((x Int)) (= (div1 x 1) x)))

;; Mod_1
  (assert (forall ((x Int)) (= (mod1 x 1) 0)))

;; Div_inf
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< x y)) (= (div1 x y) 0))))

;; Mod_inf
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< x y)) (= (mod1 x y) x))))

;; Div_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (and (< 0 x) (and (or (< 0 y) (= 0 y)) (or (< 0 z) (= 0 z))))
     (= (div1 (+ (* x y) z) x) (+ y (div1 z x)))) :pattern ((div1
                                                            (+ (* x y) z) x)) )))

;; Mod_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (and (< 0 x) (and (or (< 0 y) (= 0 y)) (or (< 0 z) (= 0 z))))
     (= (mod1 (+ (* x y) z) x) (mod1 z x))) :pattern ((mod1 (+ (* x y) z) x)) )))

;; Div_unique
  (assert
  (forall ((x Int) (y Int) (q Int))
  (=> (< 0 y)
  (=> (and (or (< (* q y) x) (= (* q y) x)) (< x (+ (* q y) y)))
  (= (div x y) q)))))

;; Div_bound
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< 0 y))
  (and (or (< 0 (div x y)) (= 0 (div x y)))
  (or (< (div x y) x) (= (div x y) x))))))

;; Div_inf
  (assert
  (forall ((x Int) (y Int))
  (=> (and (or (< 0 x) (= 0 x)) (< x y)) (= (div x y) 0))))

;; Div_inf_neg
  (assert
  (forall ((x Int) (y Int))
  (=> (and (< 0 x) (or (< x y) (= x y))) (= (div (- x) y) (- 1)))))

;; Mod_0
  (assert (forall ((y Int)) (=> (not (= y 0)) (= (mod 0 y) 0))))

;; Div_1_left
  (assert (forall ((y Int)) (=> (< 1 y) (= (div 1 y) 0))))

;; Div_minus1_left
  (assert (forall ((y Int)) (=> (< 1 y) (= (div (- 1) y) (- 1)))))

;; Mod_1_left
  (assert (forall ((y Int)) (=> (< 1 y) (= (mod 1 y) 1))))

;; Mod_minus1_left
  (assert
  (forall ((y Int))
  (! (=> (< 1 y) (= (mod (- 1) y) (+ y (- 1)))) :pattern ((mod (- 1) y)) )))

;; Div_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (< 0 x) (= (div (+ (* x y) z) x) (+ y (div z x)))) :pattern ((div (+ (* x y) z) x)) )))

;; Mod_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (< 0 x) (= (mod (+ (* x y) z) x) (mod z x))) :pattern ((mod (+ (* x y) z) x)) )))

(declare-fun pow2 (Int) Int)

(declare-fun of_int (RoundingMode Int) Float32)

(declare-fun to_int1 (RoundingMode Float32) Int)

(declare-const max_int Int)

(declare-fun sqrt1 (Real) Real)

;; Sqrt_positive
  (assert
  (forall ((x Real))
  (=> (or (< 0.0 x) (= 0.0 x)) (or (< 0.0 (sqrt1 x)) (= 0.0 (sqrt1 x))))))

;; Sqrt_square
  (assert
  (forall ((x Real))
  (=> (or (< 0.0 x) (= 0.0 x)) (= (* (sqrt1 x) (sqrt1 x)) x))))

;; Square_sqrt
  (assert
  (forall ((x Real)) (=> (or (< 0.0 x) (= 0.0 x)) (= (sqrt1 (* x x)) x))))

;; Sqrt_mul
  (assert
  (forall ((x Real) (y Real))
  (=> (and (or (< 0.0 x) (= 0.0 x)) (or (< 0.0 y) (= 0.0 y)))
  (= (sqrt1 (* x y)) (* (sqrt1 x) (sqrt1 y))))))

;; Sqrt_le
  (assert
  (forall ((x Real) (y Real))
  (=> (and (or (< 0.0 x) (= 0.0 x)) (or (< x y) (= x y)))
  (or (< (sqrt1 x) (sqrt1 y)) (= (sqrt1 x) (sqrt1 y))))))

(declare-fun rem1 (Float32 Float32) Float32)

;; one_is_int
  (assert (fp.isIntegral32 (fp #b0 #b01111111 #b00000000000000000000000)))

;; one_of_int
  (assert (= (fp #b0 #b01111111 #b00000000000000000000000) (of_int RNA 1)))

(declare-datatypes ((t__ref 0))
(((t__refqtmk (t__content Float32)))))
(declare-fun attr__ATTRIBUTE_IMAGE (Bool) us_image)

(declare-fun attr__ATTRIBUTE_VALUE__pre_check (us_image) Bool)

(declare-fun attr__ATTRIBUTE_VALUE (us_image) Bool)

(declare-sort integer 0)

(declare-fun integerqtint (integer) Int)

(declare-fun attr__ATTRIBUTE_IMAGE1 (Int) us_image)

(declare-fun attr__ATTRIBUTE_VALUE__pre_check1 (us_image) Bool)

(declare-fun attr__ATTRIBUTE_VALUE1 (us_image) Int)

(declare-fun user_eq (integer integer) Bool)

(declare-const dummy integer)

(declare-datatypes ((integer__ref 0))
(((integer__refqtmk (integer__content integer)))))
(define-fun integer__ref_integer__content__projection ((a integer__ref)) integer 
  (integer__content a))

(declare-sort float__ 0)

(declare-fun user_eq1 (float__ float__) Bool)

(declare-fun attr__ATTRIBUTE_IMAGE2 (Float32) us_image)

(declare-fun attr__ATTRIBUTE_VALUE__pre_check2 (us_image) Bool)

(declare-fun attr__ATTRIBUTE_VALUE2 (us_image) Float32)

(declare-const dummy1 float__)

(declare-datatypes ((float____ref 0))
(((float____refqtmk (float____content float__)))))
(define-fun float____ref_float____content__projection ((a float____ref)) float__ 
  (float____content a))

(declare-fun user_eq2 (Real Real) Bool)

(declare-const value__size Int)

(declare-fun object__size (Real) Int)

;; value__size_axiom
  (assert (or (< 0 value__size) (= 0 value__size)))

;; object__size_axiom
  (assert
  (forall ((a Real)) (or (< 0 (object__size a)) (= 0 (object__size a)))))

(declare-const attr__ATTRIBUTE_ADDRESS Int)

(declare-const attr__ATTRIBUTE_ADDRESS1 Int)

(declare-const attr__ATTRIBUTE_ADDRESS2 Int)

(declare-const c1 Float32)

(declare-const attr__ATTRIBUTE_ADDRESS3 Int)

(declare-const c2 Float32)

(declare-const attr__ATTRIBUTE_ADDRESS4 Int)

(declare-const c3 Float32)

(declare-const attr__ATTRIBUTE_ADDRESS5 Int)

(declare-const c4 Float32)

(declare-const attr__ATTRIBUTE_ADDRESS6 Int)

(declare-const attr__ATTRIBUTE_ADDRESS7 Int)

(declare-sort quadrant 0)

(declare-fun quadrantqtint (quadrant) Int)

(declare-fun attr__ATTRIBUTE_IMAGE3 (Int) us_image)

(declare-fun attr__ATTRIBUTE_VALUE__pre_check3 (us_image) Bool)

(declare-fun attr__ATTRIBUTE_VALUE3 (us_image) Int)

(declare-fun user_eq3 (quadrant quadrant) Bool)

(declare-const dummy2 quadrant)

(declare-datatypes ((quadrant__ref 0))
(((quadrant__refqtmk (quadrant__content quadrant)))))
(define-fun quadrant__ref_quadrant__content__projection ((a quadrant__ref)) quadrant 
  (quadrant__content a))

(declare-fun cos1 (Real) Real)

(declare-fun sin1 (Real) Real)

;; Pythagorean_identity
  (assert
  (forall ((x Real)) (= (+ (* (cos1 x) (cos1 x)) (* (sin1 x) (sin1 x))) 1.0)))

;; Cos_le_one
  (assert
  (forall ((x Real))
  (or
  (< (ite (or (< 0.0 (cos1 x)) (= 0.0 (cos1 x))) (cos1 x) (- (cos1 x))) 1.0)
  (= (ite (or (< 0.0 (cos1 x)) (= 0.0 (cos1 x))) (cos1 x) (- (cos1 x))) 1.0))))

;; Sin_le_one
  (assert
  (forall ((x Real))
  (or
  (< (ite (or (< 0.0 (sin1 x)) (= 0.0 (sin1 x))) (sin1 x) (- (sin1 x))) 1.0)
  (= (ite (or (< 0.0 (sin1 x)) (= 0.0 (sin1 x))) (sin1 x) (- (sin1 x))) 1.0))))

;; Cos_0
  (assert (= (cos1 0.0) 1.0))

;; Sin_0
  (assert (= (sin1 0.0) 0.0))

(declare-const pi1 Real)

;; Pi_double_precision_bounds
  (assert
  (and (< (/ 7074237752028440.0 2251799813685248.0) pi1)
  (< pi1 (/ 7074237752028441.0 2251799813685248.0))))

;; Cos_pi
  (assert (= (cos1 pi1) (- 1.0)))

;; Sin_pi
  (assert (= (sin1 pi1) 0.0))

;; Cos_pi2
  (assert (= (cos1 (* (/ 5.0 10.0) pi1)) 0.0))

;; Sin_pi2
  (assert (= (sin1 (* (/ 5.0 10.0) pi1)) 1.0))

;; Cos_plus_pi
  (assert (forall ((x Real)) (= (cos1 (+ x pi1)) (- (cos1 x)))))

;; Sin_plus_pi
  (assert (forall ((x Real)) (= (sin1 (+ x pi1)) (- (sin1 x)))))

;; Cos_plus_pi2
  (assert
  (forall ((x Real)) (= (cos1 (+ x (* (/ 5.0 10.0) pi1))) (- (sin1 x)))))

;; Sin_plus_pi2
  (assert (forall ((x Real)) (= (sin1 (+ x (* (/ 5.0 10.0) pi1))) (cos1 x))))

;; Cos_neg
  (assert (forall ((x Real)) (= (cos1 (- x)) (cos1 x))))

;; Sin_neg
  (assert (forall ((x Real)) (= (sin1 (- x)) (- (sin1 x)))))

;; Cos_sum
  (assert
  (forall ((x Real) (y Real))
  (= (cos1 (+ x y)) (+ (* (cos1 x) (cos1 y)) (- (* (sin1 x) (sin1 y)))))))

;; Sin_sum
  (assert
  (forall ((x Real) (y Real))
  (= (sin1 (+ x y)) (+ (* (sin1 x) (cos1 y)) (* (cos1 x) (sin1 y))))))

(declare-fun atan1 (Real) Real)

;; Tan_atan
  (assert
  (forall ((x Real)) (= (* (sin1 (atan1 x)) (/ 1.0 (cos1 (atan1 x)))) x)))

;; c1__def_axiom
  (assert (= c1 (fp #b0 #b01111111 #b10010010000111000000000)))

;; c2__def_axiom
  (assert (= c2 (fp #b0 #b01110000 #b11011010101000000000000)))

;; c3__def_axiom
  (assert (= c3 (fp #b0 #b01100001 #b00010000101101000000000)))

;; c4__def_axiom
  (assert (= c4 (fp #b0 #b01001111 #b10000100011010011000101)))

(declare-const x Float32)

(declare-const q Int)

(declare-const r Int)

;; Assume
  (assert (fp.isFinite32 x))

;; Assume
  (assert
  (=> (or (= false true) (or (< 0 3) (= 0 3)))
  (and (or (< 0 q) (= 0 q)) (or (< q 3) (= q 3)))))

;; Assume
  (assert
  (=>
  (or (= false true)
  (or (< (- 2147483648) 2147483647) (= (- 2147483648) 2147483647)))
  (and (or (< (- 2147483648) r) (= (- 2147483648) r))
  (or (< r 2147483647) (= r 2147483647)))))

;; Assume
  (assert
  (and (fp.leq (fp #b0 #b00000000 #b00000000000000000000000) x)
  (fp.leq x (fp #b0 #b10001000 #b10010001000000000000000))))

;; Assume
  (assert (fp.isFinite32 c1))

;; Assume
  (assert (fp.isFinite32 c2))

;; Assume
  (assert (fp.isFinite32 c3))

;; Assume
  (assert (fp.isFinite32 c4))

;; Assume
  (assert
  (fp.isFinite32 (fp.div RNE x (fp #b0 #b01111111 #b10010010000111111011011))))

(declare-const r1 Int)

;; H
  (assert (or (< 0 r1) (= 0 r1)))

;; H
  (assert (or (< r1 511) (= r1 511)))

;; H
  (assert
  (= (ite (or
          (< (* (to_real (- 500000001)) (/ 1.0 (to_real 1000000000))) (+ (fp.to_real (fp.div RNE 
          x (fp #b0 #b01111111 #b10010010000111111011011))) (- (to_real 
          r1))))
          (= (* (to_real (- 500000001)) (/ 1.0 (to_real 1000000000))) (+ (fp.to_real (fp.div RNE 
          x (fp #b0 #b01111111 #b10010010000111111011011))) (- (to_real 
          r1)))))
     true false) true))

;; H
  (assert
  (= (ite (or
          (< (+ (fp.to_real (fp.div RNE x (fp #b0 #b01111111 #b10010010000111111011011))) (- (to_real 
          r1))) (* (to_real 500000001) (/ 1.0 (to_real 1000000000))))
          (= (+ (fp.to_real (fp.div RNE x (fp #b0 #b01111111 #b10010010000111111011011))) (- (to_real 
          r1))) (* (to_real 500000001) (/ 1.0 (to_real 1000000000)))))
     true false) true))

;; H
  (assert
  (and (or (< (- 2147483648) r1) (= (- 2147483648) r1))
  (or (< r1 2147483647) (= r1 2147483647))))

;; Ensures
  (assert (fp.isFinite32 (fp.sub RNE x (fp.mul RNE (of_int RNE r1) c1))))

(assert
;; defqtvc
 ;; File "certified_sine.ads", line 36, characters 0-0
  (not
  (fp.isFinite32 (fp.sub RNE (fp.sub RNE x (fp.mul RNE (of_int RNE r1) 
  c1)) (fp.mul RNE (of_int RNE r1) c2)))))
(check-sat)
