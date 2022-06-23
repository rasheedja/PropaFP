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

(declare-sort float__ 0)

(declare-fun user_eq (float__ float__) Bool)

(declare-fun attr__ATTRIBUTE_IMAGE1 (Float32) us_image)

(declare-fun attr__ATTRIBUTE_VALUE__pre_check1 (us_image) Bool)

(declare-fun attr__ATTRIBUTE_VALUE1 (us_image) Float32)

(declare-const dummy float__)

(declare-datatypes ((float____ref 0))
(((float____refqtmk (float____content float__)))))
(define-fun float____ref_float____content__projection ((a float____ref)) float__ 
  (float____content a))

(declare-fun user_eq1 (Real Real) Bool)

(declare-const value__size Int)

(declare-fun object__size (Real) Int)

;; value__size_axiom
  (assert (or (< 0 value__size) (= 0 value__size)))

;; object__size_axiom
  (assert
  (forall ((a Real)) (or (< 0 (object__size a)) (= 0 (object__size a)))))

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

(declare-const x Float32)

(declare-const attr__ATTRIBUTE_ADDRESS Int)

(declare-const attr__ATTRIBUTE_ADDRESS1 Int)

(declare-const attr__ATTRIBUTE_ADDRESS2 Int)

(declare-const onesin Float32)

(declare-const twosin Float32)

;; Assume
  (assert (fp.isFinite32 x))

;; Assume
  (assert
  (and (fp.leq (fp.neg (fp #b0 #b01111110 #b00000000000000000000000)) 
  x) (fp.leq x (fp #b0 #b01111110 #b00000000000000000000000))))

;; Assume
  (assert true)

;; Assume
  (assert
  (=>
  (or (= false true)
  (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
  (fp.isFinite32 onesin)))

;; Assume
  (assert true)

;; Assume
  (assert
  (=>
  (or (= false true)
  (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
  (fp.isFinite32 twosin)))

(declare-const onesin1 Float32)

;; H
  (assert
  (= (ite (or
          (< (* (to_real (- 48)) (/ 1.0 (to_real 100))) (fp.to_real onesin1))
          (= (* (to_real (- 48)) (/ 1.0 (to_real 100))) (fp.to_real onesin1)))
     true false) true))

;; H
  (assert
  (= (ite (or (< (fp.to_real onesin1) (* (to_real 48) (/ 1.0 (to_real 100))))
          (= (fp.to_real onesin1) (* (to_real 48) (/ 1.0 (to_real 100)))))
     true false) true))

;; H
  (assert
  (= (ite (or
          (< (ite (or
                  (< 0.0 (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1))))
                  (= 0.0 (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1)))))
             (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1)))
             (- (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1))))) (* (to_real 25889) (/ 1.0 (to_real 100000000))))
          (= (ite (or
                  (< 0.0 (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1))))
                  (= 0.0 (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1)))))
             (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1)))
             (- (+ (sin1 (fp.to_real x)) (- (fp.to_real onesin1))))) (* (to_real 25889) (/ 1.0 (to_real 100000000)))))
     true false) true))

;; H
  (assert (fp.isFinite32 onesin1))

(declare-const twosin1 Float32)

;; H
  (assert
  (= (ite (or
          (< (* (to_real (- 48)) (/ 1.0 (to_real 100))) (fp.to_real twosin1))
          (= (* (to_real (- 48)) (/ 1.0 (to_real 100))) (fp.to_real twosin1)))
     true false) true))

;; H
  (assert
  (= (ite (or (< (fp.to_real twosin1) (* (to_real 48) (/ 1.0 (to_real 100))))
          (= (fp.to_real twosin1) (* (to_real 48) (/ 1.0 (to_real 100)))))
     true false) true))

;; H
  (assert
  (= (ite (or
          (< (ite (or
                  (< 0.0 (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real 
                  twosin1))))
                  (= 0.0 (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real 
                  twosin1)))))
             (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real twosin1)))
             (- (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real twosin1))))) (* (to_real 25889) (/ 1.0 (to_real 100000000))))
          (= (ite (or
                  (< 0.0 (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real 
                  twosin1))))
                  (= 0.0 (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real 
                  twosin1)))))
             (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real twosin1)))
             (- (+ (sin1 (fp.to_real onesin1)) (- (fp.to_real twosin1))))) (* (to_real 25889) (/ 1.0 (to_real 100000000)))))
     true false) true))

;; H
  (assert (fp.isFinite32 twosin1))

(assert
;; defqtvc
 ;; File "quadratic_equations.ads", line 40, characters 0-0
  (not
  (= (ite (or
          (< (ite (or
                  (< 0.0 (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real 
                  twosin1))))
                  (= 0.0 (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real 
                  twosin1)))))
             (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real twosin1)))
             (- (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real twosin1))))) (* (to_real 51778) (/ 1.0 (to_real 100000000))))
          (= (ite (or
                  (< 0.0 (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real 
                  twosin1))))
                  (= 0.0 (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real 
                  twosin1)))))
             (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real twosin1)))
             (- (+ (sin1 (sin1 (fp.to_real x))) (- (fp.to_real twosin1))))) (* (to_real 51778) (/ 1.0 (to_real 100000000)))))
     true false) true)))
(check-sat)
