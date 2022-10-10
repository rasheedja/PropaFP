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

;; private__bool_eq
(declare-fun private__bool_eq (us_private
  us_private) Bool)

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

;; int__ref___projection
(define-fun int__ref___projection ((a int__ref)) Int
  (int__content a))

;; __fixed__ref___projection
(define-fun us_fixed__ref___projection ((a us_fixed__ref)) Int
  (us_fixed__content a))

;; bool__ref___projection
(define-fun bool__ref___projection ((a bool__ref)) Bool
  (bool__content a))

;; real__ref___projection
(define-fun real__ref___projection ((a real__ref)) Real
  (real__content a))

;; __private__ref___projection
(define-fun us_private__ref___projection ((a us_private__ref)) us_private
  (us_private__content a))

;; pow2
(declare-fun pow2 (Int) Int)

;; abs'def
(assert
  (forall ((x Real))
    (! (and
         (=> (or (< 0.0 x) (= 0.0 x)) (= (ite (>= x 0.0) x (- x)) x))
         (=>
           (not (or (< 0.0 x) (= 0.0 x)))
           (= (ite (>= x 0.0) x (- x)) (- x)))) :pattern ((ite (>= x 0.0) x (- x))) )))

;; of_int
(declare-fun of_int (RoundingMode
  Int) Float32)

;; to_int
(declare-fun to_int1 (RoundingMode
  Float32) Int)

(declare-const max_int Int)

;; sqrt
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
    (=>
      (and (or (< 0.0 x) (= 0.0 x)) (or (< 0.0 y) (= 0.0 y)))
      (= (sqrt1 (* x y)) (* (sqrt1 x) (sqrt1 y))))))

;; Sqrt_le
(assert
  (forall ((x Real) (y Real))
    (=>
      (and (or (< 0.0 x) (= 0.0 x)) (or (< x y) (= x y)))
      (or (< (sqrt1 x) (sqrt1 y)) (= (sqrt1 x) (sqrt1 y))))))

;; copy_sign
(declare-fun copy_sign (Float32
  Float32) Float32)

;; copy_sign'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=>
           (or
             (and (fp.isPositive x) (fp.isPositive y))
             (and (fp.isNegative x) (fp.isNegative y)))
           (= (copy_sign x y) x))
         (=>
           (not
             (or
               (and (fp.isPositive x) (fp.isPositive y))
               (and (fp.isNegative x) (fp.isNegative y))))
           (= (copy_sign x y) (fp.neg x)))) :pattern ((copy_sign x y)) )))

;; bool_lt
(declare-fun bool_lt (Float32
  Float32) Bool)

;; bool_lt'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.lt x y) (= (bool_lt x y) true))
         (=> (not (fp.lt x y)) (= (bool_lt x y) false))) :pattern ((bool_lt
                                                                    x
                                                                    y)) )))

;; bool_le
(declare-fun bool_le (Float32
  Float32) Bool)

;; bool_le'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.leq x y) (= (bool_le x y) true))
         (=> (not (fp.leq x y)) (= (bool_le x y) false))) :pattern ((bool_le
                                                                    x
                                                                    y)) )))

;; bool_gt
(declare-fun bool_gt (Float32
  Float32) Bool)

;; bool_gt'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.lt y x) (= (bool_gt x y) true))
         (=> (not (fp.lt y x)) (= (bool_gt x y) false))) :pattern ((bool_gt
                                                                    x
                                                                    y)) )))

;; bool_ge
(declare-fun bool_ge (Float32
  Float32) Bool)

;; bool_ge'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.leq y x) (= (bool_ge x y) true))
         (=> (not (fp.leq y x)) (= (bool_ge x y) false))) :pattern ((bool_ge
                                                                    x
                                                                    y)) )))

;; bool_eq
(declare-fun bool_eq (Float32
  Float32) Bool)

;; bool_eq'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.eq x y) (= (bool_eq x y) true))
         (=> (not (fp.eq x y)) (= (bool_eq x y) false))) :pattern ((bool_eq
                                                                    x
                                                                    y)) )))

;; bool_neq
(declare-fun bool_neq (Float32
  Float32) Bool)

;; bool_neq'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (not (fp.eq x y)) (= (bool_neq x y) true))
         (=> (fp.eq x y) (= (bool_neq x y) false))) :pattern ((bool_neq x y)) )))

;; rem
(declare-fun rem1 (Float32
  Float32) Float32)

;; one_is_int
(assert (fp.isIntegral32 (fp #b0 #b01111111 #b00000000000000000000000)))

;; one_of_int
(assert (= (fp #b0 #b01111111 #b00000000000000000000000) (of_int RNA 1)))

(declare-datatypes ((t__ref 0))
  (((t__refqtmk (t__content Float32)))))

;; bool_eq
(declare-fun bool_eq1 (Bool
  Bool) Bool)

;; bool_eq'def
(assert
  (forall ((x Bool) (y Bool))
    (! (and
         (=> (= x y) (= (bool_eq1 x y) true))
         (=> (not (= x y)) (= (bool_eq1 x y) false))) :pattern ((bool_eq1
                                                                  x
                                                                  y)) )))

;; to_int
(declare-fun to_int2 (Bool) Int)

;; to_int'def
(assert
  (forall ((b Bool))
    (! (and
         (=> (= b true) (= (to_int2 b) 1))
         (=> (not (= b true)) (= (to_int2 b) 0))) :pattern ((to_int2 b)) )))

;; of_int
(declare-fun of_int1 (Int) Bool)

;; of_int'def
(assert
  (forall ((i Int))
    (! (and
         (=> (= i 0) (= (of_int1 i) false))
         (=> (not (= i 0)) (= (of_int1 i) true))) :pattern ((of_int1 i)) )))

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE (Bool) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE (us_image) Bool)

;; bool_eq
(declare-fun bool_eq2 (Real
  Real) Bool)

;; bool_ne
(declare-fun bool_ne (Real
  Real) Bool)

;; bool_lt
(declare-fun bool_lt1 (Real
  Real) Bool)

;; bool_le
(declare-fun bool_le1 (Real
  Real) Bool)

;; bool_gt
(declare-fun bool_gt1 (Real
  Real) Bool)

;; bool_ge
(declare-fun bool_ge1 (Real
  Real) Bool)

;; bool_eq_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_eq2 x y) true) (= x y)))))

;; bool_ne_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_ne x y) true) (not (= x y))))))

;; bool_lt_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_lt1 x y) true) (< x y)))))

;; bool_int__le_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_le1 x y) true) (or (< x y) (= x y))))))

;; bool_gt_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_gt1 x y) true) (< y x)))))

;; bool_ge_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_ge1 x y) true) (or (< y x) (= y x))))))

(declare-sort integer 0)

;; integer'int
(declare-fun integerqtint (integer) Int)

;; bool_eq
(declare-fun bool_eq3 (Int
  Int) Bool)

;; bool_eq'def
(assert
  (forall ((x Int) (y Int))
    (! (and
         (=> (= x y) (= (bool_eq3 x y) true))
         (=> (not (= x y)) (= (bool_eq3 x y) false))) :pattern ((bool_eq3
                                                                  x
                                                                  y)) )))

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE1 (Int) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check1 (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE1 (us_image) Int)

;; user_eq
(declare-fun user_eq (integer
  integer) Bool)

(declare-const dummy integer)

(declare-datatypes ((integer__ref 0))
  (((integer__refqtmk (integer__content integer)))))

;; integer__ref_integer__content__projection
(define-fun integer__ref_integer__content__projection ((a integer__ref)) integer
  (integer__content a))

(declare-sort float__ 0)

;; bool_eq
(declare-fun bool_eq4 (Float32
  Float32) Bool)

;; bool_eq'def
(assert
  (forall ((x Float32) (y Float32))
    (! (and
         (=> (fp.eq x y) (= (bool_eq4 x y) true))
         (=> (not (fp.eq x y)) (= (bool_eq4 x y) false))) :pattern ((bool_eq4
                                                                    x
                                                                    y)) )))

;; user_eq
(declare-fun user_eq1 (float__
  float__) Bool)

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE2 (Float32) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check2 (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE2 (us_image) Float32)

(declare-const dummy1 float__)

(declare-datatypes ((float____ref 0))
  (((float____refqtmk (float____content float__)))))

;; float____ref_float____content__projection
(define-fun float____ref_float____content__projection ((a float____ref)) float__
  (float____content a))

;; bool_eq
(declare-fun bool_eq5 (Real
  Real) Bool)

(declare-const value__size Int)

(declare-const object__size Int)

(declare-const alignment Int)

;; value__size_axiom
(assert (or (< 0 value__size) (= 0 value__size)))

;; object__size_axiom
(assert (or (< 0 object__size) (= 0 object__size)))

;; alignment_axiom
(assert (or (< 0 alignment) (= 0 alignment)))

;; user_eq
(declare-fun user_eq2 (Real
  Real) Bool)

(declare-const dummy2 Real)

(declare-datatypes ((big_real__ref 0))
  (((big_real__refqtmk (big_real__content Real)))))

;; big_real__ref_big_real__content__projection
(define-fun big_real__ref_big_real__content__projection ((a big_real__ref)) Real
  (big_real__content a))

(declare-datatypes ((valid_big_real__ref 0))
  (((valid_big_real__refqtmk (valid_big_real__content Real)))))

;; valid_big_real__ref_valid_big_real__content__projection
(define-fun valid_big_real__ref_valid_big_real__content__projection ((a valid_big_real__ref)) Real
  (valid_big_real__content a))

;; to_real
(declare-fun to_real1 (Int) Real)

;; to_real__function_guard
(declare-fun to_real__function_guard (Real
  Int) Bool)

;; bool_eq
(declare-fun bool_eq6 (Int
  Int) Bool)

(declare-const value__size1 Int)

(declare-const object__size1 Int)

(declare-const alignment1 Int)

;; value__size_axiom
(assert (or (< 0 value__size1) (= 0 value__size1)))

;; object__size_axiom
(assert (or (< 0 object__size1) (= 0 object__size1)))

;; alignment_axiom
(assert (or (< 0 alignment1) (= 0 alignment1)))

;; user_eq
(declare-fun user_eq3 (Int
  Int) Bool)

(declare-const dummy3 Int)

(declare-datatypes ((big_integer__ref 0))
  (((big_integer__refqtmk (big_integer__content Int)))))

;; big_integer__ref_big_integer__content__projection
(define-fun big_integer__ref_big_integer__content__projection ((a big_integer__ref)) Int
  (big_integer__content a))

(declare-datatypes ((valid_big_integer__ref 0))
  (((valid_big_integer__refqtmk (valid_big_integer__content Int)))))

;; valid_big_integer__ref_valid_big_integer__content__projection
(define-fun valid_big_integer__ref_valid_big_integer__content__projection 
  ((a valid_big_integer__ref)) Int
  (valid_big_integer__content a))

;; to_real__post_axiom
(assert true)

;; to_real__def_axiom
(assert
  (forall ((arg Int))
    (! (=>
         (and
           (or (< (- 2147483648) arg) (= (- 2147483648) arg))
           (or (< arg 2147483647) (= arg 2147483647)))
         (= (to_real1 arg) (* (to_real arg) (/ 1.0 (to_real 1))))) :pattern (
    (to_real1
      arg)) )))

;; abs
(declare-fun abs1 (Int) Int)

;; abs'def
(assert
  (forall ((x Int))
    (! (and
         (=> (or (< 0 x) (= 0 x)) (= (abs1 x) x))
         (=> (not (or (< 0 x) (= 0 x))) (= (abs1 x) (- x)))) :pattern (
    (abs1
      x)) )))

;; Abs_le
(assert
  (forall ((x Int) (y Int))
    (=
      (or (< (abs1 x) y) (= (abs1 x) y))
      (and (or (< (- y) x) (= (- y) x)) (or (< x y) (= x y))))))

;; Abs_pos
(assert (forall ((x Int)) (or (< 0 (abs1 x)) (= 0 (abs1 x)))))

;; div
(declare-fun div1 (Int
  Int) Int)

;; mod
(declare-fun mod1 (Int
  Int) Int)

;; Div_mod
(assert
  (forall ((x Int) (y Int))
    (=> (not (= y 0)) (= x (+ (* y (div1 x y)) (mod1 x y))))))

;; Div_bound
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< 0 x) (= 0 x)) (< 0 y))
      (and
        (or (< 0 (div1 x y)) (= 0 (div1 x y)))
        (or (< (div1 x y) x) (= (div1 x y) x))))))

;; Mod_bound
(assert
  (forall ((x Int) (y Int))
    (=>
      (not (= y 0))
      (and (< (- (abs1 y)) (mod1 x y)) (< (mod1 x y) (abs1 y))))))

;; Div_sign_pos
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< 0 x) (= 0 x)) (< 0 y))
      (or (< 0 (div1 x y)) (= 0 (div1 x y))))))

;; Div_sign_neg
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< x 0) (= x 0)) (< 0 y))
      (or (< (div1 x y) 0) (= (div1 x y) 0)))))

;; Mod_sign_pos
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< 0 x) (= 0 x)) (not (= y 0)))
      (or (< 0 (mod1 x y)) (= 0 (mod1 x y))))))

;; Mod_sign_neg
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< x 0) (= x 0)) (not (= y 0)))
      (or (< (mod1 x y) 0) (= (mod1 x y) 0)))))

;; Rounds_toward_zero
(assert
  (forall ((x Int) (y Int))
    (=>
      (not (= y 0))
      (or
        (< (abs1 (* (div1 x y) y)) (abs1 x))
        (= (abs1 (* (div1 x y) y)) (abs1 x))))))

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
    (! (=>
         (and (< 0 x) (and (or (< 0 y) (= 0 y)) (or (< 0 z) (= 0 z))))
         (= (div1 (+ (* x y) z) x) (+ y (div1 z x)))) :pattern ((div1
                                                                  (+ (* x y) z)
                                                                  x)) )))

;; Mod_mult
(assert
  (forall ((x Int) (y Int) (z Int))
    (! (=>
         (and (< 0 x) (and (or (< 0 y) (= 0 y)) (or (< 0 z) (= 0 z))))
         (= (mod1 (+ (* x y) z) x) (mod1 z x))) :pattern ((mod1
                                                            (+ (* x y) z)
                                                            x)) )))

;; Div_unique
(assert
  (forall ((x Int) (y Int) (q Int))
    (=>
      (< 0 y)
      (=>
        (and (or (< (* q y) x) (= (* q y) x)) (< x (+ (* q y) y)))
        (= (div x y) q)))))

;; Div_bound
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (or (< 0 x) (= 0 x)) (< 0 y))
      (and
        (or (< 0 (div x y)) (= 0 (div x y)))
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

;; mod
(declare-fun mod2 (Int
  Int) Int)

;; mod'def
(assert
  (forall ((x Int) (y Int))
    (! (and
         (=>
           (or (and (< 0 x) (< 0 y)) (and (< x 0) (< y 0)))
           (= (mod2 x y) (mod1 x y)))
         (=>
           (not (or (and (< 0 x) (< 0 y)) (and (< x 0) (< y 0))))
           (and
             (=> (= (mod1 x y) 0) (= (mod2 x y) 0))
             (=> (not (= (mod1 x y) 0)) (= (mod2 x y) (+ (mod1 x y) y)))))) :pattern (
    (mod2
      x
      y)) )))

;; real_pi
(declare-fun real_pi (tuple0) Real)

;; real_pi__function_guard
(declare-fun real_pi__function_guard (Real
  tuple0) Bool)

(declare-sort quadrant 0)

;; quadrant'int
(declare-fun quadrantqtint (quadrant) Int)

;; bool_eq
(declare-fun bool_eq7 (Int
  Int) Bool)

;; bool_eq'def
(assert
  (forall ((x Int) (y Int))
    (! (and
         (=> (= x y) (= (bool_eq7 x y) true))
         (=> (not (= x y)) (= (bool_eq7 x y) false))) :pattern ((bool_eq7
                                                                  x
                                                                  y)) )))

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE3 (Int) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check3 (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE3 (us_image) Int)

;; user_eq
(declare-fun user_eq4 (quadrant
  quadrant) Bool)

(declare-const dummy4 quadrant)

(declare-datatypes ((quadrant__ref 0))
  (((quadrant__refqtmk (quadrant__content quadrant)))))

;; quadrant__ref_quadrant__content__projection
(define-fun quadrant__ref_quadrant__content__projection ((a quadrant__ref)) quadrant
  (quadrant__content a))

;; real_sin
(declare-fun real_sin (Real) Real)

;; real_sin__function_guard
(declare-fun real_sin__function_guard (Real
  Real) Bool)

;; real_sin__post_axiom
(assert
  (forall ((a Real))
    (! (=>
         (real_sin__function_guard (real_sin a) a)
         (and
           (and
             (and
               (= (bool_le1
                    (ite (>= (real_sin a) 0.0) (real_sin a) (- (real_sin a)))
                    (to_real1 1)) true)
               (=>
                 (= (bool_eq2 a (to_real1 0)) true)
                 (= (bool_eq2 (real_sin a) (to_real1 0)) true)))
             (and
               (real_pi__function_guard (real_pi Tuple0) Tuple0)
               (=>
                 (= (bool_eq2 a (real_pi Tuple0)) true)
                 (= (bool_eq2 (real_sin a) (to_real1 0)) true))))
           (and
             (real_pi__function_guard (real_pi Tuple0) Tuple0)
             (=>
               (= (bool_eq2
                    a
                    (* (* (to_real1 1) (/ 1.0 (to_real1 2))) (real_pi Tuple0))) true)
               (= (bool_eq2 (real_sin a) (to_real1 1)) true))))) :pattern (
    (real_sin
      a)) )))

;; real_cos
(declare-fun real_cos (Real) Real)

;; real_cos__function_guard
(declare-fun real_cos__function_guard (Real
  Real) Bool)

(declare-const x Float32)

;; real_pi__post_axiom
(assert
  (forall ((us_void_param tuple0))
    (! (=>
         (real_pi__function_guard (real_pi us_void_param) us_void_param)
         (and
           (= (bool_ge1
                (real_pi us_void_param)
                (* (to_real 7074237752028440) (/ 1.0 (to_real 2251799813685248)))) true)
           (= (bool_le1
                (real_pi us_void_param)
                (* (to_real 7074237752028441) (/ 1.0 (to_real 2251799813685248)))) true))) :pattern (
    (real_pi
      us_void_param)) )))

;; real_cos__post_axiom
(assert
  (forall ((a Real))
    (! (=>
         (real_cos__function_guard (real_cos a) a)
         (and
           (and
             (and
               (= (bool_le1
                    (ite (>= (real_cos a) 0.0) (real_cos a) (- (real_cos a)))
                    (to_real1 1)) true)
               (=>
                 (= (bool_eq2 a (to_real1 0)) true)
                 (= (bool_eq2 (real_cos a) (to_real1 1)) true)))
             (and
               (real_pi__function_guard (real_pi Tuple0) Tuple0)
               (=>
                 (= (bool_eq2 a (real_pi Tuple0)) true)
                 (= (bool_eq2 (real_cos a) (to_real1 (- 1))) true))))
           (and
             (real_pi__function_guard (real_pi Tuple0) Tuple0)
             (=>
               (= (bool_eq2
                    a
                    (* (* (to_real1 1) (/ 1.0 (to_real1 2))) (real_pi Tuple0))) true)
               (= (bool_eq2 (real_cos a) (to_real1 0)) true))))) :pattern (
    (real_cos
      a)) )))

(declare-const finalresult Float32)

(declare-const q Int)

(declare-const r Int)

(declare-const result__ Float32)

;; Assume
(assert (fp.isFinite32 x))

;; Assume
(assert
  (=>
    (or
      (= false true)
      (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
    (fp.isFinite32 finalresult)))

;; Assume
(assert
  (and
    (fp.leq (fp.neg (fp #b0 #b10001000 #b10010001000000000000000)) x)
    (fp.leq x (fp #b0 #b10001000 #b10010001000000000000000))))

(declare-const o Float32)

;; H
(assert
  (and
    (=>
      (fp.lt x (fp #b0 #b00000000 #b00000000000000000000000))
      (= o (fp.neg x)))
    (=>
      (not (fp.lt x (fp #b0 #b00000000 #b00000000000000000000000)))
      (= o x))))

;; Assume
(assert (fp.isFinite32 o))

;; Assume
(assert true)

;; Assume
(assert
  (=>
    (or (= false true) (or (< 0 3) (= 0 3)))
    (and (or (< 0 q) (= 0 q)) (or (< q 3) (= q 3)))))

;; Assume
(assert true)

;; Assume
(assert
  (=>
    (or
      (= false true)
      (or (< (- 2147483648) 2147483647) (= (- 2147483648) 2147483647)))
    (and
      (or (< (- 2147483648) r) (= (- 2147483648) r))
      (or (< r 2147483647) (= r 2147483647)))))

;; Assume
(assert true)

;; Assume
(assert
  (=>
    (or
      (= false true)
      (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
    (fp.isFinite32 result__)))

(declare-const y Float32)

(declare-const r1 Int)

;; H
(assert (or (< 0 r1) (= 0 r1)))

;; H
(assert (or (< r1 511) (= r1 511)))

;; H
(assert
  (= (bool_ge1
       (+ (fp.to_real (fp.div RNE o (fp #b0 #b01111111 #b10010010000111111011011))) (- 
       (to_real1
         r1)))
       (* (to_real1 (- 500000001)) (/ 1.0 (to_real1 1000000000)))) true))

;; H
(assert
  (= (bool_le1
       (+ (fp.to_real (fp.div RNE o (fp #b0 #b01111111 #b10010010000111111011011))) (- 
       (to_real1
         r1)))
       (* (to_real1 500000001) (/ 1.0 (to_real1 1000000000)))) true))

;; H
(assert (fp.leq (fp.neg (fp #b0 #b01111110 #b10100010001101010111010)) y))

;; H
(assert (fp.leq y (fp #b0 #b01111110 #b10100010001101010111010)))

;; H
(assert
  (and
    (real_pi__function_guard (real_pi Tuple0) Tuple0)
    (= (bool_ge1
         (+ (fp.to_real y) (- (+ (fp.to_real o) (- (* (* (to_real1 r1) 
         (real_pi
           Tuple0)) (/ 1.0 (fp.to_real (fp #b0 #b10000000 #b00000000000000000000000))))))))
         (* (to_real1 (- 18)) (/ 1.0 (to_real1 100000)))) true)))

;; H
(assert
  (and
    (real_pi__function_guard (real_pi Tuple0) Tuple0)
    (= (bool_le1
         (+ (fp.to_real y) (- (+ (fp.to_real o) (- (* (* (to_real1 r1) 
         (real_pi
           Tuple0)) (/ 1.0 (fp.to_real (fp #b0 #b10000000 #b00000000000000000000000))))))))
         (* (to_real1 18) (/ 1.0 (to_real1 100000)))) true)))

;; H
(assert (fp.isFinite32 y))

;; H
(assert
  (and
    (or (< 0 (mod2 r1 4)) (= 0 (mod2 r1 4)))
    (or (< (mod2 r1 4) 3) (= (mod2 r1 4) 3))))

;; H
(assert
  (and
    (or (< (- 2147483648) r1) (= (- 2147483648) r1))
    (or (< r1 2147483647) (= r1 2147483647))))

(declare-const result__1 Float32)

;; H
(assert
  (and
    (=>
      (or
        (and
          (= (mod2 r1 4) 0)
          (or (= (mod2 r1 4) 2) (not (= (mod2 r1 4) 2))))
        (and
          (not (= (mod2 r1 4) 0))
          (or (= (mod2 r1 4) 2) (and (not (= (mod2 r1 4) 2)) (= false true)))))
      (and
        (and
          (and
            (and
              (fp.leq (fp.neg (fp #b0 #b01111111 #b00000000000000000000000)) 
              result__1)
              (fp.leq result__1 (fp #b0 #b01111111 #b00000000000000000000000)))
            (and
              (real_sin__function_guard
                (real_sin (fp.to_real y))
                (fp.to_real y))
              (= (bool_ge1
                   (+ (fp.to_real result__1) (- (real_sin (fp.to_real y))))
                   (* (to_real1 (- 58)) (/ 1.0 (to_real1 1000000000)))) true)))
          (and
            (real_sin__function_guard
              (real_sin (fp.to_real y))
              (fp.to_real y))
            (= (bool_le1
                 (+ (fp.to_real result__1) (- (real_sin (fp.to_real y))))
                 (* (to_real1 58) (/ 1.0 (to_real1 1000000000)))) true)))
        (fp.isFinite32 result__1)))
    (=>
      (not
        (=>
          (not (= (mod2 r1 4) 0))
          (=> (not (= (mod2 r1 4) 2)) (= false true))))
      (and
        (and
          (and
            (and
              (fp.leq (fp.neg (fp #b0 #b01111111 #b00000000000000000000000)) 
              result__1)
              (fp.leq result__1 (fp #b0 #b01111111 #b00000000000000000000000)))
            (and
              (real_cos__function_guard
                (real_cos (fp.to_real y))
                (fp.to_real y))
              (= (bool_ge1
                   (+ (fp.to_real result__1) (- (real_cos (fp.to_real y))))
                   (* (to_real1 (- 14)) (/ 1.0 (to_real1 100000000)))) true)))
          (and
            (real_cos__function_guard
              (real_cos (fp.to_real y))
              (fp.to_real y))
            (= (bool_le1
                 (+ (fp.to_real result__1) (- (real_cos (fp.to_real y))))
                 (* (to_real1 14) (/ 1.0 (to_real1 100000000)))) true)))
        (fp.isFinite32 result__1)))))

(declare-const finalresult1 Float32)

;; H
(assert
  (and
    (=>
      (or
        (fp.lt x (fp #b0 #b00000000 #b00000000000000000000000))
        (and
          (not (fp.lt x (fp #b0 #b00000000 #b00000000000000000000000)))
          (= false true)))
      (and
        (=>
          (or (< 2 (mod2 r1 4)) (= 2 (mod2 r1 4)))
          (= finalresult1 result__1))
        (=>
          (not (or (< 2 (mod2 r1 4)) (= 2 (mod2 r1 4))))
          (= finalresult1 (fp.neg result__1)))))
    (=>
      (not
        (=>
          (not (fp.lt x (fp #b0 #b00000000 #b00000000000000000000000)))
          (= false true)))
      (and
        (=>
          (or (< 2 (mod2 r1 4)) (= 2 (mod2 r1 4)))
          (= finalresult1 (fp.neg result__1)))
        (=>
          (not (or (< 2 (mod2 r1 4)) (= 2 (mod2 r1 4))))
          (= finalresult1 result__1))))))

;; Goal def'vc
;; File "hie_sin.ads", line 64, characters 0-0
(assert
  (not
  (=>
    (real_sin__function_guard (real_sin (fp.to_real x)) (fp.to_real x))
    (= (bool_ge1
         (+ (fp.to_real finalresult1) (- (real_sin (fp.to_real x))))
         (* (to_real1 (- 19)) (/ 1.0 (to_real1 100000)))) true))))

(check-sat)
