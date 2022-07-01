;; produced by aern2.drv ;;
(set-info :smt-lib-version 2.6)
(set-logic AUFBVFPDTNIRA)
;;; generated by SMT-LIB2 driver
;;; SMT-LIB2 driver: bit-vectors, common part
;;; SMT-LIB2: integer arithmetic
;;; SMT-LIB2: real arithmetic
(define-fun fp.isFinite32 ((x Float32)) Bool (not (or (fp.isInfinite x) (fp.isNaN x))))
(define-fun fp.isIntegral32 ((x Float32)) Bool (or (fp.isZero x) (and (fp.isNormal x) (= x (fp.roundToIntegral RNE x)))))
(define-fun fp.isFinite64 ((x Float64)) Bool (not (or (fp.isInfinite x) (fp.isNaN x))))
(define-fun fp.isIntegral64 ((x Float64)) Bool (or (fp.isZero x) (and (fp.isNormal x) (= x (fp.roundToIntegral RNE x)))))
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

;; of_int
(declare-fun of_int1 (RoundingMode
  Int) Float64)

;; to_int
(declare-fun to_int2 (RoundingMode
  Float64) Int)

(declare-const max_int1 Int)

;; bool_lt
(declare-fun bool_lt1 (Float64
  Float64) Bool)

;; bool_lt'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.lt x y) (= (bool_lt1 x y) true))
         (=> (not (fp.lt x y)) (= (bool_lt1 x y) false))) :pattern ((bool_lt1
                                                                    x
                                                                    y)) )))

;; bool_le
(declare-fun bool_le1 (Float64
  Float64) Bool)

;; bool_le'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.leq x y) (= (bool_le1 x y) true))
         (=> (not (fp.leq x y)) (= (bool_le1 x y) false))) :pattern (
    (bool_le1
      x
      y)) )))

;; bool_gt
(declare-fun bool_gt1 (Float64
  Float64) Bool)

;; bool_gt'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.lt y x) (= (bool_gt1 x y) true))
         (=> (not (fp.lt y x)) (= (bool_gt1 x y) false))) :pattern ((bool_gt1
                                                                    x
                                                                    y)) )))

;; bool_ge
(declare-fun bool_ge1 (Float64
  Float64) Bool)

;; bool_ge'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.leq y x) (= (bool_ge1 x y) true))
         (=> (not (fp.leq y x)) (= (bool_ge1 x y) false))) :pattern (
    (bool_ge1
      x
      y)) )))

;; bool_eq
(declare-fun bool_eq1 (Float64
  Float64) Bool)

;; bool_eq'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.eq x y) (= (bool_eq1 x y) true))
         (=> (not (fp.eq x y)) (= (bool_eq1 x y) false))) :pattern ((bool_eq1
                                                                    x
                                                                    y)) )))

;; bool_neq
(declare-fun bool_neq1 (Float64
  Float64) Bool)

;; bool_neq'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (not (fp.eq x y)) (= (bool_neq1 x y) true))
         (=> (fp.eq x y) (= (bool_neq1 x y) false))) :pattern ((bool_neq1
                                                                 x
                                                                 y)) )))

;; rem
(declare-fun rem2 (Float64
  Float64) Float64)

;; one_is_int
(assert
  (fp.isIntegral64 (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))

;; one_of_int
(assert
  (= (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000) 
  (of_int1
    RNA
    1)))

(declare-datatypes ((t__ref1 0))
  (((t__refqtmk1 (t__content1 Float64)))))

;; bool_eq
(declare-fun bool_eq2 (Bool
  Bool) Bool)

;; bool_eq'def
(assert
  (forall ((x Bool) (y Bool))
    (! (and
         (=> (= x y) (= (bool_eq2 x y) true))
         (=> (not (= x y)) (= (bool_eq2 x y) false))) :pattern ((bool_eq2
                                                                  x
                                                                  y)) )))

;; to_int
(declare-fun to_int3 (Bool) Int)

;; to_int'def
(assert
  (forall ((b Bool))
    (! (and
         (=> (= b true) (= (to_int3 b) 1))
         (=> (not (= b true)) (= (to_int3 b) 0))) :pattern ((to_int3 b)) )))

;; of_int
(declare-fun of_int2 (Int) Bool)

;; of_int'def
(assert
  (forall ((i Int))
    (! (and
         (=> (= i 0) (= (of_int2 i) false))
         (=> (not (= i 0)) (= (of_int2 i) true))) :pattern ((of_int2 i)) )))

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE (Bool) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE (us_image) Bool)

;; bool_eq
(declare-fun bool_eq3 (Real
  Real) Bool)

;; bool_ne
(declare-fun bool_ne (Real
  Real) Bool)

;; bool_lt
(declare-fun bool_lt2 (Real
  Real) Bool)

;; bool_le
(declare-fun bool_le2 (Real
  Real) Bool)

;; bool_gt
(declare-fun bool_gt2 (Real
  Real) Bool)

;; bool_ge
(declare-fun bool_ge2 (Real
  Real) Bool)

;; bool_eq_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_eq3 x y) true) (= x y)))))

;; bool_ne_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_ne x y) true) (not (= x y))))))

;; bool_lt_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_lt2 x y) true) (< x y)))))

;; bool_int__le_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_le2 x y) true) (or (< x y) (= x y))))))

;; bool_gt_axiom
(assert
  (forall ((x Real)) (forall ((y Real)) (= (= (bool_gt2 x y) true) (< y x)))))

;; bool_ge_axiom
(assert
  (forall ((x Real))
    (forall ((y Real)) (= (= (bool_ge2 x y) true) (or (< y x) (= y x))))))

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
(declare-fun user_eq (float__
  float__) Bool)

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE1 (Float32) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check1 (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE1 (us_image) Float32)

(declare-const dummy float__)

(declare-datatypes ((float____ref 0))
  (((float____refqtmk (float____content float__)))))

;; float____ref_float____content__projection
(define-fun float____ref_float____content__projection ((a float____ref)) float__
  (float____content a))

(declare-sort long_float 0)

;; bool_eq
(declare-fun bool_eq5 (Float64
  Float64) Bool)

;; bool_eq'def
(assert
  (forall ((x Float64) (y Float64))
    (! (and
         (=> (fp.eq x y) (= (bool_eq5 x y) true))
         (=> (not (fp.eq x y)) (= (bool_eq5 x y) false))) :pattern ((bool_eq5
                                                                    x
                                                                    y)) )))

;; user_eq
(declare-fun user_eq1 (long_float
  long_float) Bool)

;; attr__ATTRIBUTE_IMAGE
(declare-fun attr__ATTRIBUTE_IMAGE2 (Float64) us_image)

;; attr__ATTRIBUTE_VALUE__pre_check
(declare-fun attr__ATTRIBUTE_VALUE__pre_check2 (us_image) Bool)

;; attr__ATTRIBUTE_VALUE
(declare-fun attr__ATTRIBUTE_VALUE2 (us_image) Float64)

(declare-const dummy1 long_float)

(declare-datatypes ((long_float__ref 0))
  (((long_float__refqtmk (long_float__content long_float)))))

;; long_float__ref_long_float__content__projection
(define-fun long_float__ref_long_float__content__projection ((a long_float__ref)) long_float
  (long_float__content a))

;; bool_eq
(declare-fun bool_eq6 (Real
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

(declare-sort integer 0)

;; integer'int
(declare-fun integerqtint (integer) Int)

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
(declare-fun user_eq3 (integer
  integer) Bool)

(declare-const dummy3 integer)

(declare-datatypes ((integer__ref 0))
  (((integer__refqtmk (integer__content integer)))))

;; integer__ref_integer__content__projection
(define-fun integer__ref_integer__content__projection ((a integer__ref)) integer
  (integer__content a))

;; bool_eq
(declare-fun bool_eq8 (Int
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
(declare-fun user_eq4 (Int
  Int) Bool)

(declare-const dummy4 Int)

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

(declare-const x Float32)

;; real_sin
(declare-fun real_sin (Real) Real)

;; real_sin__function_guard
(declare-fun real_sin__function_guard (Real
  Real) Bool)

;; real_pi
(declare-fun real_pi (tuple0) Real)

;; real_pi__function_guard
(declare-fun real_pi__function_guard (Real
  tuple0) Bool)

;; real_sin__post_axiom
(assert
  (forall ((a Real))
    (! (=>
         (real_sin__function_guard (real_sin a) a)
         (and
           (and
             (and
               (= (bool_le2
                    (ite (>= (real_sin a) 0.0) (real_sin a) (- (real_sin a)))
                    (to_real1 1)) true)
               (=>
                 (= (bool_eq3 a (to_real1 0)) true)
                 (= (bool_eq3 (real_sin a) (to_real1 0)) true)))
             (and
               (real_pi__function_guard (real_pi Tuple0) Tuple0)
               (=>
                 (= (bool_eq3 a (real_pi Tuple0)) true)
                 (= (bool_eq3 (real_sin a) (to_real1 0)) true))))
           (and
             (real_pi__function_guard (real_pi Tuple0) Tuple0)
             (=>
               (= (bool_eq3
                    a
                    (* (* (to_real1 1) (/ 1.0 (to_real1 2))) (real_pi Tuple0))) true)
               (= (bool_eq3 (real_sin a) (to_real1 1)) true))))) :pattern (
    (real_sin
      a)) )))

(declare-const sqrt_epsilon_lf Float64)

(declare-const g Float32)

(declare-const h0 Float32)

;; sqrt_epsilon_lf__def_axiom
(assert
  (= sqrt_epsilon_lf (fp #b0 #b01111100101 #b0000000000000000000000000000000000000000000000000000)))

;; g__def_axiom
(assert (= g (fp.mul RNE x x)))

;; h0__def_axiom
(assert (= h0 (fp.neg (fp #b0 #b01110010 #b10011000111110111001100))))

;; real_pi__post_axiom
(assert
  (forall ((us_void_param tuple0))
    (! (=>
         (real_pi__function_guard (real_pi us_void_param) us_void_param)
         (and
           (= (bool_ge2
                (real_pi us_void_param)
                (* (to_real 7074237752028440) (/ 1.0 (to_real 2251799813685248)))) true)
           (= (bool_le2
                (real_pi us_void_param)
                (* (to_real 7074237752028441) (/ 1.0 (to_real 2251799813685248)))) true))) :pattern (
    (real_pi
      us_void_param)) )))

(declare-const result__ Float32)

(declare-const h1 Float32)

(declare-const h2 Float32)

;; Assume
(assert (fp.isFinite32 x))

;; Assume
(assert
  (=>
    (or
      (= false true)
      (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
    (fp.isFinite32 result__)))

;; Assume
(assert
  (and
    (fp.leq (fp.neg (fp #b0 #b01111110 #b10100010001101010111010)) x)
    (fp.leq x (fp #b0 #b01111110 #b10100010001101010111010))))

;; Assume
(assert (fp.isFinite64 sqrt_epsilon_lf))

;; Ensures
(assert (fp.isFinite32 (fp.mul RNE x x)))

;; Assume
(assert (= (fp.mul RNE x x) g))

;; Assume
(assert (fp.isFinite32 g))

;; Assume
(assert (fp.isFinite32 h0))

;; Assume
(assert true)

;; Assume
(assert
  (=>
    (or
      (= false true)
      (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
    (fp.isFinite32 h1)))

;; Assume
(assert true)

;; Assume
(assert
  (=>
    (or
      (= false true)
      (fp.leq (fp.neg (fp #b0 #b11111110 #b11111111111111111111111)) (fp #b0 #b11111110 #b11111111111111111111111)))
    (fp.isFinite32 h2)))

(declare-const h11 Float32)

;; H
(assert (fp.leq (fp.neg (fp #b0 #b10000010 #b10000000000000000000000)) h11))

;; H
(assert (fp.leq h11 (fp #b0 #b10000010 #b10000000000000000000000)))

;; H
(assert
  (fp.eq h11 (fp.add RNE (fp.mul RNE h0 g) (fp #b0 #b01111000 #b00010001000001100000010))))

;; H
(assert (fp.isFinite32 h11))

(declare-const h21 Float32)

;; H
(assert (fp.leq (fp.neg (fp #b0 #b10000010 #b10000000000000000000000)) h21))

;; H
(assert (fp.leq h21 (fp #b0 #b10000010 #b10000000000000000000000)))

;; H
(assert
  (fp.eq h21 (fp.add RNE (fp.mul RNE h11 g) (fp.neg (fp #b0 #b01111100 #b01010101010101010100000)))))

;; H
(assert (fp.isFinite32 h21))

(declare-const result__1 Float32)

;; H
(assert
  (and
    (=>
      (or
        (fp.leq (fp.abs x) (fp #b0 #b01100101 #b00000000000000000000000))
        (and
          (not
            (fp.leq (fp.abs x) (fp #b0 #b01100101 #b00000000000000000000000)))
          (= false true)))
      (= result__1 x))
    (=>
      (not
        (=>
          (not
            (fp.leq (fp.abs x) (fp #b0 #b01100101 #b00000000000000000000000)))
          (= false true)))
      (and
        (fp.isFinite32 (fp.mul RNE h21 g))
        (and
          (fp.isFinite32 (fp.mul RNE x (fp.mul RNE h21 g)))
          (and
            (fp.isFinite32 (fp.add RNE (fp.mul RNE x (fp.mul RNE h21 
            g)) x))
            (= result__1 (fp.add RNE (fp.mul RNE x (fp.mul RNE h21 g)) 
            x))))))))

;; Goal def'vc
;; File "hie_sin.ads", line 60, characters 0-0
(assert
  (not
  (=>
    (real_sin__function_guard (real_sin (fp.to_real x)) (fp.to_real x))
    (= (bool_ge2
         (+ (fp.to_real result__1) (- (real_sin (fp.to_real x))))
         (* (to_real1 (- 75)) (/ 1.0 (to_real1 1000000000)))) true))))

(check-sat)
