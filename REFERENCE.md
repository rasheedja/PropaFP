# PropaFP Reference

PropaFP supports SMTLIB2 files produced by our [custom Why3 driver](sparkFiles/propafp.drv).
PropaFP also supports custom input files using the operations defined below.
Anything enclosed with {} are things that should be replaced as appropriate.

```lisp
(declare-fun varName () {varType}) ; Used to declare variables
                                 ; varType must be Real or Integer
                                 ; custom function declarations (i.e., declare-fun with some input types) is not currently supported
(assert {booleanValue})

(>= {n1} {n2}) ; n1 and n2 are things that evaluate to a Real/Integer number
               ; Comparisons return a boolean value
(<= {n1} {n2})
(> {n1} {n2})
(< {n1} {n2})
(= {n1} {n2})

(and {b1} {b2}) ; b1 and b2 are things that evaluate to a boolean value
(or {b1} {b2})
(=> {b1} {b2}) ; this is an implication, i.e. b1 implies b2
(not {b}) ; b is something that evaluates to a boolean value

true  ; boolean value true
false ; boolean value false


(+ {n1} {n2}) ; n1 and n2 are things that evaluate to a Real/Integer number
(- {n1} {n2})
(* {n1} {n2})
(/ {n1} {n2})
(^ {n1} {n2})
(min {n1} {n2})
(max {n1} {n2})
(mod {n1} {n2})

(sqrt {n}) ; n is something that evaluates to a Real/Integer number
(abs {n}) 
(sin {n}) 
(cos {n})

s ; Strings are interpreted as variables. All variables must be bounded: unbounded variables are quietly ignored.
n ; Any number is treated as a Real number.

(to_int_rne {n}) ; round n to the nearest integer, with ties rounding to the nearest even number
(to_int_rtp {n}) ; round n to the nearest integer, with ties rounding towards positive infinity
(to_int_rtn {n}) ; round n to the nearest integer, with ties rounding towards negative infinity
(to_int_rtz {n}) ; round n to the nearest integer, with ties rounding towards zero
(to_int_rna {n}) ; round n to the nearest integer, with ties rounding away from zero

(float32_rne {n}) ; round n to the nearest 32-bit float, with ties rounding to the nearest even number
(float32_rtp {n}) ; round n to the nearest 32-bit float, with ties rounding towards positive infinity
(float32_rtn {n}) ; round n to the nearest 32-bit float, with ties rounding towards negative infinity
(float32_rtz {n}) ; round n to the nearest 32-bit float, with ties rounding towards zero
(float32_rna {n}) ; round n to the nearest 32-bit float, with ties rounding away from zero

(float64_rne {n}) ; round n to the nearest 64-bit float, with ties rounding to the nearest even number
(float64_rtp {n}) ; round n to the nearest 64-bit float, with ties rounding towards positive infinity
(float64_rtn {n}) ; round n to the nearest 64-bit float, with ties rounding towards negative infinity
(float64_rtz {n}) ; round n to the nearest 64-bit float, with ties rounding towards zero
(float64_rna {n}) ; round n to the nearest 64-bit float, with ties rounding away from zero

```

PropaFP will read `assert`s (which consist of the other supported operations) and `declare-fun` in an SMT2 file.
`declare-fun` is used to declare variables and their type.
For example, the following is used to declare the real variable `x` which can hold any value between 0 and 1.

```lisp
(declare-fun x () Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
...
```

PropaFP understands the following types:

```text
Real
Int
Int* (Any type prefixed with Int is treated as an unbounded Int)
Float32
Float64
```

See `smt/` within each directory in `examples/` for examples of files that can be understood by PropaFP (Note that (set-logic QF_NRA) is used for dReal and is ignored by PropaFP).
