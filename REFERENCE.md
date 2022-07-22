# PropaFP Reference

PropaFP supports SMT2 files produced by our [custom Why3 driver](sparkFiles/propafp.drv).
You may also provide your own input file based on Lisp.
The currently supported functions are:

```lisp
(+ arg1 arg2)
(- arg1 arg2)
(* arg1 arg2)
(/ arg1 arg2)
(^ arg1 arg2)

(=  arg1 arg2)
(>= arg1 arg2)
(<= arg1 arg2)
(>  arg1 arg2)
(<  arg1 arg2)

(min arg1 arg2) 
(max arg1 arg2) 

(abs arg1)
(mod arg1 arg2) 

(sin  arg1)
(cos  arg1)
(pow  arg1)
(sqrt arg1)

(and arg1 arg2) 
(or  arg1 arg2) 
(not arg1) 

pi
true
false

(to_int_rne arg1)
(to_int_rna arg1)
(to_int_rtp arg1)
(to_int_rtz arg1)
(to_int_rtn arg1)

(float32_rne arg1)
(float32_rtp arg1)
(float32_rtn arg1)
(float32_rtz arg1)
(float32_rna arg1)

(float64_rne arg1)
(float64_rtp arg1)
(float64_rtn arg1)
(float64_rtz arg1)
(float64_rna arg1)

(declare-fun funName ([inputTypes]) [outputTypes])
(assert boolArg1)
```

PropaFP will only read `assert`s and `declare-fun` in an SMT2 file.
PropaFP only understands type declarations for `declare-fun`.
Note that the [inputTypes] list may be empty.
For example, PropaFP can understand the following:

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
