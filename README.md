[![Build Status](https://travis-ci.org/monadius/ocaml_simple_interval.svg?branch=master)](https://travis-ci.org/monadius/ocaml_simple_interval)

# ocaml_simple_interval
A simple and (hopefully) portable floating-point interval arithmetic library in OCaml.

Original repository: [https://github.com/monadius/ocaml_simple_interval](https://github.com/monadius/ocaml_simple_interval)

## References

- S. Rump, P. Zimmermann, S. Boldo, G. Melquiond 
  [*Computing predecessor and successor in rounding to nearest*](https://hal.inria.fr/inria-00337537/document)
  [(link2)](http://www.ti3.tuhh.de/paper/rump/RuZiBoMe09.pdf)

- S. Rump, T. Ogita, Y. Morikura, S. Oishi
  [*Interval arithmetic with fixed rounding mode*](https://www.jstage.jst.go.jp/article/nolta/7/3/7_362/_pdf)

- F. Goualard 
  [*How do you compute the midpoint of an interval?*](https://hal.archives-ouvertes.fr/hal-00576641/document)
  
- [*ValidatedNumerics.jl*](https://github.com/dpsanders/ValidatedNumerics.jl)

- [*Java library for interval computations*](https://java.net/projects/jinterval)

- S. Boldo, 
  [*Dekker algorithm: error of the multiplication*](https://www.lri.fr/~sboldo/progs/Dekker.c.html). 
  See also S. Boldo, C. Marché,
  [*Formal verification of numerical programs: from C annotated programs to mechanical proofs*](https://hal.inria.fr/hal-00777605/document)

# Interval1

[`Interval1`](interval1.mli) is a simple OCaml interval arithmetic
library which does not depend on any external files and libraries. It
uses the standard rounding to nearest floating-point operations to
compute rigorous interval enclosures of mathematical operations. These
interval enclosures may be not optimal floating-point intervals but in
most cases the error is no more than 1 ulp for each interval endpoint.

# Interval2

[`Interval2`](interval2.mli) is another simple OCaml interval
arithmetic library. It computes optimal floating-point intervals for
basic arithmetic operations. In some cases, it performs computations
with rational arithmetic. This library is slower than `Interval1` but
it may be used in cases when optimal intervals are required (for
instance, when point intervals play an important role or when
discontinuous functions are considered).

# Docs

See the [docs](docs) directory.

# Tests

See the [tests](tests) directory.
