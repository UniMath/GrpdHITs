# Constructing Higher Inductive Types as Groupoid Quotients

We show that all finitary 1-truncated higher inductive types can be constructed with propositional truncations, set quotients, and the groupoid quotient. We formalize a notion of signature for HITs and we show that each signature gives rise to a bicategory of algebras in 1-types and in groupoids. Then we show that biinitial objects in the bicategory of algebras in 1-types satisfy the induction and we construct a biadjunction between thes two bicategories of algebras. We finish up by constructing a biinitial object in the bicategory of algebras in groupoids.

# Installation

- Make sure to have UniMath (https://github.com/UniMath/UniMath) installed
- coq_makefile -f _CoqProject -o Makefile
- make

To decrease the compilation time, it is suggested to do `make -j 3` instead of `make`.