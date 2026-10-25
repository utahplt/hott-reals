#import "../lib.typ": *

== `Relation.Binary.Order.Pseudolattice.Base`

#definition(<IsPseudolattice>, agda: "IsPseudolattice")[
  A *lattice*#footnote[The Cubical Agda library calls this a _pseudolattice_ and reserves _lattice_ for one with a greatest and a least element, which is typically referred to as a bounded lattice. This appears to be nonstandard, and we follow the more traditional convention.] is a partially ordered set $(L, <=)$ in which any two elements $x, y$ have a greatest lower bound $x inter.sq y$ and a least upper bound $x union.sq y$. That is, for all $z$,
  $
    z <= x inter.sq y <==> z <= x " and " z <= y,
    wide
    x union.sq y <= z <==> x <= z " and " y <= z.
  $
]

#lemma(<makePseudolatticeFromPoset>, agda: "makePseudolatticeFromPoset")[
  Let $(P, <=)$ be a partially ordered set with binary operations $inter.sq$ and $union.sq$ such that for all $a, b, x : P$,
  - $a inter.sq b <= a$ and $a inter.sq b <= b$, and if $x <= a$ and $x <= b$ then $x <= a inter.sq b$;
  - $a <= a union.sq b$ and $b <= a union.sq b$, and if $a <= x$ and $b <= x$ then $a union.sq b <= x$.
  Then $(P, <=)$ is a lattice with meet $inter.sq$ and join $union.sq$.
]

#definition(<IsPseudolatticeEquiv>, agda: "IsPseudolatticeEquiv")[
  An *order isomorphism* between lattices $(L, <=)$ and $(M, <=)$ is an equivalence $e colon L -> M$ such that $x <= y$ if and only if $e(x) <= e(y)$ for all $x, y : L$.
]
