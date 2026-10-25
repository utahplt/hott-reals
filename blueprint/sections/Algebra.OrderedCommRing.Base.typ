#import "../lib.typ": *

== `Algebra.OrderedCommRing.Base`

#definition(<IsOrderedCommRing>, agda: "IsOrderedCommRing")[
  An *ordered commutative ring* is a set $R$ together with constants $0$, $1$, operations $-$, $+$, $dot$, $inter.sq$, $union.sq$, and relations $<=$, $<$ such that:
  - $(R, 0, 1, -, +, dot)$ is a commutative ring.
  - $(R, <=, inter.sq, union.sq)$ is a lattice (@IsPseudolattice).
  - $(R, <)$ is a strict order (irreflexive, transitive, and weakly linear).
  - The two orders are compatible: $x < y$ implies $x <= y$; $x <= y$ if and only if $not (y < x)$; and $x < y <= z$ or $x <= y < z$ implies $x < z$.
  - Both orders are compatible with addition: $x <= y$ implies $x + z <= y + z$, and likewise for $<$. Moreover, if $0 < x + y$ then $0 < x$ or $0 < y$.
  - Both orders are compatible with multiplication: for $0 <= z$, $x <= y$ implies $x dot z <= y dot z$, and for $0 < z$, $x < y$ implies $x dot z < y dot z$. Finally, $0 < 1$.
  Monotonicity is only required on the right, since the left versions follow from commutativity. The axioms that do not mention multiplication are exactly those of an ordered abelian group (@IsOrderedAbGroup).
]
