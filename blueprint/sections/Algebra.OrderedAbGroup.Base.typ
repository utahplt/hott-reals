#import "../lib.typ": *

== `Algebra.OrderedAbGroup.Base`

#definition(<IsOrderedAbGroup>, agda: "IsOrderedAbGroup")[
  An *ordered abelian group* is a set $G$ together with a constant $0$, operations $-$, $+$, $inter.sq$, $union.sq$, and relations $<=$, $<$ such that:
  - $(G, 0, +, -)$ is an abelian group.
  - $(G, <=, inter.sq, union.sq)$ is a lattice (@IsPseudolattice).
  - $(G, <)$ is a strict order (irreflexive, transitive, and weakly linear).
  - The two orders are compatible: $x < y$ implies $x <= y$; $x <= y$ if and only if $not (y < x)$; and $x < y <= z$ or $x <= y < z$ implies $x < z$.
  - Both orders are compatible with addition: $x <= y$ implies $x + z <= y + z$, and likewise for $<$. Moreover, if $0 < x + y$ then $0 < x$ or $0 < y$.
  Monotonicity is only required on the right; the left versions follow from commutativity.

  Classically, these are the totally ordered abelian groups. With excluded middle, the axiom $x <= y <==> not (y < x)$ implies strong totality of $<=$. The lattice operations are specified as data because the order is not necessarily decidable, similarly to the ordered fields of #cite-p(<univalentfoundationsprogram2013>)[Definition 11.2.7].
]
