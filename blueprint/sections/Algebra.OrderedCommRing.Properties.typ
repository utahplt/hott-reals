#import "../lib.typ": *

== `Algebra.OrderedCommRing.Properties`

Throughout this section $R$ is an ordered commutative ring (@IsOrderedCommRing).

#lemma(<OrderedCommRingToOrderedAbGroup>, agda: "OrderedCommRing→OrderedAbGroup")[
  Every ordered commutative ring (@IsOrderedCommRing) is an ordered abelian group under its addition, with the same lattice and the same strict order.
]
#proof[
  The additive structure of a commutative ring is an abelian group, and the remaining axioms of @IsOrderedAbGroup are among those of @IsOrderedCommRing verbatim.
]

#lemma(<mulNonNeg>, agda: "0≤·")[
  For all $x, y : R$, if $0 <= x$ and $0 <= y$, then $0 <= x dot y$.
]
#proof[
  By $0 <= x$ and monotonicity of multiplication on the right by $y$ (which is nonnegative) (@IsOrderedCommRing), we have $0 dot y <= x dot y$, and $0 dot y = 0$ by the ring laws.
]

#lemma(<sqMonoLt>, agda: "0≤→<→²<²")[
  For all $x, y : R$, if $0 <= x$ and $x < y$, then $x dot x < y dot y$.
]
#proof[
  Since $0 <= x < y$, we have $0 < y$ by mixed transitivity (@IsOrderedCommRing). Then $x dot x <= x dot y$ by monotonicity on the left by $x$ (which is nonnegative), and $x dot y < y dot y$ by strict monotonicity on the right $y$ (which is positive). The conclusion follows by mixed transitivity.
]

#lemma(<sqInj>, agda: "0≤→0≤→²≡²→≡")[
  For all $x, y : R$, if $0 <= x$, $0 <= y$ and $x dot x = y dot y$, then $x = y$.
]
#proof[
  By antisymmetry of $<=$ it suffices to show $x <= y$ and $y <= x$, and by the axiom $x <= y <=> not (y < x)$ (@IsOrderedCommRing) it suffices to refute $y < x$ and $x < y$. If $y < x$, then $y dot y < x dot x$ by @sqMonoLt at $y$ (which is nonnegative), contradicting $x dot x = y dot y$ by the irreflexivity of $<$. The argument for $x < y$ is symmetric.
]

#lemma(<absMul>, agda: "abs·")[
  For all $x, y : R$, $abs(x dot y) = abs(x) dot abs(y)$.
]
#proof[
  Our strategey is to show that the squares of both sides agree and then apply @sqInj.

  Both sides are nonnegative. The left is nonnegative by @absNonNeg, and the right is nonnegative by @mulNonNeg applied to @absNonNeg twice. Their squares also agree. The square of an absolute value is the square of its argument, $abs(z) dot abs(z) = z dot z$, so
  $
    abs(x dot y) dot abs(x dot y) = (x dot y) dot (x dot y),
  $
  and
  $
    (abs(x) dot abs(y)) dot (abs(x) dot abs(y)) = (abs(x) dot abs(x)) dot (abs(y) dot abs(y)) = (x dot x) dot (y dot y) = (x dot y) dot (x dot y)
  $
  by the commutative ring laws. Thus, applying @sqInj gives $abs(x dot y) = abs(x) dot abs(y)$.
]

// TODO: Name is bad, and why isn't it in the ordered abelian group properties?
#lemma(<triangleSubLe>, agda: "triangularInequality-")[
  For all $x, y, z : R$, $abs(x - y) <= abs(x - z) + abs(z - y)$.
]

#lemma(<selfSeparated>, agda: "selfSeparated")[
  For all $x, y : R$, if $abs(x - y) < z$ for every $z : R$ with $0 < z$, then $x = y$.
]
// TODO: Write proof for this because I'm interested in it.
