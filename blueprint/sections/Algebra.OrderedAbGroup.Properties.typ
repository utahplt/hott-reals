#import "../lib.typ": *
#import "../notation.typ": *

== `Algebra.OrderedAbGroup.Properties`

Throughout this section, let $G$ be an ordered abelian group (@IsOrderedAbGroup).

#lemma(<plusEquivR>, agda: "+PseudolatticeEquivR")[
  For every $z : G$, the map $x |-> x + z colon G -> G$ which translates by $z$ is an order automorphism (@IsPseudolatticeEquiv).
]
#proof[
  We show that $x |-> x + z$ has an inverse, is monotone, and reflects order. Its inverse is $x |-> x - z$, because $G$ is an abelian group under addition, and hence
  $
    (x + z) - z = x = (x - z) + z
  $
  for all $x : G$. We can view the statement that $x <= y$ implies $x + z <= y + z$ for all $x, y, z$ as the statement that the map $x |-> x + z$ is monotone for all $z$, so we have this by corresponding axiom of ordered abelian groups. The same axiom at $-z$ yields that the inverse is monotone too. If $x + z <= y + z$, then
  $
    x = (x + z) - z <= (y + z) - z = y,
  $
  and thus $x |-> x + z$ reflects order.
  // TODO: Should we pull this argument into a small lemma that says to show order reflection, it suffices to show monotonicity of the inverse?
]

#corollary(<meetTranslate>, agda: "+DistL⊓")[
  For all $x, y, z : G$, $(x inter.sq y) + z = (x + z) inter.sq (y + z)$.
]
#proof[
  By @plusEquivR, $x |-> x + z$ is an order isomorphism, so it preserves meets by @presMeet.
]

#corollary(<joinTranslate>, agda: "+DistL⊔")[
  For all $x, y, z : G$, $(x union.sq y) + z = (x + z) union.sq (y + z)$.
]
#proof[
  By @plusEquivR, $x |-> x + z$ is an order isomorphism, so it preserves joins by @presJoin.
]

#lemma(<plusCancelRLe>, agda: "+CancelR≤")[
  Addition on the right reflects order. For all $x, y, z : G$, if $x + z <= y + z$, then $x <= y$.
]
#proof[
  Adding $-z$ on the right (@IsOrderedAbGroup) gives $(x + z) - z <= (y + z) - z$, and by the abelian group laws $(x + z) - z = x$ and $(y + z) - z = y$.
]

#lemma(<plusCancelRLt>, agda: "+CancelR<")[
  Addition on the right reflects strict order. For all $x, y, z : G$, if $x + z < y + z$, then $x < y$.
]
#proof[
  As in the proof of @plusCancelRLe, with strict monotonicity of addition (@IsOrderedAbGroup) in place of monotonicity.
]

#lemma(<negFlipLe>, agda: "-Flip≤")[
  For all $x, y : G$, if $x <= y$, then $-y <= -x$.
]
#proof[
  Adding $-x - y$ on the right gives $x + (-x - y) <= y + (-x - y)$, and by the abelian group laws $x + (-x - y) = -y$ and $y + (-x - y) = -x$.
]

#lemma(<negFlipLt>, agda: "-Flip<")[
  For all $x, y : G$, if $x < y$, then $-y < -x$.
]
#proof[
  As in the proof of @negFlipLe, with strict monotonicity of addition (@IsOrderedAbGroup) in place of monotonicity.
]

#lemma(<negPseudolatticeEquiv>, agda: "-PseudolatticeEquiv")[
  Negation $x |-> -x$ is an order isomorphism $G -> op(G)$ from $G$ to its dual (@DualPseudolattice).
]
#proof[
  We show that negation has an inverse, is monotone, and reflects order. It is its own inverse, since $-(-x) = x$. It is monotone as a map $G -> op(G)$: if $x <= y$, then $-y <= -x$ in $G$ (@negFlipLe), which is $-x <= -y$ in $op(G)$. Its inverse is monotone as a map $op(G) -> G$: if $x <= y$ in $op(G)$, then $y <= x$ in $G$, and negation gives $-x <= -y$ in $G$. Monotonicity of the inverse is order reflection of the original, as in @plusEquivR.
  // TODO: See TODO above about pulling out this reflective monotone inverse argument
]

#corollary(<negMeet>, agda: "-⊓")[
  For all $x, y : G$, $-(x inter.sq y) = (-x) union.sq (-y)$.
]
#proof[
  Apply @presMeet to negation $e colon G -> op(G)$, an order isomorphism by @negPseudolatticeEquiv. This gives
  $
    -(x inter.sq y) = e(x inter.sq_G y) = e(x) inter.sq_(op(G)) e(y) = (-x) union.sq (-y),
  $
  because meets in $op(G)$ are joins in $G$.
]

#corollary(<negJoin>, agda: "-⊔")[
  For all $x, y : G$, $-(x union.sq y) = (-x) inter.sq (-y)$.
]
#proof[
  Apply @presJoin to negation $e colon G -> op(G)$, an order isomorphism by @negPseudolatticeEquiv. This gives
  $
    -(x union.sq y) = e(x union.sq_G y) = e(x) union.sq_(op(G)) e(y) = (-x) inter.sq (-y),
  $
  because joins in $op(G)$ are meets in $G$.
]

#definition(<abs>, agda: "abs")[
  The *absolute value* of $z : G$ is $abs(z) := z union.sq (-z)$.
]

#lemma(<leAbs>, agda: "≤abs")[
  For all $z : G$, $z <= abs(z)$.
]
#proof[
  This is just the claim that $z$ is below its join with $-z$.
]

#lemma(<negLeAbs>, agda: "-≤abs")[
  For all $z : G$, $-z <= abs(z)$.
]
#proof[
  This is just the claim that $-z$ is below its join with $z$.
]

#lemma(<absNonNeg>, agda: "0≤abs")[
  For all $z : G$, $0 <= abs(z)$.
]
#proof[
  By @IsOrderedAbGroup, $0 <= abs(z)$ if and only if not $abs(z) < 0$, so suppose $abs(z) < 0$. Then $-0 < -abs(z)$ by @negFlipLt, $-abs(z) <= -z$ by @negFlipLe applied to @leAbs, and $-z <= abs(z)$ by @negLeAbs. Since $-0 = 0$, this reads
  $
    0 < -abs(z) <= -z <= abs(z) < 0,
  $
  contradicting irreflexivity.
]

#lemma(<absNeg>, agda: "abs-")[
  For all $x : G$, $abs(-x) = abs(x)$.
]
#proof[
  We compute
  $
    abs(-x) = (-x) union.sq (-(-x)) = (-x) union.sq x = x union.sq (-x) = abs(x).
  $
  This uses $-(-x) = x$ and the commutativity of $union.sq$.
]

#lemma(<absSubComm>, agda: "abs-Comm")[
  For all $x, y : G$, $abs(x - y) = abs(y - x)$.
]
#proof[
  We compute
  $
    abs(x - y) = abs(--(x - y)) = abs(-(x - y)) = abs(y - x),
  $
  which uses that negation is its own inverse, @absNeg, and the group laws.

  // TODO: Copy editing
]

#lemma(<absDeltaLtLtPlus>, agda: "absΔ<→<+")[
  For all $x, y, z : G$, if $abs(x - y) < z$, then $y < x + z$.
]
#proof[
  Since $-(x - y) <= abs(x - y)$, we have
  $
    y = x + (-(x - y)) <= x + abs(x - y) < x + z.
  $
]

#lemma(<absDeltaMeetR>, agda: "absΔ⊓≤R")[
  For all $x, y, z : G$,
  $
    abs((x inter.sq z) - (y inter.sq z)) <= abs(x - y).
  $
]
#proof[
  Let $d := abs(x - y)$. We have $x - d <= y$ because $x - y <= d$, and $z - d <= z$ because $0 <= d$ (@absNonNeg). Then
  $
    (x inter.sq z) - d = (x - d) inter.sq (z - d) <= y inter.sq z
  $
  by @meetTranslate and @meetMono, that is, $(x inter.sq z) - (y inter.sq z) <= d$. The same argument with $x$ and $y$ exchanged gives $(y inter.sq z) - (x inter.sq z) <= abs(y - x) = d$ (@absSubComm). So $d$ is an upper bound of both $(x inter.sq z) - (y inter.sq z)$ and its negation, and therefore $d$ is an upper bound of their join, which is $abs((x inter.sq z) - (y inter.sq z))$. In other words,
  $
    abs((x inter.sq z) - (y inter.sq z)) <= d = abs(x - y).
  $
]

#corollary(<absDeltaMeetL>, agda: "absΔ⊓≤L")[
  For all $x, y, z : G$,
  $
    abs((x inter.sq y) - (x inter.sq z)) <= abs(y - z).
  $
]
#proof[
  Apply @absDeltaMeetR to $y$, $z$, $x$ and commute both meets.
]

#corollary(<absDeltaJoinR>, agda: "absΔ⊔≤R")[
  For all $x, y, z : G$,
  $
    abs((x union.sq z) - (y union.sq z)) <= abs(x - y).
  $
]
#proof[
  By @negJoin,
  $
    (-x) inter.sq (-z) = -(x union.sq z) "and" (-y) inter.sq (-z) = -(y union.sq z).
  $
  Also
  $
    abs(-a - (-b)) = abs(-(a - b)) = abs(a - b)$
  for all $a, b : G$ (@absNeg). So applying @absDeltaMeetR to $-x$, $-y$, and $-z$ reads
  $
    abs(-(x union.sq z) - (-(y union.sq z))) <= abs(-x - (-y)),
  $
  that is,
  $
    abs((x union.sq z) - (y union.sq z)) <= abs(x - y).
  $
]

#corollary(<absDeltaJoinL>, agda: "absΔ⊔≤L")[
  For all $x, y, z : G$,
  $
    abs((x union.sq y) - (x union.sq z)) <= abs(y - z).
  $
]
#proof[
  Applying @absDeltaJoinR to $y$, $z$ and $x$ gives $abs((y union.sq x) - (z union.sq x)) <= abs(y - z)$, and joins commute.
]

#lemma(<nonNegAbsEqId>, agda: "0≤→abs≡id")[
  For all $x : G$, if $0 <= x$, then $abs(x) = x$.
]
#proof[
  By antisymmetry, it suffices to show $x <= abs(x)$ and $abs(x) <= x$. We obtain the first by @leAbs. For the second, we have both $x <= x$ and $-x <= x$. The first follows by reflexivity and the second from $-x <= -0 = 0 <= x$ by @negFlipLe and by assumption. Therefore the join $abs(x) = x union.sq (-x)$ is below $x$.
]

#corollary(<absAbs>, agda: "absAbs")[
  For all $x : G$, $abs(abs(x)) = abs(x)$.
]
#proof[
  We have $0 <= abs(x)$ by @absNonNeg, so @nonNegAbsEqId applies to $abs(x)$.
]

#corollary(<absZero>, agda: "abs0")[
  $abs(0) = 0$.
]
#proof[
  We have $0 <= 0$, so @nonNegAbsEqId applies.
]

#lemma(<triangleLe>, agda: "▵≤")[
  For all $x, y : G$, $abs(x + y) <= abs(x) + abs(y)$.
]
#proof[
  The join $abs(x + y) = (x + y) union.sq (-(x + y))$ is below $abs(x) + abs(y)$ if both of its arguments are. First, $x + y <= abs(x) + y <= abs(x) + abs(y)$ by @leAbs and the monotonicity of addition on the right and then on the left. Second, we have $-(x + y) = (-x) + (-y)$ by the abelian group laws, and $(-x) + (-y) <= abs(x) + (-y) <= abs(x) + abs(y)$ from @negLeAbs.
]

#lemma(<absLeIff>, agda: "abs≤≃")[
  For all $x, y : G$, $abs(x) <= y$ if and only if $x <= y$ and $-x <= y$.
]
#proof[
  By definition, $abs(x) = x union.sq (-x)$, and a join is below $y$ if and only if both of its arguments are below $y$ (@IsPseudolattice).
]

#lemma(<absDeltaAbsLe>, agda: "absΔabs≤")[
  For all $x, y : G$, $abs(abs(x) - abs(y)) <= abs(x - y)$.
]
#proof[
  By @absLeIff, it suffices to show $abs(x) - abs(y) <= abs(x - y)$ and $-(abs(x) - abs(y)) <= abs(x - y)$. For the first, we have
  $
    abs(x) = abs((x - y) + y) <= abs(x - y) + abs(y)
  $
  by @triangleLe. Adding $-abs(y)$ on the right gives
  $
    abs(x) - abs(y) <= (abs(x - y) + abs(y)) - abs(y) = abs(x - y).
  $
  For the second, the same argument with $x$ and $y$ exchanged gives
  $
    -(abs(x) - abs(y)) = abs(y) - abs(x) <= abs(y - x) = abs(x - y).
  $
]

#corollary(<absLtLt>, agda: "abs<→<")[
  For all $x, y : G$, if $abs(x) < y$, then $x < y$.
]
#proof[
  We have $x <= abs(x) < y$ (@leAbs).
]

#corollary(<absLtNegLt>, agda: "abs<→-<")[
  For all $x, y : G$, if $abs(x) < y$, then $-y < x$.
]
#proof[
  We have $-x <= abs(x) < y$ (@negLeAbs), which gives $-x < y$, and then @negFlipLt gives $-y < -(-x) = x$.
]
