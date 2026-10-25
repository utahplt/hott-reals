#import "../lib.typ": *
#import "../notation.typ": *

== `Relation.Binary.Order.Pseudolattice.Properties`

// TODO def. 1.1:
Throughout this section, let $(L, <=)$ and $(M, <=)$ be lattices (@IsPseudolattice).

#definition(<DualPseudolattice>, agda: "DualPseudolattice")[
  The *dual* $op(L)$ of $L$ is the set $L$ with its order reversed. That is, $x <= y$ in $op(L)$ if and only if $y <= x$ in $L$. It is again a lattice, in which the meet is the join $union.sq$ of $L$ and the join is the meet $inter.sq$ of $L$.
]

#lemma(<meetMono>, agda: "∧Mono")[
  If $x <= y$ and $z <= w$, then $x inter.sq z <= y inter.sq w$.
]
#proof[
  We have $x inter.sq z <= x <= y$, since $x inter.sq z$ is a lower bound of $x$ and $x <= y$ holds by assumption. Likewise, we have $x inter.sq z <= z <= w$. Therefore, $x inter.sq z$ is a lower bound of both $y$ and $w$, and hence lies below their greatest lower bound:
  $
    x inter.sq z <= y inter.sq w.
  $
]

#corollary(<meetMonoR>, agda: "∧MonoR")[
  If $x <= y$, then $x inter.sq z <= y inter.sq z$.
]
#proof[
  Apply @meetMono with $z <= z$.
]

#corollary(<meetMonoL>, agda: "∧MonoL")[
  If $x <= y$, then $z inter.sq x <= z inter.sq y$.
]
#proof[
  Apply @meetMono with $z <= z$.
]

#lemma(<joinMono>, agda: "∨Mono")[
  If $x <= y$ and $z <= w$, then $x union.sq z <= y union.sq w$.
]
#proof[
  Apply @meetMono in $op(L)$, where the hypotheses become $y <= x$ and $w <= z$ and the meet is $union.sq$. It gives $y union.sq w <= x union.sq z$ in $op(L)$, which is $x union.sq z <= y union.sq w$ in $L$.
  // TODO: Isn't saying "gives $y union.sq w <= x union.sq z$ in $op(L)$" misleading if we are switching the order but not the meet/join symbol?
]

#corollary(<joinMonoR>, agda: "∨MonoR")[
  If $x <= y$, then $x union.sq z <= y union.sq z$.
]
#proof[
  Apply @joinMono with $z <= z$.
]

#corollary(<joinMonoL>, agda: "∨MonoL")[
  If $x <= y$, then $z union.sq x <= z union.sq y$.
]
#proof[
  Apply @joinMono with $z <= z$.
]

#lemma(<leEquivFunIffInvEqLe>, agda: "≤equivFun≃invEq≤")[
  If $e colon L -> M$ is an order isomorphism (@IsPseudolatticeEquiv), then for all $x : L$ and $m : M$, $m <= e(x)$ if and only if $e^(-1)(m) <= x$.
]
#proof[
  We have $e(e^(-1)(m)) = m <= e(x)$, which holds if and only if $e^(-1)(m) <= x$ because $e$ preserves and reflects order.
]

#lemma(<presMeet>, agda: "pres∧")[
  If $e colon L -> M$ is an order isomorphism, then $e(x inter.sq y) = e(x) inter.sq e(y)$ for all $x, y : L$.
]
#proof[
  For all $m : M$,
  $
    m <= e(x inter.sq y)
    & <==> e^(-1)(m) <= x inter.sq y
    && "by" #ref(<leEquivFunIffInvEqLe>) \
    & <==> e^(-1)(m) <= x " and " e^(-1)(m) <= y
    && "by the universal property of meets in" L \
    & <==> m <= e(x) " and " m <= e(y)
    && "by" #ref(<leEquivFunIffInvEqLe>).
  $
  Thus $e(x inter.sq y)$ satisfies the universal property of the meet of $e(x)$ and $e(y)$ in $M$, and as meets are unique, it follows that $e(x inter.sq y) = e(x) inter.sq e(y)$.
]

#lemma(<DualPseudolatticeEquiv>, agda: "DualPseudolatticeEquiv")[
  If $e colon L -> M$ is an order isomorphism, then so is $e colon op(L) -> op(M)$.
]
#proof[
  For $x, y : L$, $x <= y$ in $op(L)$ means $y <= x$, which holds if and only if $e(y) <= e(x)$, that is, $e(x) <= e(y)$ in $op(M)$.
]

#lemma(<presJoin>, agda: "pres∨")[
  If $e colon L -> M$ is an order isomorphism, then $e(x union.sq y) = e(x) union.sq e(y)$ for all $x, y : L$.
]
#proof[
  Apply @presMeet to $e colon op(L) -> op(M)$, which is an order isomorphism by @DualPseudolatticeEquiv. Meets in $op(L)$ and $op(M)$ are joins in $L$ and $M$, so the result reads $e(x union.sq y) = e(x) union.sq e(y)$.
]

Taken together, @presMeet and @presJoin say that an order isomorphism is an isomorphism of lattices in the algebraic sense of a bijection preserving $inter.sq$ and $union.sq$.
