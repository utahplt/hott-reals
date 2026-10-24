#import "../notation.typ": *

Sections are named after Agda modules and ordered by dependency, so a definition precedes its uses. Following the HoTT book, "there merely exists", the symbol $exists$ and "or" mean the propositionally truncated existential and disjunction.
// TODO: unless we state otherwise because we want to mean the non-truncated version
We write the type of positive rationals, a rational together with a proof that it is positive, as $Qp$. We are purposefully loose and write a positive rational and its underlying rational the same.
In the sections on the completion, $a$ and $b$ range over $M$; $u$, $v$ and $w$ over $completion(M)$; $x$ and $y$ over Cauchy approximations in $completion(M)$; and $epsilon$, $delta$, $eta$ and $theta$ over $Qp$. In `Relation.Premetric.Properties` likewise, $x$ is a Cauchy approximation, there in $M$.
