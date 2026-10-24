#import "../lib.typ": *
#import "../notation.typ": *

= `Relation.Premetric.Base`

*Definition* (`IsPremetric`; #cite-p(<gilbert2017>)[Definition 2.1]).
A *premetric space* is a set $M$ together with a family of mere relations $x close(epsilon) y$ on $M$, indexed by $epsilon : Qp$ and read "$x$ and $y$ are $epsilon$-close", such that:
- (reflexivity) $x close(epsilon) x$;
- (symmetry) $x close(epsilon) y$ implies $y close(epsilon) x$;
- (separatedness) if $x close(epsilon) y$ for every $epsilon$, then $x = y$;
- (triangularity) $x close(epsilon) y$ and $y close(delta) z$ imply $x close(epsilon + delta) z$;
- (roundedness) if $x close(epsilon) y$, then there merely exists some $delta < epsilon$ such that $x close(delta) y$.

*Lemma* (`isPropIsPremetric`).
For a set $M$ with a family of mere relations $x close(epsilon) y$, being a premetric space is a proposition.
