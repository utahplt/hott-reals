#let chapters = (
  (
    title: [Pseudolattices],
    sections: (
      "Relation.Binary.Order.Pseudolattice.Base",
      "Relation.Binary.Order.Pseudolattice.Properties",
    ),
  ),
  (
    title: [Ordered abelian groups],
    sections: (
      "Algebra.OrderedAbGroup.Base",
      "Algebra.OrderedAbGroup.Properties",
    ),
  ),
  (
    title: [Ordered commutative rings],
    sections: (
      "Algebra.OrderedCommRing.Base",
      "Algebra.OrderedCommRing.Properties",
    ),
  ),
)

#let chapter(c) = {
  heading(level: 1, c.title)
  for section in c.sections { include "sections/" + section + ".typ" }
}
