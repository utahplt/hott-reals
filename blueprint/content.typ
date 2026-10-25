#let chapters = (
  (
    title: [Pseudolattices],
    sections: (
      "Relation.Binary.Order.Pseudolattice.Base",
      "Relation.Binary.Order.Pseudolattice.Properties",
    ),
  ),
)

#let chapter(c) = {
  heading(level: 1, c.title)
  for section in c.sections { include "sections/" + section + ".typ" }
}
