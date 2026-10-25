#import "lib.typ": statements
#import "content.typ": chapters, chapter

#let blueprint-title = "Constructive Analysis in Cubical Agda"
#let authors = ("Jackson Brough", "Lorenzo Molena")
#set document(title: blueprint-title, author: authors)
#set page(paper: "us-letter", margin: 1in, numbering: "1")
#set text(font: "New Computer Modern", size: 12pt)
#show math.equation: set text(font: "New Computer Modern Math")
#show raw: set text(font: "JuliaMono")
#set par(justify: true)
#set heading(numbering: "1.1")
#show: statements

#align(center)[
  #title[Blueprint]
  #text(size: 1.2em)[#blueprint-title]

  // Jackson Brough, Lorenzo Molena
  #authors.join(", ")
]

#outline(depth: 2)

#heading(numbering: none)[Notation]
#include "sections/preface.typ"

#for c in chapters { chapter(c) }

#bibliography("references.bib", style: "ieee")
