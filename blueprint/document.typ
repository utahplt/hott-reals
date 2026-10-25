#import "lib.typ": statements
#import "content.typ": chapters, chapter

#set document(title: [Constructive Analysis in Cubical Agda], author: "Jackson Brough")
#set page(paper: "us-letter", margin: 1in, numbering: "1")
#set text(font: "New Computer Modern", size: 12pt)
#show math.equation: set text(font: "New Computer Modern Math")
#show raw: set text(font: "JuliaMono")
#set par(justify: true)
#set heading(numbering: "1.1")
#show: statements

#align(center)[
  #title[Blueprint]
  #text(size: 1.2em)[HoTT book reals on top of premetric spaces]

  Jackson Brough, Lorenzo Molena
]

#outline(depth: 2)

#heading(numbering: none)[Notation]
#include "sections/preface.typ"

#for c in chapters { chapter(c) }
