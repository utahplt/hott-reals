#let cite-p(key, locator) = cite(key, form: "prose", supplement: locator)

// We use Typst figures to display mathematical statements (definitions, lemmas,
// theorems, corollaries). They all share one counter. Using a reference like
// `@label` produces "Lemma 2.3" at the callsite.
#let statement-kind = "statement"

#let statement-numbering(..n) = numbering("1.1", counter(heading).get().first(), ..n.pos())

#let upright-kinds = ("Definition",)

#let statement(supplement, key, agda: none, source: none, body) = {
  let names = if agda == none { () } else if type(agda) == str { (agda,) } else { agda }
  let note = (if names != () { names.map(raw).join(", ") }, source).filter(part => part != none)
  [#figure(
    kind: statement-kind,
    supplement: supplement,
    numbering: statement-numbering,
    caption: if note.len() > 0 { note.join("; ") },
    outlined: false,
    body,
  )#key]
}

#let definition = statement.with("Definition")
#let lemma = statement.with("Lemma")
#let theorem = statement.with("Theorem")
#let corollary = statement.with("Corollary")

#let qed-symbol = $square$
#let qed = h(1em) + h(1fr) + qed-symbol

// Put the QED symbol at the right margin of the last line of `body`. When the
// body ends in a list item, the symbol goes at the end of that item; when it
// ends in a display equation, it takes the place of an equation number.
#let append-qed(body) = {
  let sequence = [].func()
  let space = [ ].func()
  if body.func() == sequence {
    let children = body.children
    let last = children.len() - 1
    while last >= 0 and children.at(last).func() in (space, parbreak) { last -= 1 }
    if last < 0 { return body + qed }
    sequence(children.slice(0, last) + (append-qed(children.at(last)),))
  } else if body.func() == list.item {
    list.item(append-qed(body.body))
  } else if body.func() == enum.item {
    let number = if body.has("number") { body.number } else { auto }
    enum.item(number, append-qed(body.body))
  } else if body.func() == math.equation and body.block {
    math.equation(block: true, numbering: _ => qed-symbol, number-align: right + bottom, body.body)
  } else {
    body + qed
  }
}

#let proof(body) = block(breakable: true, above: 1.2em, below: 1.2em)[
  _Proof._ #append-qed(body)
]

#let show-statement(it) = {
  let head = [*#it.supplement #it.counter.display(it.numbering)*]
  if it.caption != none { head += [ (#it.caption.body)] }
  let body = if it.supplement.text in upright-kinds { it.body } else { emph(it.body) }
  block(breakable: true, above: 1.2em, below: 1.2em, width: 100%)[
    #set align(left)
    #head. #body
  ]
}

#let statements(document) = {
  let statement-figure = figure.where(kind: statement-kind)
  show heading.where(level: 1): it => counter(statement-figure).update(0) + it
  show statement-figure: show-statement
  document
}
