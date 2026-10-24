#let Qp = $QQ_+$

#let tolerance-relation(symbol, tolerance) = {
  if tolerance.pos() == () { symbol } else { math.attach(math.scripts(symbol), b: tolerance.pos().first()) }
}

#let close(..tolerance) = tolerance-relation(sym.approx, tolerance)
#let cclose(..tolerance) = tolerance-relation(sym.tilde.op, tolerance)

#let completion(M) = $frak(C) thin #M$
