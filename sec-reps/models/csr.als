sig CSR {
  rows, cols: Int,
  A: seq Value,
  IA, JA: seq Int
}

pred repInv [c: CSR] {
  c.rows >= 0
  c.cols >= 0
  c.IA[0] = 0
  c.IA.last = #c.A
  #c.A = #c.JA
  #c.IA = add[c.rows, 1]
  Zero not in c.A.elems
  all i: range[c.rows] |
    c.IA[i] <= c.IA[add[i, 1]]
  all j: c.JA.elems | j in range[c.cols]
  all i: range[c.rows] |
    let a = c.IA[i], b = c.IA[add[i, 1]] |
      !c.JA.subseq[a, sub[b, 1]].hasDups
}