pred alpha [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  m.vals = {
    i: range[c.rows], 
    j: range[c.cols], 
    v: Value |
      let k = { 
        k: range[c.IA[i], c.IA[i.add[1]]] |
          c.JA[k] = j } |
            one k => v = c.A[k] 
              else v = Zero
  }
}

assert repValid {
  all c: CSR, m: Matrix |
    repInv[c] and alpha[c, m] => repInv[m]
}