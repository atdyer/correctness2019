pred MVM [A: Matrix, x: seq Value, 
          b: seq SumProd] {
  A.rows = #b
  A.cols = #x
  all i: range[A.rows] |
    dotProd[A.vals[i], x, b[i]]
}

pred MVM [C: CSR, x: seq Value, 
          b: seq SumProd] {
  C.rows = #b
  C.cols = #x
  all i: range[C.rows] |
    let row = getrow[C, i] |
      dotProd[row, x, b[i]]
}

pred dotProd [row: Int->Value, 
              x: seq Value, 
              b: SumProd] {
  b.vals = { i: row.univ, j, k: Value-Zero | 
               j = row[i] and k = x[i] }
}

fun getrow [c: CSR, row: Int]: Int->Value {
  let cols = rowcols[c, row],
      vals = rowvals[c, row] | ~cols.vals
}

pred refines [n: Int] {
  all C: CSR, M: Matrix, x: seq Value, 
      Cb, Mb: seq SumProd |
    C.rows = n and C.cols = n and
    mulBoth[C, M, x, Cb, Mb] => vecEqv[Cb, Mb]
}

pred mulBoth [C: CSR, M: Matrix, x: seq Value, 
              Cb, Mb: seq SumProd] {
  repInv[C] and repInv[M] and alpha[C, M]
    and MVM[C, x, Cb] and MVM[M, x, Mb]
}

pred vecEqv [a, b: seq SumProd] {
  #a = #b
  all i: a.inds |
    a[i].vals = b[i].vals
}