pred ellcsr [e: ELL, c: CSR] {
  e.rows = c.rows
  e.cols = c.cols
  c.IA[0] = 0
  #c.IA = c.rows.add[1]
  some kpos: seq Int {
    kpos[0] = 0
    #kpos = e.rows.mul[e.maxnz].add[1]
    #c.A = kpos.last
    #c.JA = kpos.last
    all i: range[e.rows] {
      all k: range[e.maxnz] {
        let kp = i.mul[e.maxnz].add[k],
            kp' = kp.add[1] {
          rowcols[e, i][k] != -1 => {
            c.A[kp] = rowvals[e, i][k]
            c.JA[kp] = rowcols[e, i][k]
            kpos[kp'] = kpos[kp].add[1]
          } else {
            kpos[kp'] = kpos[kp]
          }
        }
      }
      c.IA[i.add[1]] = kpos[i.add[1].mul[e.maxnz]]
    }
  }
}

assert translationValid {
  all e: ELL, c: CSR |
    repInv[e] and ellcsr[e, c] => repInv[c]
}