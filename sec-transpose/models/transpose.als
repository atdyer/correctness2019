pred copyvals [c, c': CSR, iao, iao': seq Int] {
  #iao' = #iao
  some ia: Int->Int->Int {
    -- init ia and array lengths
    0->iao in ia
    #ia.Int.Int = add[#c.A, 1]
    all i: ia.Int.Int | #ia[i] = #iao
    -- iterate
    all i: range[c.rows] {
      all k: range[c.IA[i], c.IA[i.add[1]]] {
        let t = k, t' = t.add[1],
            j = c.JA[k], nxt = ia[t][j] {
          ia[t'] = ia[t] ++ j->nxt.add[1]
          c'.JA[nxt] = i
          c'.A[nxt] = c.A[k]
        }
      }
    }
    iao' = ia[c.IA.last]
  }
}