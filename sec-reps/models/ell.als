sig ELL {
  rows, cols, maxnz: Int,
  vals: seq Value,
  cids: seq Int
}

pred repInv [e: ELL] {
  e.rows >= 0
  e.cols >= 0
  e.maxnz >= 0
  e.maxnz <= e.cols
  let sz = mul[e.rows, e.maxnz] |
    #e.cids = sz and #e.vals = sz
  all j: e.cids.elems |
    gte[j, -1] and lt[j, e.cols]
  all i: range[e.rows], j: range[e.cols] |
    let s = mul[i, e.maxnz],
        t = sub[add[s, e.maxnz], 1] |
      #e.cids.subseq[s, t].indsOf[j] <= 1
  all i: Int |
    e.cids[i] = -1 <=> e.vals[i] = Zero
}