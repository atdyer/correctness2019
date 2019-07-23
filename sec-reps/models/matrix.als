sig Value {}
one sig Zero extends Value {}

sig Matrix {
  rows, cols: Int,
  vals: Int -> Int -> lone Value
}

pred repInv [m: Matrix] {
  m.rows >= 0
  m.cols >= 0
  m.vals.univ = range[m.rows]->range[m.cols]
}