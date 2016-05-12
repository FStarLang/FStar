type heap = unit

type nonrec 'a ref = 'a ref

type aref =
   | Ref of (unit * unit)

let emp =
  ()

