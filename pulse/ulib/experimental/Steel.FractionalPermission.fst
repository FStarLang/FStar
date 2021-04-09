module Steel.FractionalPermission
open FStar.Real

[@@erasable]
noeq type perm : Type0 =
  | MkPerm: v:real{ v >. zero } -> perm

let writeable (p: perm) : GTot bool =
  MkPerm?.v p = one

let half_perm (p: perm) : Tot perm =
  MkPerm ((MkPerm?.v p) /. two)

let sum_perm (p1 p2: perm) : Tot perm =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

let lesser_equal_perm (p1 p2:perm) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

let full_perm : perm = MkPerm one
