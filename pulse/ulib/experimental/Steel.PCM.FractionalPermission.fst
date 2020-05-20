module Steel.PCM.FractionalPermission
open FStar.Real

[@@erasable]
noeq type perm : Type0 =
  | MkPerm: v:real{ v >. 0.0R } -> perm

let writeable (p: perm) : GTot bool =
  MkPerm?.v p = 1.0R

let half_perm (p: perm) : GTot (perm) =
  MkPerm ((MkPerm?.v p) /. two)

let sum_perm (p1 p2: perm) : GTot perm =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

let lesser_equal_perm (p1 p2:perm) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

let full_perm : perm = MkPerm 1.0R
