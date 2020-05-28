module Steel.PCM.FractionalPermission

open FStar.Real
open Steel.PCM
open Steel.PCM.Unitless

#set-options "--fuel 0 --ifuel 1"

[@erasable]
noeq type perm : Type u#0 =
  | MkPerm: v:real{v >. 0.0R} -> perm

let full_perm : perm = MkPerm 1.0R

let writeable (p: perm) : GTot bool =
  MkPerm?.v p = 1.0R

let half_perm (p: perm) : Tot perm =
  MkPerm ((MkPerm?.v p) /. two)

let sum_perm (p1 p2: perm) : Tot perm =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

let lesser_equal_perm (p1 p2:perm) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

noeq type with_perm (a: Type u#a) = {
  value: a;
  perm: perm
}

let composable_with_perm' (#a: Type) (x y: with_perm a) : prop =
  x.value == y.value /\
  lesser_equal_perm (sum_perm x.perm y.perm) full_perm

let composable_with_perm (#a: Type) : symrel (with_perm a) =
  fun (x y: with_perm a) -> composable_with_perm' x y


let compose_with_perm
  (#a: Type u#a)
  (x: with_perm a)
  (y: with_perm a{x `composable_with_perm ` y}) =
  {
   value = x.value;
   perm = sum_perm x.perm y.perm
  }

let frac_perm_pcm' (#a: Type u#a) : unitless_pcm' (with_perm a) = {
  unitless_composable = composable_with_perm;
  unitless_op = compose_with_perm;
}

let frac_perm_pcm (#a: Type u#a) : unitless_pcm (with_perm a) = {
  unitless_p = frac_perm_pcm';
  unitless_comm = (fun _ _ -> ());
  unitless_assoc = (fun _ _ _ -> ());
  unitless_assoc_r = (fun _ _ _ -> ());
}
