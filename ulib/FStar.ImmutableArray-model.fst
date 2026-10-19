(* Model implementation of FStar.ImmutableArray: verified, but never extracted (the real implementation is native).
   An array is modeled as a list, see FStar.ImmutableArray.Base-model.fst. *)
module FStar.ImmutableArray

friend FStar.ImmutableArray.Base
open FStar.ImmutableArray.Base
module L = FStar.List.Tot

let to_list s = A?.l s
let to_list_of_list _ = ()
let of_list_to_list _ = ()
let length_spec _ = ()
let index_spec _ _ = ()
let to_list_precedes _ = ()

let rec upd_list (#a:Type) (l:list a) (i:nat{i < L.length l}) (v:a)
  : Tot (r:list a{L.length r == L.length l})
  = match l with
    | x :: tl -> if i = 0 then v :: tl else x :: upd_list tl (i - 1) v

let rec index_upd_list (#a:Type) (l:list a) (i:nat{i < L.length l}) (v:a) (j:nat{j < L.length l})
  : Lemma (L.index (upd_list l i v) j == (if i = j then v else L.index l j))
  = match l with
    | _ :: tl -> if i = 0 || j = 0 then () else index_upd_list tl (i - 1) v (j - 1)

let upd s i v = A (upd_list (A?.l s) i v)
let length_upd _ _ _ = ()
let index_upd s i v j = index_upd_list (A?.l s) i v j
let push s v = A (L.append (A?.l s) [v])
let to_list_push _ _ = ()
