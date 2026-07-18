module Bug2954

#set-options "--ext compat:2954"

open FStar.List.Pure
open FStar.FunctionalExtensionality
open FStar.Bytes

noeq type comb (n:nat) (ret_type:Type) =
  | Comb: send: FStar.Bytes.bytes -> cont:((llist FStar.Bytes.bytes n) -> ret_type){is_restricted (llist FStar.Bytes.bytes n) cont} -> comb n ret_type

#push-options "--ifuel 1"
val fmap_comb_flip: #n:nat -> #b:Type -> #c:Type -> x:comb n b -> f:(y:b{y<<x} -> c) -> comb n c
let fmap_comb_flip #n x f =
  let Comb xa fb = x in
  let cont vb =
    f (fb vb)
  in
  Comb xa (FStar.FunctionalExtensionality.on _ cont)
#pop-options

val fmap_comb: #n:nat  -> #b:Type -> #c:Type -> (b -> c) -> comb n b -> comb n c
let fmap_comb #n f x =
  fmap_comb_flip x f

noeq type comba (n:nat) (ret:Type) =
  | Abort: comba n ret
  | Ret: v:ret -> comba n ret
  | Com: v:comb n (comba n ret) -> comba n ret

#push-options "--ifuel 1"
val join_comba: #n:nat -> #ret:Type -> comba n (comba n ret) -> comba n ret
let rec join_comba #n #ret x =
  match x with
  | Abort -> Abort
  | Ret r -> r
  | Com y ->
    Com (fmap_comb_flip y join_comba)
#pop-options
