module LList
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.FractionalPermission
open Steel.SelReference
include LList.Invariant
module L = FStar.List.Tot.Base

#set-options "--ide_id_info_off"

let rec datas (#a:Type) (l:list (cell a)) : list a =
  match l with
  | [] -> []
  | hd::tl -> data hd :: datas tl

val new_llist (#a:Type) (init:a)
  : SteelSel (t a & list (cell a))
          emp
          (fun pc -> llist (fst pc) (snd pc))
          (requires fun _ -> True)
          (ensures fun _ pc _ -> datas (snd pc) == [init])

let new_llist #a init =
  let cell = mk_cell null_llist init in
  let p = alloc_pt cell in
  intro_llist_nil a;
  rewrite_slprop (llist null_llist []) (llist (next cell) []) (fun _ -> ());
  intro_llist_cons p cell [];
  let pc = p, [cell] in
  pc

val push (#a:Type) (ptr:t a) (l:list (cell a)) (v:a)
  : SteelSel (t a & list (cell a))
          (llist ptr l)
          (fun pc -> llist (fst pc) (snd pc))
          (requires fun _ -> True)
          (ensures fun _ pc _ -> datas (snd pc) == v::datas l)

let push #a ptr l v =
  let cell = mk_cell ptr v in
  let p = alloc_pt cell in
  rewrite_slprop (llist ptr l) (llist (next cell) l) (fun _ -> ());
  intro_llist_cons p cell l;
  let pc = p, (cell::l) in
  pc

val pop (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : SteelSel a
          (llist ptr l)
          (fun _ -> llist (next (L.hd l)) (L.tl l))
          (requires fun _ -> True)
          (ensures fun _ x _ -> x == data (L.hd l))

let pop #a ptr l =
  let hd = L.hd l in
  let tl = L.tl l in
  rewrite_slprop (llist ptr l) (llist ptr (hd::tl)) (fun _ -> ());
  elim_llist_cons ptr hd tl;
  let c = read_pt ptr in
  let n = next hd in
  free_pt ptr;
  rewrite_slprop (llist (next hd) tl) (llist (next (L.hd l)) (L.tl l)) (fun _ -> ());
  return (data c)
