module LList
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open LList.Invariant
module L = FStar.List.Tot.Base

let rec datas (#a:Type) (l:list (cell a)) : list a =
  match l with
  | [] -> []
  | hd::tl -> data hd :: datas tl

val new_llist (#a:Type) (init:a)
  : Steel (t a & list (cell a))
          emp
          (fun pc -> llist (fst pc) (snd pc))
          (requires fun _ -> True)
          (ensures fun _ pc _ -> datas (snd pc) == [init])

let new_llist #a init =
  let cell = mk_cell null_llist init in
  let p = alloc cell in
  assume (p =!= null_llist);
  intro_llist_nil a;
  change_slprop (llist null_llist []) (llist (next cell) []) (fun _ -> ());
  intro_llist_cons p cell [];
  let pc = p, [cell] in
  pc

val push (#a:Type) (ptr:t a) (l:list (cell a)) (v:a)
  : Steel (t a & list (cell a))
          (llist ptr l)
          (fun pc -> llist (fst pc) (snd pc))
          (requires fun _ -> True)
          (ensures fun _ pc _ -> datas (snd pc) == v::datas l)

let push #a ptr l v =
  let cell = mk_cell ptr v in
  let p = alloc cell in
  assume (p =!= null_llist);
  change_slprop (llist ptr l) (llist (next cell) l) (fun _ -> ());
  intro_llist_cons p cell l;
  let pc = p, (cell::l) in
  pc

val pop (#a:Type) (ptr:t a) (l:list (cell a){Cons? l})
  : Steel a
          (llist ptr l)
          (fun _ -> llist (next (L.hd l)) (L.tl l))
          (requires fun _ -> True)
          (ensures fun _ x _ -> x == data (L.hd l))

let pop #a ptr l =
  let hd = L.hd l in
  let tl = L.tl l in
  change_slprop (llist ptr l) (llist ptr (hd::tl)) (fun _ -> ());
  elim_llist_cons ptr hd tl;
  let c = read ptr in
  let n = next hd in
  drop (pts_to ptr full_perm c);
  change_slprop (llist (next hd) tl) (llist (next (L.hd l)) (L.tl l)) (fun _ -> ());
  data c
