(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

(* PSI *)

module SMC

open FStar.List.Tot
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

let to_s2 p1 p2 = union (singleton p1) (singleton p2)

val read_fn: p:prin -> unit -> Wys (list int) (fun m0 -> b2t (m0 = Mode Par (singleton p)))
                                          (fun m0 r t -> True)
let read_fn _ _ = w_read_int_list ()

val nth: n:nat -> l:list int{length l >= n + 1} -> Tot int
let rec nth n l = if n = 0 then hd_of_cons l else nth (n - 1) (tl_of_cons l)

val mem: x:Box int alice_s -> l:Box (list int) bob_s
         -> n:nat{length (v_of_box l) >= n}
	 -> Wys (bool * int) (pre (Mode Par ab)) post
let rec mem x l n =
  if n = 0 then mk_tuple false 0
  else
    let g:unit -> Wys int (pre (Mode Par bob_s)) post =
      fun _ -> nth (n - 1) (unbox_p l)
    in
    let y = as_par bob_s g in
    let cmp:unit -> Wys (bool * int) (pre (Mode Sec ab)) post =
      fun _ -> if unbox_s x = unbox_s y then mk_tuple true (unbox_s x) else mk_tuple false 0
    in
    let p = as_sec ab cmp in
    if fst p then p else mem x l (n - 1)

val psi: l1:Box (list int) alice_s -> l2:Box (list int) bob_s
         -> n1:nat{length (v_of_box l1) >= n1} -> n2:nat{length (v_of_box l2) >= n2}
	 -> acc:list int
	 -> Wys (list int) (pre (Mode Par ab)) post
let rec psi l1 l2 n1 n2 acc =
  if n1 = 0 then acc
  else
    let g:unit -> Wys int (pre (Mode Par alice_s)) post =
      fun _ -> nth (n1 - 1) (unbox_p l1)
    in
    let x = as_par alice_s g in
    let p = mem x l2 n2 in
    let acc' = if fst p then mk_cons (snd p) acc else acc in
    psi l1 l2 (n1 - 1) n2 acc'

val mlength: l:list int -> Tot (n:nat{n = length l})
let rec mlength l = if is_Nil l then 0 else 1 + mlength (tl_of_cons l)

val psi_m: unit -> Wys (list int) (pre (Mode Par ab)) post
let psi_m _ =
  let l1 = as_par alice_s (read_fn alice) in
  let l2 = as_par bob_s (read_fn bob) in

  let len: p:prin -> l:(Box (list int) (singleton p))
           -> unit
	   -> Wys nat (pre (Mode Par (singleton p))) (fun _ r _ -> True /\ r = length (v_of_box l)) =
    fun _ l _ ->
    let l = unbox_p l in
    mlength l
  in
  let n1 = as_par alice_s (len alice l1) in
  let n2 = as_par bob_s (len bob l2) in

  let g: p:prin{p = alice \/ p = bob} -> n:Box int (singleton p)
         -> unit
	 -> Wys int (pre (Mode Sec ab)) (fun _ r _ -> True /\ r = v_of_box n) =
    fun p n _ -> unbox_s n
  in

  let n1' = as_sec ab (g alice n1) in
  let n2' = as_sec ab (g bob n2) in

  psi l1 l2 n1' n2' (mk_nil ())
;;

let l = main ab psi_m in
print_int_list l
