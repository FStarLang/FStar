(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

(* Millionaire's with 2 parties *)

module SMC

open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val read_fn: unit -> Wys (int * int) (fun m0 -> Mode.m m0 = Par /\
                                        (exists p. Mode.ps m0 = singleton p))
                                (fun m0 r t -> True)
let read_fn x = w_read_int_tuple ()

val median: unit -> Wys int (pre (Mode Par ab)) post
let median _ =
  let p_alice = as_par alice_s read_fn in
  let p_bob = as_par bob_s read_fn in

  let tup = mk_tuple p_alice p_bob in

  let g:unit -> Wys int (pre (Mode Sec ab)) post =
    fun _ ->
      let p_alice = fst tup in
      let p_bob = snd tup in
      let a_t = unbox_s p_alice in
      let b_t = unbox_s p_bob in
      let x1 = fst a_t in
      let x2 = snd a_t in
      let y1 = fst b_t in
      let y2 = snd b_t in
      let t1 = mk_tuple x1 y1 in
      let x1 = fst t1 in
      let y1 = snd t1 in
      let b1 = x1 <= y1 in
      let x3 = if b1 then x2 else x1 in
      let y3 = if b1 then y1 else y2 in
      let b2 = x3 <= y3 in
      if b2 then x3 else y3
  in

  as_sec ab g
;;

let x = main ab median in
print_int x
