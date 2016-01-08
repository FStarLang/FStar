(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
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

val read_fn: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                  (exists p. Mode.ps m0 = singleton p))
                          (fun m0 r t -> True)
let read_fn x = w_read_int ()

val mill1: unit -> Wys bool (pre (Mode Par ab)) post
let mill1 _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  
  let g:unit -> Wys bool (pre (Mode Sec ab)) post =
    fun _ ->
    let x = unbox_s x in
    let y = unbox_s y in
    let b =
      if x > y then
	let b = true in
	b
      else
	let b = false in
	b
    in
    b
  in

  as_sec ab g
;;

let x = main ab mill1 in
print_bool x
