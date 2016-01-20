(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

(* Millionaire's for any 2 parties, private output for the first party, using wires *)

module SMC

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let bc = union bob_s charlie_s
let abc = union ab charlie_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

let to_s2 p1 p2 = union (singleton p1) (singleton p2)

val read_fn: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                  (exists p. Mode.ps m0 = singleton p))
                          (fun m0 r t -> True)
let read_fn x = w_read_int ()

val mill5_sec: #p1:prin -> #p2:prin -> w:Wire int (union (singleton p1) (singleton p2))
               -> unit
               -> Wys bool (pre (Mode Par (to_s2 p1 p2))) post
let mill5_sec #p1 #p2 w _ =
  let g:unit -> Wys bool (pre (Mode Sec (to_s2 p1 p2))) post =
    fun _ -> (projwire_s p1 w) > (projwire_s p2 w)
  in
  as_sec (to_s2 p1 p2) g

val mill5: unit -> Wys bool (pre (Mode Par abc)) post
let mill5 _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire wb wc in

  let _ = as_par ab (mill5_sec #alice #bob w1) in
  let _ = as_par bc (mill5_sec #bob #charlie w2) in

  true
;;

let _ = main abc mill5 in ()
