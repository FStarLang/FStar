(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi lib.fst
 --*)

module SMC

open Prins
open FFI
open Wysteria
open WLib

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let bc = union bob_s charlie_s
let abc = union ab charlie_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

val read_fn: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                        (exists p. Mode.ps m0 = singleton p))
                          (fun m0 r t -> True)
let read_fn x = w_read_int ()

val gps_sec: ps:prins
             -> w:Wire int ps{forall p. mem p ps <==> w_contains p w}
             -> unit
             -> Wys (Wire prin ps) (pre (Mode Par ps)) post
let gps_sec ps w _ =

  let wfold_f: int -> prev:prin{w_contains prev w}
               -> p:prin{w_contains p w} -> y:int{w_select p w = y}
               -> Wys (prev:prin{w_contains prev w}) (fun m0 -> b2t (m0 = Mode Sec ps)) (fun m0 r t -> True) =
    fun c prev p y ->
      let y' = projwire_s prev w in
      if c - y' < c - y then prev else p
  in

  let waps_f: p:prin{w_contains p w} -> x:int{w_select p w = x}
              -> Wys prin (pre (Mode Sec ps)) post =
    fun p x ->
      let ps' = remove p ps in
      wfold ps' w (wfold_f x) p
  in

  let g: unit -> Wys (Wire prin ps) (pre (Mode Sec ps)) post =
    fun _ -> waps ps w waps_f
  in

  as_sec ps g

val gps: unit -> Wys bool (pre (Mode Par abc)) post
let gps _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire w1 wc in

  let _ = as_par ab (gps_sec ab w1) in

  let _ = as_par abc (gps_sec abc w2) in

  true
;;

let x = main abc gps in ()
