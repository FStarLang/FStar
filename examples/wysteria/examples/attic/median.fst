(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

module SMC

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre (m:mode)   = fun m0 -> m0 = m
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val median_pre: #ps1:prins -> #ps2:prins
                -> x1:Box int ps1 -> x2:Box int ps1
                -> y1:Box int ps2 -> y2:Box int ps2
                -> GTot bool
let median_pre #ps1 #ps2 x1 x2 y1 y2 =
  let x1, x2, y1, y2 = v_of_box x1, v_of_box x2, v_of_box y1, v_of_box y2 in
  x1 < x2 && y1 < y2 && x1 <> y1 && x1 <> y2 && x2 <> y1 && x2 <> y2

val monolithic_median: x1:Box int alice_s -> x2:Box int alice_s
                       -> y1:Box int bob_s -> y2:Box int bob_s
                       -> Wys int (fun m0 -> m0 = Mode Par ab /\ median_pre x1 x2 y1 y2)
                                  (fun m0 r t -> b2t (t = [TMsg #int r]))
let monolithic_median x1 x2 y1 y2 =
  let f:unit -> Wys int (pre (Mode Sec ab)) (fun m0 r t -> b2t (t = [])) =
    fun _ ->
      let x1 = unbox_s x1 in
      let x2 = unbox_s x2 in
      let y1 = unbox_s y1 in
      let y2 = unbox_s y2 in
      let a = x1 <= y1 in
      let x3 = if a then x2 else x1 in
      let y3 = if a then y1 else y2 in
      let d = x3 <= y3 in
      if d then x3 else y3
  in
  as_sec ab f

val optimized_median:
  x1:Box int alice_s -> x2:Box int alice_s
  -> y1:Box int bob_s -> y2:Box int bob_s
  -> unit
  -> Wys int (fun m0 -> m0 = Mode Par ab /\ median_pre x1 x2 y1 y2)
             (fun m0 r t -> Let (v_of_box x1 <= v_of_box y1)
                                (fun a -> Let (if a then x2 else x1)
                                              (fun x3 -> Let (if a then y1 else y2)
                                                             (fun y3 -> Let (v_of_box x3 <= v_of_box y3)
                                                                            (fun d -> (d ==> r = v_of_box x3)     /\
                                                                                      (not d ==> r = v_of_box y3) /\
                                                                                      t = (TMsg #bool a::
                                                                                           TScope alice_s []::
                                                                                           TScope bob_s []::
                                                                                           TMsg #bool d::
                                                                                           [TMsg #int r]))))))
let optimized_median x1 x2 y1 y2 _ =
  let cmp: x:Box int alice_s -> y:Box int bob_s
           -> unit -> Wys bool (pre (Mode Sec ab)) (fun m0 r t -> r = (v_of_box x <= v_of_box y) /\ t = []) =
    fun x y _ -> unbox_s x <= unbox_s y
  in
  
  let selector: b:bool -> p:prin -> z1:Box int (singleton p) -> z2:Box int (singleton p)
                -> unit -> Wys int (pre (Mode Par (singleton p)))
                                   (fun m0 r t -> (b      ==> r = v_of_box z1) /\
                                                  (not b  ==> r = v_of_box z2) /\ t = [])
    = fun b p z1 z2 _ -> if b then unbox_p z1 else unbox_p z2
  in
  
  let final_sb: b:bool -> x:Box int alice_s -> y:Box int bob_s -> unit
                -> Wys int (pre (Mode Sec ab)) (fun m0 r t -> (b     ==> r = v_of_box x) /\
                                                              (not b ==> r = v_of_box y) /\ t = [])
    = fun b x y _ -> if b then unbox_s x else unbox_s y
  in
  
  let a = as_sec ab (cmp x1 y1) in
  let x3 = as_par alice_s (selector a alice x2 x1) in
  let y3 = as_par bob_s (selector a bob y1 y2) in
  let d = as_sec ab (cmp x3 y3) in
  as_sec ab (final_sb d x3 y3)

open FStar.Relational

val opt_median_secure_alice: x1:Box int alice_s -> x2:Box int alice_s
                             -> y1:Box int bob_s -> y2:Box int bob_s
                             -> y1':Box int bob_s -> y2':Box int bob_s
                             -> unit
                             -> Wys2 (rel int int) (fun m0 -> m0 = R (Mode Par ab) (Mode Par ab) /\
                                                      median_pre x1 x2 y1 y2 /\ median_pre x1 x2 y1' y2')
                                             (fun m0 r t -> R.l r = R.r r ==> R.l t = R.r t)
let opt_median_secure_alice x1 x2 y1 y2 y1' y2' _ =
  compose_wys2 (optimized_median x1 x2 y1 y2) (optimized_median x1 x2 y1' y2')

val opt_median_secure_bob: x1:Box int alice_s -> x2:Box int alice_s
                           -> x1':Box int alice_s -> x2':Box int alice_s
                           -> y1:Box int bob_s -> y2:Box int bob_s
                           -> unit
                           -> Wys2 (rel int int) (fun m0 -> m0 = R (Mode Par ab) (Mode Par ab) /\
                                                      median_pre x1 x2 y1 y2 /\ median_pre x1' x2' y1 y2)
                                           (fun m0 r t -> R.l r = R.r r ==> R.l t = R.r t)
let opt_median_secure_bob x1 x2 x1' x2' y1 y2 _ =
  compose_wys2 (optimized_median x1 x2 y1 y2) (optimized_median x1' x2' y1 y2)
