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

(*
 * mode should be able to project all values from the wire bundle
 *)
type wfold_pre (#b:Type) (#eps:eprins) (m:mode) (ps:eprins) (w:Wire b eps) =
  Mode.m m = Sec /\ (forall p. mem p ps ==> (w_contains p w /\ CanProjWireS #b m w p))

(* we can give a more precise type to p arg of f, p:prin{mem p ps}, but then unification in the recursive call fails *)
val wfold: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
           -> #eps:eprins
           -> ps:eprins
           -> w:Wire b eps{forall p. mem p ps ==> w_contains p w}
           -> =f:(a -> (p:prin{w_contains p w}) -> x:b{w_select p w = x} -> Wys a req_f ens_f)
           -> a
           -> Wys a (fun m0 -> wfold_pre #b m0 ps w /\ req_f m0) (fun m0 r t -> True)
              (decreases (size ps))
let rec wfold #eps ps w f x =
  if ps = empty () then x
  else
    let p = choose ps in
    let y = projwire_s p w in
    wfold (remove p ps) w f (f x p y)

type waps_pre (#a:Type) (#b:Type) (#eps:eprins) (m:mode) (ps:eprins) (w:Wire a eps) =
  Mode.m m = Sec /\ (forall p. mem p ps ==> (w_contains p w /\ CanProjWireS #a m w p /\ CanMkWireS b m (singleton p)))

val waps: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> trace -> Type)
          -> #eps:eprins
          -> ps:prins
          -> w:Wire a eps{forall p. mem p ps ==> w_contains p w}
          -> =f:(p:prin{w_contains p w} -> x:a{w_select p w = x} -> Wys b req_f ens_f)
          -> Wys (Wire b ps) (fun m0 -> waps_pre #a #b m0 ps w /\ req_f m0) post
             (decreases (size ps))
let rec waps #eps ps w f =
  let p = choose ps in
  let ps' = remove p ps in
  let y = projwire_s p w in
  let wp = mkwire_s (singleton p) (f p y) in
  if ps' = empty () then
    let _ = eq_lemma ps (singleton p) in
    wp
  else
    let w' = waps ps' w f in
    let _ = eq_lemma ps (union (singleton p) ps') in
    concat_wire wp w'

val gps_sec: ps:prins -> w:Wire int ps -> unit
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

val gps: unit -> Wys unit (pre (Mode Par abc)) post
let gps _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire w1 wc in

  let t1 = as_par ab (gps_sec ab w1) in

  let _ = cut (b2t (subset abc abc)) in
  let _ = cut (can_box (Wire prin abc) abc) in
  let t2 = as_par abc (gps_sec abc w2) in
  ()
;;

let x = main abc gps in ()
