(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
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

val mill8_sec: ps:prins
               -> w:Wire int ps
               -> unit
               -> Wys (option prin) (pre (Mode Par ps)) post
let mill8_sec ps w _ =

  let f: option (p:prin{w_contains p w})
          -> (p:prin{w_contains p w}) -> (y:int{w_select p w = y})
          -> Wys (option (p:prin{w_contains p w})) (pre (Mode Sec ps)) post =
    fun x p y ->
      if is_none x then mk_some p
      else
      	let p' = v_of_some x in
        let y' = projwire_s p' w in
        if y > y' then mk_some p else mk_some p'
  in

  let g:unit -> Wys (option (p:prin{w_contains p w})) (pre (Mode Sec ps)) (post #(option (p:prin{w_contains p w}))) =
    fun _ -> wfold ps w f (mk_none ())
  in

  let p = as_sec ps g in
  if is_none p then mk_none () else mk_some (v_of_some p)

val mill8: unit -> Wys bool (pre (Mode Par abc)) post
let mill8 _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire w1 wc in

  let _ = as_par abc (mill8_sec abc w2) in

  true
;;

let _ = main abc mill8 in ()

