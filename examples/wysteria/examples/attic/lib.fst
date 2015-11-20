(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

module WLib

open Prins
open FFI
open Wysteria

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
          -> Wys (Wire b ps) (fun m0 -> waps_pre #a #b m0 ps w /\ req_f m0)
                             (fun m0 r t -> b2t (w_dom r = ps))
             (decreases (size ps))
let rec waps #eps ps w f =
  let p = choose ps in
  let ps' = remove p ps in
  let y = projwire_s p w in
  let wp = mkwire_s (singleton p) (f p y) in
  if ps' = empty () then
    let _ = assert (ps = singleton p) in
    wp
  else
    let w' = waps ps' w f in
    let _ = assert (ps = union (singleton p) ps') in
    concat_wire wp w'

type wapp_pre (#a:Type) (#b:Type) (#eps:eprins) (m:mode) (ps:eprins) (w:Wire a eps) (req_f: mode -> Type) =
  (forall p. mem p ps ==> (w_contains p w /\ DelPar m (singleton p)   /\
                           CanMkWireP b m (singleton p) (singleton p) /\
                           req_f (Mode Par (singleton p))))

val wapp: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> trace -> Type)
          -> #eps:eprins
          -> ps:prins
          -> w:Wire a eps{forall p. mem p ps ==> w_contains p w}
          -> =f:(p:prin{w_contains p w} -> x:a{w_select p w = x} -> Wys b req_f ens_f)
          -> Wys (Wire b ps) (fun m0 -> wapp_pre #a #b m0 ps w req_f)
                             (fun m0 r t -> b2t (w_dom r = ps))
             (decreases (size ps))
let rec wapp 'a 'b 'req_f 'ens_f #eps ps w f =
  let g: p:prin{mem p ps} -> unit -> Wys 'b (fun m0 -> m0 = Mode Par (singleton p) /\ 'req_f m0) (fun m0 r t -> True) =
    fun p _ ->
      let x = projwire_p p w in
      f p x
  in
  let p = choose ps in
  let ps' = remove p ps in
  let py = as_par (singleton p) (g p) in
  let wp = mkwire_p #'b #(singleton p) (singleton p) py in
  if ps' = empty () then
    let _ = assert (ps = singleton p) in
    wp
  else
    let w' = wapp (remove p ps) w f in
    let _ = assert (ps = union (singleton p) ps') in
    concat_wire wp w'
