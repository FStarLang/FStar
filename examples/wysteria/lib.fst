(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi Set --admit_fsi Wysteria;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/ordset.fsi $LIB/ordmap.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst wysteria.fsi
 --*)

module WLib

open OrdMap
open OrdSet

open Wysteria

val wfold_helper: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
                  -> w:Wire b
                  -> =f:(a -> (p:prin{w_contains p w}) -> x:b{w_select p w = x} -> Wys a req_f ens_f)
                  -> a
                  -> ps:eprins{forall p. mem p ps ==> w_contains p w}
                  -> Wys a (fun m0 -> Mode.m m0 = Sec                                 /\
                                      (forall y. mem y ps ==> CanProjWireS #b m0 w y) /\
                                      req_f m0)
                           (fun m0 r -> True)
let rec wfold_helper w f x ps =
  if ps = empty then x
  else
    let Some p = choose ps in
    let y = projwire_s w p in
    wfold_helper w f (f x p y) (remove p ps)

(*
 * mode should be able to project all values from the wire bundle
 *)
type wfold_pre (#b:Type) (m:mode) (w:Wire b) =
  (forall p. w_contains p w ==> CanProjWireS #b m w p)

val wfold: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
           -> w:Wire b
           -> =f:(a -> (p:prin{w_contains p w}) -> x:b{w_select p w = x} -> Wys a req_f ens_f)
           -> a
           -> Wys a (fun m0   -> Mode.m m0 = Sec /\ wfold_pre m0 w /\ req_f m0)
                    (fun m0 r -> True)
let wfold w f x =
  let ps = w_dom w in
  wfold_helper w f x ps

val waps_helper: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
                 -> w:Wire a
                 -> =f:(p:prin{w_contains p w} -> x:a{w_select p w = x} -> Wys b req_f ens_f)
                 -> ps:eprins{forall p. mem p ps ==> w_contains p w}
                 -> Wys (Wire b) (fun m0 -> Mode.m m0 = Sec                                        /\
                                            (forall y. mem y ps ==> CanProjWireS #a m0 w y)        /\
                                            (forall y. mem y ps ==> CanMkWireS b m0 (singleton y)) /\
                                            req_f m0)
                                 (fun m0 r -> b2t (w_dom r = ps))
let rec waps_helper (#a:Type) (#b:Type) (#req_f:mode -> Type) (#ens_f:mode -> b -> Type) w f ps =
  if ps = empty then w_empty
  else
    let Some p = choose ps in
    let y = projwire_s w p in
    let wp = mkwire_s (singleton p) (f p y) in
    let ps_rest = remove p ps in
    let w' = waps_helper #a #b #req_f #ens_f w f ps_rest in
    w_concat wp w'

val waps: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
          -> w:Wire a
          -> =f:(p:prin{w_contains p w} -> x:a{w_select p w = x} -> Wys b req_f ens_f)
          -> Wys (Wire b) (fun m0 -> Mode.m m0 = Sec                                        /\
                                     (forall y. w_contains y w ==> CanProjWireS #a m0 w y)        /\
                                     (forall y. w_contains y w ==> CanMkWireS b m0 (singleton y)) /\
                                     req_f m0)
                          (fun m0 r -> True)
let rec waps w f =
  let ps = w_dom w in
  waps_helper w f ps

(*val wapp_helper: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
                 -> w:Wire a
                 -> =f:(p:prin{contains w p} -> x:a{sel w p = x} -> Wys b req_f ens_f)
                 -> l:list prin
                 -> Wys (Wire b) (fun m0 -> (forall p. List.mem p l ==> contains w p) /\
                                            (forall p. contains w p ==> (DelPar m0 (singleton p) /\
                                                                         req_f (Mode Par (singleton p)))))
                                 (fun m0 r -> True)
let rec wapp_helper 'a 'b 'r 'e w f l =
  match l with
    | []     -> empty_wire
    | hd::tl ->
      let g: p:prin{contains w p} -> Wys 'b (fun m0 -> b2t (m0 = Mode Par (singleton p))) (fun m0 r -> True) =
        fun p ->
          let x = projwire_p w p in
          f p x
      in
      empty_wire

      (*
       * we would like to not pass all arguments to g.
       * but writing this fails and gives an error:
         let g: #b:Type -> (p:prin{contains w p}) ->
                           Wys b (fun m0 -> b2t (m0 = Mode Par (singleton p)))
       *)
      (*let g: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
             -> w:Wire a
             -> =f:(p:prin{contains w p} -> x:a{sel w p = x} -> Wys b req_f ens_f)
             -> (p:prin{contains w p})
             -> unit
             -> Wys b (fun m0 -> m0 = Mode Par (singleton p) /\ req_f m0) (fun m0 r -> True) =
        fun w f p _ ->
          let x = projwire_p w p in
          f p x
      in*)

      (*let w1 = wapp_helper w f tl in
      let x = as_par (singleton hd) (g w f hd) in //error here: expected type unit -> Wys b, got unit -> Wys b
      let w2 = mkwire_p (singleton hd) x in
      concat_wire w1 w2*)

val wapp: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
                     -> w:Wire a
                     -> =f:(p:prin{contains w p} -> x:a{sel w p = x} -> Wys b req_f ens_f)
                     -> Wys (Wire b) (fun m0   -> (forall p. contains w p ==> (DelPar m0 (singleton p) /\
                                                                               req_f (Mode Par (singleton p)))))
                                     (fun m0 r -> True)
let wapp w f = wapp_helper w f (dom_of_wire w)*)
