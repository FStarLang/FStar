(*--build-config
    options:--admit_fsi Set --admit_fsi Map --admit_fsi Wysteria;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/map.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst wysteria.fsi
 --*)

module WLib

open Map
open Set

open Wysteria

val wfold_helper: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
                  -> w:Wire b
                  -> =f:(a -> (p:prin{contains w p}) -> x:b{sel w p = x} -> Wys a req_f ens_f)
                  -> a
                  -> l:list prin
                  -> Wys a (fun m0 -> Mode.p_or_s m0 = Sec /\
                                      (forall y. List.mem y l ==> CanProjWireS w y (Mode.ps m0)) /\
                                      req_f m0)
                           (fun m0 r -> True)
let rec wfold_helper w f x l =
 match l with
   | [] -> x
   | hd::tl ->
     let y = projwire_s w hd in
     wfold_helper w f (f x hd y) tl

(*
 * mode should be able to project all values from the wire bundle
 *)
type wfold_pre (#b:Type) (w:Wire b) (mode_ps:prins) =
  (forall p. contains w p ==> CanProjWireS w p mode_ps)

val wfold: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
           -> w:Wire b
           -> =f:(a -> (p:prin{contains w p}) -> x:b{sel w p = x} -> Wys a req_f ens_f)
           -> a
           -> Wys a (fun m0   -> Mode.p_or_s m0 = Sec /\ wfold_pre w (Mode.ps m0) /\ req_f m0)
                    (fun m0 r -> True)
let wfold w f x =
  let l = dom_of_wire w in
  wfold_helper w f x l


val box_l: #a:Type -> ps:prins -> l:list a
           -> Wys (list (Box a)) (fun m0   -> Mode.p_or_s m0 = Par /\ CanBoxP ps (Mode.ps m0))
                                 (fun m0 r -> (forall b. List.mem b r ==> ps_of_box b = ps /\
                                                                          List.mem (v_of_box b) l) /\
                                              (forall x. List.mem x l ==> (exists b. List.mem b r /\ v_of_box b = x)))
let rec box_l ps l = match l with
  | []     -> []
  | hd::tl ->
    let b = box_p hd ps in
    let l' = box_l ps tl in
    b::l'

(*
 * mode should be able to project all list prins
 * mode should be able to unbox the list elts in par as well as sec
 * par since wire domain has to be known to all parties
 *)
val waps: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
          -> l:list (Box prin)
          -> w:Wire a
          -> =f:(p:prin{contains w p} -> x:a{sel w p = x} -> Wys b req_f ens_f)
          -> Wys (Wire b) (fun m0 -> Mode.p_or_s m0 = Sec /\
                                     (forall b. List.mem b l ==> (CanProjWireS w (v_of_box b) (Mode.ps m0) /\
                                                                  CanUnboxS b (Mode.ps m0) /\ CanUnboxP b (Mode.ps m0))) /\
                                     req_f m0)
                          (fun m0 r -> True)
let rec waps l w f =
  match l with
    | []     -> empty_wire
    | hd::tl ->
      let w1 = waps tl w f in
      let p = unbox_s hd in
      let x = projwire_s w p in
      let w2 = mkwire_ss hd (f p x) in
      concat_wire w1 w2


val wapp_helper: #a:Type -> #b:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> b -> Type)
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
let wapp w f = wapp_helper w f (dom_of_wire w)
