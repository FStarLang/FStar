module Wysteria

open Set
open Heap

open Prims.STATE

type prin

type prins = set prin

type p_or_s =
  | Par
  | Sec

type mode =
  | Mode: p_or_s:p_or_s -> ps:prins -> mode

assume val moderef : ref mode

(* TODO: make it abstract to the clients *)
type Wire (a:Type) = Map.t prin a

type Box: Type -> Type

val v_of_box: #a:Type -> x:Box a -> GTot a

val ps_of_box: #a:Type -> x:Box a -> GTot prins

kind Requires         = mode -> Type
kind Ensures (a:Type) = mode -> a -> Type

effect Wys (a:Type) (req:Requires) (ens:Ensures a) =
  STATE a (fun (p:a -> heap -> Type) (h0:heap) -> req (sel h0 moderef) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (sel h0 moderef) x ==> p x h1))
          (fun (p:a -> heap -> Type) (h0:heap) -> req (sel h0 moderef) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (sel h0 moderef) x ==> p x h1))


(*****)

type DelPar (m:mode) (ps:prins) =
  Mode.p_or_s m = Par /\ subset ps (Mode.ps m)

val as_par: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys (Box a) (fun m0   -> DelPar m0 ps /\ req_f (Mode Par ps))
                           (fun m0 r -> ps_of_box r = ps /\
                                        ens_f (Mode Par ps) (v_of_box r))

(*****)

type DelSec (m:mode) (ps:prins) = ps = (Mode.ps m)

val as_sec: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys a (fun m0   -> DelSec m0 ps /\ req_f (Mode Sec ps))
                     (fun m0 r -> ens_f (Mode Sec ps) r)

(*****)

type CanUnboxP (#a:Type) (x:Box a) (mode_ps:prins) = b2t (subset mode_ps (ps_of_box x))

val unbox_p: #a:Type -> x:Box a
             -> Wys a (fun m0   -> Mode.p_or_s m0 = Par /\ CanUnboxP x (Mode.ps m0))
                      (fun m0 r -> b2t (r = v_of_box x))

(*****)

(*
 * we could afford intersection of ps_of_box x and Mode.ps m0 to be non-empty,
 * since it's enough for one party to provide the value, all need not be present
 *)

type CanUnboxS (#a:Type) (x:Box a) (mode_ps:prins) = b2t (subset (ps_of_box x) mode_ps)

val unbox_s: #a:Type -> x:Box a
             -> Wys a (fun m0   -> Mode.p_or_s m0 = Sec /\ CanUnboxS x (Mode.ps m0))
                      (fun m0 r -> b2t (r = v_of_box x))

(*****)

type CanBoxP (#a:Type) (ps:prins) (mode_ps:prins) = b2t (subset ps mode_ps)

val box_p: #a:Type -> x:a -> ps:prins
           -> Wys (Box a) (fun m0   -> Mode.p_or_s m0 = Par /\ CanBoxP ps (Mode.ps m0))
                          (fun m0 r -> ps_of_box r = ps /\ v_of_box r = x)

(*****)

open Map

(*****)

type CanMkWireP (#a:Type) (ps:prins) (x:Box a) (mode_ps: prins) =
  CanUnboxP x ps /\ subset ps mode_ps

val mkwire_p: #a:Type -> ps:prins -> x:Box a
              -> Wys (Wire a) (fun m0   -> Mode.p_or_s m0 = Par /\ CanMkWireP ps x (Mode.ps m0))
                              (fun m0 r -> b2t (r = const_on ps (v_of_box x)))

(*****)

(*
 * CanUnboxP since all parties must know the domain of wire bundle
 *)

type CanMkWireS (ps:Box prins) (mode_ps:prins) =
  CanUnboxP ps mode_ps /\ subset (v_of_box ps) mode_ps

val mkwire_s: #a:Type -> ps:Box prins -> x:a
              -> Wys (Wire a) (fun m0   -> Mode.p_or_s m0 = Sec /\ CanMkWireS ps (Mode.ps m0))
                              (fun m0 r -> b2t (r = const_on (v_of_box ps) x))

type CanMkWireSS (ps:Box prin) (mode_ps:prins) =
  CanUnboxP ps mode_ps /\ mem (v_of_box ps) mode_ps

val mkwire_ss: #a:Type -> ps:Box prin -> x:a
               -> Wys (Wire a) (fun m0   -> Mode.p_or_s m0 = Sec /\ CanMkWireSS ps (Mode.ps m0))
                               (fun m0 r -> b2t (r = const_on (singleton (v_of_box ps)) x))

(*****)

type CanProjWireP (#a:Type) (x:Wire a) (p:prin) (mode_ps:prins) =
  mode_ps = singleton p /\ contains x p

val projwire_p: #a:Type -> x:Wire a -> p:prin
                -> Wys a (fun m0   -> Mode.p_or_s m0 = Par /\ CanProjWireP x p (Mode.ps m0))
                         (fun m0 r -> b2t (r = sel x p))

(*****)

type CanProjWireS (#a:Type) (x:Wire a) (p:prin) (mode_ps:prins) =
  mem p mode_ps /\ contains x p

val projwire_s: #a:Type -> x:Wire a -> p:prin
                -> Wys a (fun m0   -> Mode.p_or_s m0 = Sec /\ CanProjWireS x p (Mode.ps m0))
                         (fun m0 r -> b2t (r = sel x p))

(*****)

(*
 * DisjointDom ?
 *)

val concat_wire: #a:Type -> x:Wire a -> y:Wire a
                 -> Wys (Wire a) (fun m0   -> True)
                                 (fun m0 r -> b2t (r = concat x y))

(*****)

type Share: Type -> Type

val v_of_sh: #a:Type -> Share a -> GTot a

val ps_of_sh: #a:Type -> Share a -> GTot prins

val mk_share: #a:Type -> x:a -> Wys (Share a) (fun m0   -> b2t (Mode.p_or_s m0 = Sec))
                                              (fun m0 r -> v_of_sh r = x /\
                                                           ps_of_sh r = Mode.ps m0)

val comb_share: #a:Type -> x:Share a -> Wys a (fun m0   -> Mode.p_or_s m0 = Sec /\
                                                           Mode.ps m0 = ps_of_sh x)
                                              (fun m0 r -> b2t (r = v_of_sh x))

(*********************************)

val read: #a:Type -> unit -> Wys a (fun m0 -> Mode.p_or_s m0 = Par /\
                                              (exists p. Mode.ps m0 = singleton p))
                                   (fun m0 r -> True)

val read_p: #a:Type -> unit -> Wys (Wire a) (fun m0 -> b2t (Mode.p_or_s m0 = Par))
                                            (fun m0 r -> HasDom r (Mode.ps m0))

val alice  : prin
val bob    : prin
val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

let alice_s   = singleton alice
let bob_s     = singleton bob
let charlie_s = singleton charlie

let ab   = union alice_s bob_s
let bc   = union bob_s charlie_s
let abc  = union charlie_s ab

let p_a   = Mode Par alice_s
let p_b   = Mode Par bob_s
let p_c   = Mode Par charlie_s

let p_ab  = Mode Par ab
let p_abc = Mode Par abc

let s_ab  = Mode Sec ab
let s_abc = Mode Sec abc

val list_to_set: #a:Type -> l:list a
                 -> Pure (set a) True (fun r -> (forall x. List.mem x l <==> mem x r))

(* unimplemented *)
val set_to_list: #a:Type -> s:set a
                 -> Pure (list a) True (fun r -> (forall x. List.mem x r <==> mem x s))

val dom_of_wire: #a:Type -> w:Wire a
                 -> Pure (list prin) True (fun r -> (forall x. List.mem x r <==> Map.contains w x))

val empty_wire: (w:Wire 'a{HasDom w Set.empty})
