(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/ordset.fsi $LIB/ordmap.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst
 --*)

module Wysteria

open OrdSet
open Heap

open Prims.STATE

(**********)

type prin

val p_cmp: f:(prin -> prin -> Tot bool){total_order prin f}

type prins = s:ordset prin p_cmp{not (s = empty)}

type eprins = ordset prin p_cmp

(* TODO: FIXME: Implement these *)
val prin_to_nat: prin -> Tot nat

val injective_prin_to_nat_mapping:
  unit -> Lemma (requires (True)) (ensures (forall p1 p2. prin_to_nat p1 = prin_to_nat p2 ==> p1 = p2))

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

assume val moderef : ref mode

kind Requires         = mode -> Type
kind Ensures (a:Type) = mode -> a -> Type

effect Wys (a:Type) (req:Requires) (ens:Ensures a) =
  STATE a (fun (p:a -> heap -> Type) (h0:heap) -> req (sel h0 moderef) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (sel h0 moderef) x ==> p x h1))
          (fun (p:a -> heap -> Type) (h0:heap) -> req (sel h0 moderef) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (sel h0 moderef) x ==> p x h1))

(**********)

type Box: Type -> prins -> Type

val v_of_box : #a:Type -> #ps:prins -> x:Box a ps -> GTot a

(* if a Type value can be boxed for ps  *)
type can_box: a:Type -> ps:prins -> Type

assume Canbox_nat : (forall ps. can_box nat ps)
assume Canbox_bool: (forall ps. can_box bool ps)
assume Canbox_box : (forall (a:Type) (ps':prins) ps.
                     subset ps' ps ==> can_box (Box a ps') ps)
assume Canbox_option: (forall (a:Type) ps. can_box a ps ==>
                                           can_box (option a) ps)
assume Canbox_prod: (forall (a:Type) (b:Type) ps.
                     (can_box a ps /\ can_box b ps) ==> can_box (a * b) ps)
(* TODO: FIXME: how ? *)
(*assume Canbox_refinement: (forall (a:Type) (b:a -> Type) ps.
                           can_box a ps ==> can_box (y:a{b y}) ps)*)

(**********)

type Wire: Type -> Type

val w_contains: #a:Type -> prin -> Wire a -> Tot bool
val w_empty   : #a:Type -> Tot (w:Wire a{forall p. not (w_contains p w)})
val w_select  : #a:Type -> p:prin -> w:Wire a{w_contains p w} -> Tot a
(* TODO: FIXME: implement const_on *)
val w_const_on: #a:Type -> eps:eprins -> x:a
                -> Tot (w:Wire a{forall p. (mem p eps <==> w_contains p w) /\
                                           (w_contains p w ==> w_select p w = x)})

val w_concat  :
  #a:Type -> w1:Wire a -> w2:Wire a{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> Tot (w:Wire a
          {forall p. (w_contains p w1 ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                     (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                     (w_contains p w  ==> (w_contains p w1 \/ w_contains p w2))})

val w_dom: #a:Type -> w:Wire a -> Tot (ps:prins{forall p. mem p ps <==> w_contains p w})


(* if type can be wired *)
type can_wire: Type -> Type

assume Canwire_nat : can_wire nat
assume Canwire_bool: can_wire bool
assume Canwire_prod: forall (a:Type) (b:Type). (can_wire a /\ can_wire b) ==>
                                               can_wire (a * b)


(**********)

type DelPar (m:mode) (ps:prins) = Mode.m m = Par /\ subset ps (Mode.ps m)

val as_par: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys (Box a ps) (fun m0   -> req_f (Mode Par ps) /\
                                           DelPar m0 ps        /\
                                           can_box a ps)
                              (fun m0 r -> ens_f (Mode Par ps) (v_of_box r))
  
(*****)

type DelSec (m:mode) (ps:prins) = ps = Mode.ps m

val as_sec: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys a (fun m0   -> req_f (Mode Sec ps) /\ DelSec m0 ps)
                     (fun m0 r -> ens_f (Mode Sec ps) r)

(*****)

type CanUnboxPC (mode_ps:eprins) (ps:prins) = b2t (subset mode_ps ps)

type CanUnboxP (m:mode) (ps:prins) = Mode.m m = Par /\ CanUnboxPC (Mode.ps m) ps

val unbox_p: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0   -> CanUnboxP m0 ps)
                      (fun m0 r -> b2t (r = v_of_box x))

(*****)

(* TODO: FIXME: ideally we can do with not (intersect (Mode.ps m) ps = empty 
 * but that requires examples to have to help prove this *)

type CanUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ subset ps (Mode.ps m)

val unbox_s: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0   -> CanUnboxS m0 ps)
                      (fun m0 r -> b2t (r = v_of_box x))

(*****)

type CanBoxP (a:Type) (m:mode) (ps:prins) =
  Mode.m m = Par /\ can_box a ps /\ subset ps (Mode.ps m)

val box_p: #a:Type -> x:a -> ps:prins
           -> Wys (Box a ps) (fun m0   -> CanBoxP a m0 ps)
                             (fun m0 r -> b2t (v_of_box r = x))

(*****)

type CanMkWireP (a:Type) (m:mode) (ps':prins) (eps:eprins) =
  Mode.m m = Par /\ can_wire a /\ CanUnboxPC eps ps' /\ subset eps (Mode.ps m)

val mkwire_p: #a:Type -> #ps':prins -> eps:eprins -> x:Box a ps'
              -> Wys (Wire a) (fun m0   -> CanMkWireP a m0 ps' eps)
                              (fun m0 r -> Let (v_of_box #a #ps' x) (fun y -> b2t (r = w_const_on #a eps y)))

(*****)

(*
 * CanUnboxP since all parties must know the domain of wire bundle
 *)
type CanMkWireS (a:Type) (m:mode) (eps:eprins) =
  Mode.m m = Sec /\ can_wire a /\ subset eps (Mode.ps m)

val mkwire_s: #a:Type -> eps:eprins -> x:a
              -> Wys (Wire a) (fun m0   -> CanMkWireS a m0 eps)
                              (fun m0 r -> b2t (r = w_const_on #a eps x))

(*type CanMkWireSS (ps:Box prin) (mode_ps:prins) =
  CanUnboxP ps mode_ps /\ mem (v_of_box ps) mode_ps

val mkwire_ss: #a:Type -> ps:Box prin -> x:a
               -> Wys (Wire a) (fun m0   -> Mode.p_or_s m0 = Sec /\ CanMkWireSS ps (Mode.ps m0))
                               (fun m0 r -> b2t (r = const_on (singleton (v_of_box ps)) x))*)

(*****)

type CanProjWireP (#a:Type) (m:mode) (x:Wire a) (p:prin) =
  Mode.m m = Par /\ Mode.ps m = singleton p /\ w_contains p x

val projwire_p: #a:Type -> x:Wire a -> p:prin{w_contains p x}
                -> Wys a (fun m0   -> CanProjWireP m0 x p)
                         (fun m0 r -> b2t (r = w_select p x))

(*****)

type CanProjWireS (#a:Type) (m:mode) (x:Wire a) (p:prin) =
  Mode.m m = Sec /\ mem p (Mode.ps m) /\ w_contains p x

val projwire_s: #a:Type -> x:Wire a -> p:prin{w_contains p x}
                -> Wys a (fun m0   -> CanProjWireS m0 x p)
                         (fun m0 r -> b2t (r = w_select p x))

(*****)

(*
 * DisjointDom ?
 *)
 
type CanConcatWire (#a:Type) (x:Wire a) (y:Wire a) =
  forall p. w_contains p x ==> not (w_contains p y)
 
val concat_wire: #a:Type -> x:Wire a -> y:Wire a{CanConcatWire x y}
                 -> Wys (Wire a) (fun m0   -> CanConcatWire x y)
                                 (fun m0 r -> b2t (r = w_concat x y))

(*****)

(*type Share: Type -> Type

val v_of_sh: #a:Type -> Share a -> GTot a

val ps_of_sh: #a:Type -> Share a -> GTot prins

val mk_share: #a:Type -> x:a -> Wys (Share a) (fun m0   -> b2t (Mode.p_or_s m0 = Sec))
                                              (fun m0 r -> v_of_sh r = x /\
                                                           ps_of_sh r = Mode.ps m0)

val comb_share: #a:Type -> x:Share a -> Wys a (fun m0   -> Mode.p_or_s m0 = Sec /\
                                                           Mode.ps m0 = ps_of_sh x)
                                              (fun m0 r -> b2t (r = v_of_sh x))*)

(*********************************)

val read: #a:Type -> unit -> Wys a (fun m0 -> Mode.m m0 = Par /\
                                              (exists p. Mode.ps m0 = singleton #prin #p_cmp p))
                                   (fun m0 r -> True)

(*val read_p: #a:Type -> unit -> Wys (Wire a) (fun m0 -> b2t (Mode.m m0 = Par))
                                            (fun m0 r -> HasDom r (Mode.ps m0))
*)

val alice  : prin
val bob    : prin
val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

let alice_s   = singleton #prin #p_cmp alice
let bob_s     = singleton #prin #p_cmp bob
let charlie_s = singleton #prin #p_cmp charlie

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

(*val list_to_set: #a:Type -> l:list a
                 -> Pure (set a) True (fun r -> (forall x. List.mem x l <==> mem x r))

val set_to_list: #a:Type -> s:set a
                 -> Pure (list a) True (fun r -> (forall x. List.mem x r <==> mem x s))

val dom_of_wire: #a:Type -> w:Wire a
                 -> Pure (list prin) True (fun r -> (forall x. List.mem x r <==> Map.contains w x))

val empty_wire: (w:Wire 'a{HasDom w Set.empty})*)
