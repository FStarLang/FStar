(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst
 --*)

module Wysteria

(**********)

(* declare prin and prins types and API, implemented these as ffi calls *)
type prin
type eprins

val empty: eprins

type prins = s:eprins{s =!= empty}

val mem      : p:prin -> s:eprins -> Tot (b:bool{b ==> not (s = empty)})
val singleton: p:prin -> Pure prins (True) (fun s -> s =!= empty /\ (forall p'. mem p' s = (p = p')))
val subset   : s1:eprins -> s2:eprins -> Pure bool (True) (fun b -> b <==> (forall p. mem p s1 ==> mem p s2))
val union    : s1:eprins -> s2:eprins -> Pure eprins (True) (fun s -> ((s1 =!= empty \/ s2 =!= empty) ==> s =!= empty) /\
                                                                      (forall p. mem p s = (mem p s1 || mem p s2)))

val size     : s:eprins -> Pure nat (True) (fun n -> n = 0 <==> s = empty)
val choose   : s:prins -> Pure prin (True) (fun p -> b2t (mem p s))
val remove   : p:prin -> s:prins -> Pure eprins (b2t (mem p s)) (fun s' -> (forall p'. ((mem p' s /\ p' =!= p) ==> mem p' s') /\
                                                                                       (mem p' s' ==> mem p' s)) /\
                                                                           not (mem p s')                        /\
                                                                           size s' = size s - 1)

assume val eq_lemma: s1:eprins -> s2:eprins -> Lemma (requires (forall p. mem p s1 = mem p s2)) (ensures (s1 = s2)) [SMTPat (s1 = s2)]
(**********)

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

(**********)

open Heap

let moderef : ref (option mode) = alloc None(* private *)

kind Requires         = mode -> Type
kind Ensures (a:Type) = mode -> a -> Type

effect Wys (a:Type) (req:Requires) (ens:Ensures a) =
  STATE a (fun (p:a -> heap -> Type) (h0:heap) -> is_Some (sel h0 moderef) /\ req (Some.v (sel h0 moderef)) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (Some.v (sel h0 moderef)) x ==> p x h1))
          (fun (p:a -> heap -> Type) (h0:heap) -> is_Some (sel h0 moderef) /\ req (Some.v (sel h0 moderef)) /\ (forall x h1. sel h1 moderef = sel h0 moderef /\ ens (Some.v (sel h0 moderef)) x ==> p x h1))

(**********)
type Box: Type -> prins -> Type

val v_of_box : #a:Type -> #ps:prins -> Box a ps -> GTot a

type can_box: a:Type -> ps:prins -> Type

assume Canbox_nat   : (forall ps. can_box nat ps)
assume Canbox_int   : (forall ps. can_box int ps)
assume Canbox_bool  : (forall ps. can_box bool ps)
assume Canbox_prin  : (forall ps. can_box prin ps)
assume Canbox_prins : (forall ps. can_box prins ps)
assume Canbox_eprins: (forall ps. can_box eprins ps)
assume Canbox_box   : (forall (a:Type) (ps':prins) (ps:prins).
                       subset ps' ps ==> can_box (Box a ps') ps)
assume Canbox_option: (forall (a:Type) ps. can_box a ps ==>
                                           can_box (option a) ps)
assume Canbox_prod:   (forall (a:Type) (b:Type) ps.
                       (can_box a ps /\ can_box b ps) ==> can_box (a * b) ps)

(**********)

type Wire: Type -> Type

val w_contains: #a:Type -> prin -> Wire a -> GTot bool
val w_empty   : #a:Type -> GTot (w:Wire a{forall p. not (w_contains p w)})
val w_select  : #a:Type -> p:prin -> w:Wire a{w_contains p w} -> GTot a
val w_const_on: #a:Type -> eps:eprins -> x:a
                -> GTot (w:Wire a{forall p. (mem p eps <==> w_contains p w) /\
                                            (w_contains p w ==> w_select p w = x)})

(* TODO: FIXME: Make this ghost, add a concat to the OrdMap lib and use that for computation *)
val w_concat  :
  #a:Type -> w1:Wire a -> w2:Wire a{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> Tot (w:Wire a
          {forall p. (w_contains p w1 ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                     (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                     (w_contains p w  ==> (w_contains p w1 \/ w_contains p w2))})

val w_dom: #a:Type -> w:Wire a -> GTot (ps:eprins{forall p. mem p ps <==> w_contains p w})

type can_wire: Type -> Type

assume Canwire_nat   : can_wire nat
assume Canwire_int   : can_wire int
assume Canwire_bool  : can_wire bool
assume Canwire_prin  : can_wire prin
assume Canwire_prins : can_wire prins
assume Canwire_eprins: can_wire eprins
assume Canwire_prod  : forall (a:Type) (b:Type). (can_wire a /\ can_wire b) ==>
                                                 can_wire (a * b)

assume Can_wire_implies_can_box: forall (a:Type) ps. can_wire a ==> can_box a ps
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

(* Ideally we can do with not (intersect (Mode.ps m) ps = empty
 * but that requires examples to have to help prove this.
 * Metatheory is more precise, in that it needs intersection as non-empty *)

type CanUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ subset ps (Mode.ps m)

val unbox_s: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0   -> CanUnboxS m0 ps)
                      (fun m0 r -> b2t (r = v_of_box x))

(*****)

type CanBox (a:Type) (mode_ps:prins) (ps:prins) =
  can_box a ps /\ subset ps mode_ps

val box: #a:Type -> x:a -> ps:prins
         -> Wys (Box a ps) (fun m0   -> CanBox a (Mode.ps m0) ps)
                           (fun m0 r -> b2t (v_of_box r = x))

(*****)

type CanMkWireP (a:Type) (m:mode) (ps':prins) (eps:eprins) =
  Mode.m m = Par /\ can_wire a /\ CanUnboxPC eps ps' /\ subset eps (Mode.ps m)

val mkwire_p: #a:Type -> #ps':prins -> eps:eprins -> x:Box a ps'
              -> Wys (Wire a) (fun m0   -> CanMkWireP a m0 ps' eps)
                              (fun m0 r -> Let (v_of_box #a #ps' x) (fun y -> b2t (r = w_const_on #a eps y)))

(*****)

type CanMkWireS (a:Type) (m:mode) (eps:eprins) =
  Mode.m m = Sec /\ can_wire a /\ subset eps (Mode.ps m)

val mkwire_s: #a:Type -> eps:eprins -> x:a
              -> Wys (Wire a) (fun m0   -> CanMkWireS a m0 eps)
                              (fun m0 r -> b2t (r = w_const_on #a eps x))

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

type CanConcatWire (#a:Type) (x:Wire a) (y:Wire a) =
  forall p. w_contains p x ==> not (w_contains p y)

val concat_wire: #a:Type -> x:Wire a -> y:Wire a{CanConcatWire x y}
                 -> Wys (Wire a) (fun m0   -> CanConcatWire x y)
                                 (fun m0 r -> b2t (r = w_concat x y))

(*****)

val main: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> Type)
          -> ps:prins
          -> =f:(unit -> Wys a req_f ens_f)
          -> All a (fun h0 -> req_f (Mode Par ps))
                   (fun h0 r h1 -> is_V r /\ ens_f (Mode Par ps) (V.v r))

(*****)

(* these are also ffi calls *)

val read: #a:Type -> unit -> Wys a (fun m0 -> Mode.m m0 = Par /\
                                              (exists p. Mode.ps m0 = singleton p))
                                   (fun m0 r -> True)

val alice  : prin
val bob    : prin
val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

(*****)

val wprint: #a:Type -> x:a -> ML unit
