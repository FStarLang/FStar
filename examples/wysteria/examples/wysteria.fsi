(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi Prins --admit_fsi FStar.IO;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../prins.fsi ffi.fst
 --*)

module Wysteria

open FStar.List

open Prins
open FFI

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type telt =
  | TMsg  : #a:Type -> x:a -> telt
  | TScope: ps:prins -> t:list telt -> telt

type trace = list telt

val rest_trace: t1:trace -> t2:trace -> Tot (option trace)

val last_elt: t:trace{is_Cons t} -> Tot telt

val all_but_last: t:trace{is_Cons t} -> Tot trace

val equal_trace_rest_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (b2t (t1 = t2)))
                                     (ensures (rest_trace t1 t2 = Some []))
                               [SMTPat (rest_trace t1 t2)]
                               
val rest_equal_trace_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (rest_trace t1 t2 = Some []))
                                     (ensures (b2t (t1 = t2)))
                               [SMTPat (rest_trace t1 t2)]
                               
val append_rest_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (append t1 t2 = t3))
                                (ensures (is_Some (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) = t2))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]

val rest_append_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (is_Some (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) = t2))
                                (ensures (append t1 t2 = t3))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]

val trace_assoc: t1:trace -> t2:trace -> t3:trace
                 -> Lemma (requires (is_Some (rest_trace t2 t1) /\ is_Some (rest_trace t3 t2)))
                          (ensures (is_Some (rest_trace t2 t1) /\ is_Some (rest_trace t3 t2) /\ is_Some (rest_trace t3 t1) /\
                                    Some.v (rest_trace t3 t1) = append (Some.v (rest_trace t2 t1))
                                                                       (Some.v (rest_trace t3 t2))))
                    [SMTPat (rest_trace t2 t1); SMTPat (rest_trace t3 t2)]

val last_elt_singleton_lemma: t:trace{is_Cons t}
                              -> Lemma (requires (all_but_last t = []))
                                       (ensures (t = [last_elt t]))
                                 [SMTPat (last_elt t); SMTPat (all_but_last t)]

val snoc_last_elt_lemma: elt:telt -> t:trace
                         -> Lemma (requires (True))
                                  (ensures (last_elt (t @ [elt]) = elt))
                            [SMTPat (last_elt (t @ [elt]))]

val snoc_all_but_last_lemma: elt:telt -> t:trace
                             -> Lemma (requires (True))
                                      (ensures (all_but_last (t @ [elt]) = t))
                            [SMTPat (all_but_last (t @ [elt]))]

val all_but_last_append_lemma: t:trace{is_Cons t} ->
                               Lemma (requires (True))
                                     (ensures (append (all_but_last t) ([last_elt t]) = t))
                               [SMTPat (append (all_but_last t) ([last_elt t]))]

(**********)

open FStar.Heap

//let moderef : ref (option mode) = alloc None (* private *)
assume val moderef : ref mode

let traceref: ref trace = alloc []

kind Requires         = mode -> Type
kind Ensures (a:Type) = mode -> a -> trace -> Type

type wys_encoding (a:Type) (req:Requires) (ens:Ensures a) (p:a -> heap -> Type) (h0:heap) =
  req (sel h0 moderef) /\
  (forall x h1. (sel h1 moderef = sel h0 moderef /\ is_Some (rest_trace (sel h1 traceref) (sel h0 traceref)) /\
                 ens (sel h0 moderef) x (Some.v (rest_trace (sel h1 traceref) (sel h0 traceref)))) ==> p x h1)

effect Wys (a:Type) (req:Requires) (ens:Ensures a) =
  STATE a (fun (p:a -> heap -> Type) (h0:heap) -> wys_encoding a req ens p h0)
          (fun (p:a -> heap -> Type) (h0:heap) -> wys_encoding a req ens p h0)

open FStar.Relational
open FStar.Comp

kind Requires2         = double mode -> Type
kind Ensures2 (a:Type) = double mode -> a -> double trace -> Type

type wys2_encoding (a:Type) (req:Requires2) (ens:Ensures2 a) (p:a -> heap2 -> Type) (h0:heap2) =
  req (R (sel (R.l h0) moderef) (sel (R.r h0) moderef)) /\
  (forall x h1. (sel (R.l h1) moderef = sel (R.l h0) moderef /\
                 sel (R.r h1) moderef = sel (R.r h0) moderef /\
                 is_Some (rest_trace (sel (R.l h1) traceref) (sel (R.l h0) traceref)) /\
                 is_Some (rest_trace (sel (R.r h1) traceref) (sel (R.r h0) traceref)) /\
                 ens (R (sel (R.l h0) moderef) (sel (R.r h0) moderef)) x
                     (R (Some.v (rest_trace (sel (R.l h1) traceref) (sel (R.l h0) traceref)))
                        (Some.v (rest_trace (sel (R.r h1) traceref) (sel (R.r h0) traceref))))) ==> p x h1)

effect Wys2 (a:Type) (req:Requires2) (ens:Ensures2 a) =
  STATE2 a (fun (p:a -> heap2 -> Type) (h0:heap2) -> wys2_encoding a req ens p h0)
           (fun (p:a -> heap2 -> Type) (h0:heap2) -> wys2_encoding a req ens p h0)

assume val compose_wys2: #a:Type -> #b:Type
                         -> #req0:(mode -> Type) ->#req1:(mode -> Type)
                         -> #ens0:(mode -> a -> trace -> Type) -> #ens1:(mode -> b -> trace -> Type)
                         -> =f0:(unit -> Wys a req0 ens0)
                         -> =f1:(unit -> Wys b req1 ens1)
                         -> Wys2 (rel a b) (fun m0     -> req0 (R.l m0) /\ req1 (R.r m0))
                                          (fun m0 r t -> ens0 (R.l m0) (R.l r) (R.l t) /\
                                                      ens1 (R.r m0) (R.r r) (R.r t))

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
assume Canbox_prod  : (forall (a:Type) (b:Type) ps.
                         (can_box a ps /\ can_box b ps) ==> can_box (a * b) ps)
assume Canbox_list  : (forall (a:Type) ps. can_box a ps ==> can_box (list a) ps)

assume Canbox_rel   : (forall (a:Type) (b:Type) ps.
                         (can_box a ps  /\ can_box b ps) ==> can_box (rel a b) ps)

(**********)

type Wire: Type -> eprins -> Type

val w_contains: #a:Type -> #eps:eprins -> prin -> Wire a eps -> GTot bool
val w_empty   : #a:Type -> GTot (w:Wire a (empty ()){forall p. not (w_contains p w)})
val w_select  : #a:Type -> #eps:eprins -> p:prin -> w:Wire a eps{w_contains p w} -> GTot a
val w_const_on: #a:Type -> eps:eprins -> x:a
                -> GTot (w:Wire a eps{forall p. (mem p eps <==> w_contains p w) /\
                                                (w_contains p w ==> w_select p w = x)})

(* TODO: FIXME: Make this ghost, add a concat to the OrdMap lib and use that for computation *)
val w_concat  :
  #a:Type -> #eps1:eprins -> #eps2:eprins
  -> w1:Wire a eps1 -> w2:Wire a eps2{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> Tot (w:Wire a (union eps1 eps2)
          {forall p. (w_contains p w1 ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                     (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                     (w_contains p w  ==> (w_contains p w1 \/ w_contains p w2))})

val w_dom: #a:Type -> #ps:prins -> w:Wire a ps -> GTot (ps:eprins{forall p. mem p ps <==> w_contains p w})

type can_wire: Type -> Type

assume Canwire_nat   : can_wire nat
assume Canwire_int   : can_wire int
assume Canwire_bool  : can_wire bool
assume Canwire_prin  : can_wire prin
assume Canwire_prins : can_wire prins
assume Canwire_eprins: can_wire eprins
assume Canwire_prod  : forall (a:Type) (b:Type). (can_wire a /\ can_wire b) ==>
                                                 can_wire (a * b)
assume Canwire_list  : (forall (a:Type). can_wire a ==> can_wire (list a))

assume Canbox_wire   : (forall (a:Type) (eps:eprins) (ps:prins).
                       subset eps ps ==> can_box (Wire a eps) ps)

assume Can_wire_implies_can_box: forall (a:Type) ps. can_wire a ==> can_box a ps

val w_contains_lemma: a:Type -> eps:prins -> w:Wire a eps -> p:prin
                      -> Lemma (requires (True)) (ensures (w_contains #a #eps p w =
		                                       mem p eps))
		        [SMTPat (w_contains #a #eps p w)]

(**********)

type DelPar (m:mode) (ps:prins) = Mode.m m = Par /\ subset ps (Mode.ps m)

val as_par: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys (Box a ps) (fun m0     -> req_f (Mode Par ps) /\
                                             DelPar m0 ps        /\
                                             can_box a ps)
                              (fun m0 r t -> is_Cons t /\ Cons.tl t = [] /\
                                             is_TScope (Cons.hd t)       /\
                                             TScope.ps (Cons.hd t) = ps  /\
                                             ens_f (Mode Par ps) (v_of_box r) (TScope.t (Cons.hd t)))

(*****)

type DelSec (m:mode) (ps:prins) = ps = Mode.ps m
(* TODO: FIXME: the output should be added to trace ONLY IF current mode is Par *)
val as_sec: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys a (fun m0     -> req_f (Mode Sec ps) /\ DelSec m0 ps)
                     (fun m0 r t -> is_Cons t /\ last_elt t = TMsg #a r /\
                                    ens_f (Mode Sec ps) r (all_but_last t))
                                    
(*****)

type CanUnboxPC (mode_ps:eprins) (ps:prins) = b2t (subset mode_ps ps)

type CanUnboxP (m:mode) (ps:prins) = Mode.m m = Par /\ CanUnboxPC (Mode.ps m) ps

val unbox_p: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0     -> CanUnboxP m0 ps)
                      (fun m0 r t -> r = v_of_box x /\ t = [])

(*****)

(* Ideally we can do with not (intersect (Mode.ps m) ps = empty
 * but that requires examples to have to help prove this.
 * Metatheory is more precise, in that it needs intersection as non-empty *)

type CanUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ subset ps (Mode.ps m)

val unbox_s: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0     -> CanUnboxS m0 ps)
                      (fun m0 r t -> r = v_of_box x /\ t = [])

(*****)

type CanBox (a:Type) (mode_ps:prins) (ps:prins) =
  can_box a ps /\ subset ps mode_ps

val box: #a:Type -> ps:prins -> x:a
         -> Wys (Box a ps) (fun m0     -> CanBox a (Mode.ps m0) ps)
                           (fun m0 r t -> v_of_box r = x /\ t = [])

(*****)

type CanMkWireP (a:Type) (m:mode) (ps':prins) (eps:eprins) =
  Mode.m m = Par /\ can_wire a /\ CanUnboxPC eps ps' /\ subset eps (Mode.ps m)

val mkwire_p: #a:Type -> #ps':prins -> eps:eprins -> x:Box a ps'
              -> Wys (Wire a eps) (fun m0     -> CanMkWireP a m0 ps' eps)
                                  (fun m0 r t -> r = w_const_on #a eps (v_of_box #a #ps' x) /\ t = [])

(*****)

type CanMkWireS (a:Type) (m:mode) (eps:eprins) =
  Mode.m m = Sec /\ can_wire a /\ subset eps (Mode.ps m)

val mkwire_s: #a:Type -> eps:eprins -> x:a
              -> Wys (Wire a eps) (fun m0     -> CanMkWireS a m0 eps)
                                  (fun m0 r t -> r = w_const_on #a eps x /\ t = [])

(*****)

type CanProjWireP (#a:Type) (#eps:eprins) (m:mode) (x:Wire a eps) (p:prin) =
  Mode.m m = Par /\ Mode.ps m = singleton p /\ w_contains p x

val projwire_p: #a:Type -> #eps:eprins -> p:prin -> x:Wire a eps{w_contains p x}
                -> Wys a (fun m0     -> CanProjWireP m0 x p)
                         (fun m0 r t -> r = w_select p x /\ t = [])

(*****)

type CanProjWireS (#a:Type) (#eps:eprins) (m:mode) (x:Wire a eps) (p:prin) =
  Mode.m m = Sec /\ mem p (Mode.ps m) /\ w_contains p x

val projwire_s: #a:Type -> #eps:eprins -> p:prin -> x:Wire a eps{w_contains p x}
                -> Wys a (fun m0     -> CanProjWireS m0 x p)
                         (fun m0 r t -> r = w_select p x /\ t = [])

(*****)

type CanConcatWire (#a:Type) (#eps1:eprins) (#eps2:eprins) (x:Wire a eps1) (y:Wire a eps2) =
  forall p. w_contains p x ==> not (w_contains p y)

val concat_wire: #a:Type -> #eps_x:eprins -> #eps_y:eprins
                 -> x:Wire a eps_x -> y:Wire a eps_y{CanConcatWire x y}
                 -> Wys (Wire a (union eps_x eps_y)) (fun m0     -> CanConcatWire x y)
                                                     (fun m0 r t -> r = w_concat x y /\ t = [])

(*****)

val main: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
          -> ps:prins
          -> =f:(unit -> Wys a req_f ens_f)
          -> All a (fun h0      -> req_f (Mode Par ps))
                   (fun h0 r h1 -> is_V r /\ ens_f (Mode Par ps) (V.v r) (sel h1 traceref))

(*****)

(* these are also ffi calls, and are handled in the extraction *)

val w_read_int: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                     (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r t -> b2t (t = []))
val w_read_int_tuple: unit -> Wys (int * int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> b2t (t = []))

val w_read_int_list: unit -> Wys (list int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> b2t (t = []))

val alice  : prin
val bob    : prin
val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

(*****)

val wprint: #a:Type -> x:a -> ML unit
