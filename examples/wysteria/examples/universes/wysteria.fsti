module Wysteria

open FStar.List

open Prins
open FFI

type as_mode =
  | Par
  | Sec

assume HasEq_prins: hasEq prins

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

noeq type telt =
  | TMsg  : #a:Type0 -> x:a -> telt
  | TScope: ps:prins -> t:list telt -> telt

type trace = list telt

let wys_pre = mode -> GTot Type0
let wys_post (a:Type) = a -> trace -> GTot Type0

//why is this Tot and not GTot, GTot gives some error
let wys_wp (a:Type) = wys_post a -> Tot wys_pre

inline let wys_ite_wp (a:Type)
                      (wp:wys_wp a)
                      (post:wys_post a) (m:mode) =
    forall (k:wys_post a).
       (forall (x:a) (t:trace).{:pattern (guard_free (k x t))} k x t <==> post x t)
       ==> wp k m

inline let wys_return (a:Type) (x:a) (p:wys_post a) (m:mode) = p x []

inline let wys_bind_wp (r1:range) (a:Type) (b:Type)
                       (wp1:wys_wp a)
                       (wp2:(a -> GTot (wys_wp b)))
                       (p:wys_post b) (m:mode) : GTot Type0 =
   labeled r1 "push" unit
   /\ wp1 (fun ra t1 ->
       labeled r1 "pop" unit
	 /\ (wp2 ra) (fun rb t2 -> p rb (append t1 t2)) m) m

inline let wys_if_then_else  (a:Type) (p:Type)
                             (wp_then:wys_wp a) (wp_else:wys_wp a)
                             (post:wys_post a) (m:mode) =
   l_ITE p
       (wp_then post m)
       (wp_else post m)

inline let wys_stronger (a:Type) (wp1:wys_wp a)
                        (wp2:wys_wp a) =
    (forall (p:wys_post a) (m:mode). wp1 p m ==> wp2 p m)

inline let wys_close_wp (a:Type) (b:Type)
                        (wp:(b -> GTot (wys_wp a)))
                        (p:wys_post a) (m:mode) =
    (forall (b:b). wp b p m)
inline let wys_assert_p (a:Type) (p:Type)
                        (wp:wys_wp a) (q:wys_post a) (m:mode) =
    p /\ wp q m
inline let wys_assume_p (a:Type) (p:Type)
                        (wp:wys_wp a) (q:wys_post a) (m:mode) =
    p ==> wp q m
inline let wys_null_wp (a:Type)
                       (p:wys_post a) (m:mode) =
    (forall (a:a) (t:trace). p a t)
inline let wys_trivial (a:Type) (wp:wys_wp a) =
    (forall (m:mode). wp (fun x t -> True) m)

new_effect {
  WYS : a:Type -> wp:wys_wp a -> Effect
  with
    return_wp    = wys_return
  ; bind_wp      = wys_bind_wp
  ; if_then_else = wys_if_then_else
  ; ite_wp       = wys_ite_wp
  ; stronger     = wys_stronger
  ; close_wp     = wys_close_wp
  ; assert_p     = wys_assert_p
  ; assume_p     = wys_assume_p
  ; null_wp      = wys_null_wp
  ; trivial      = wys_trivial
}

effect Wys (a:Type) (req:mode -> Type0) (ens:mode -> a -> trace -> Type0)
  = WYS a (fun (q:a -> trace -> Type0) (m:mode) ->
	     req m /\ (forall x t. ens m x t ==> q x t))

inline let lift_pure_wys (a:Type) (wp:pure_wp a) (p:wys_post a) (m:mode) = wp (fun a -> p a [])
sub_effect PURE ~> WYS = lift_pure_wys

val rest_trace: t1:trace -> t2:trace -> Tot (option trace)

val last_elt: t:trace{Cons? t} -> Tot telt

val all_but_last: t:trace{Cons? t} -> Tot trace

val equal_trace_rest_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (t1 == t2))
                                     (ensures (rest_trace t1 t2 == Some []))
                               [SMTPat (rest_trace t1 t2)]
                               
val rest_equal_trace_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (rest_trace t1 t2 == Some []))
                                     (ensures (t1 == t2))
                               [SMTPat (rest_trace t1 t2)]
                               
val append_rest_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (append t1 t2 == t3))
                                (ensures (Some? (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) == t2))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]

val rest_append_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (Some? (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) == t2))
                                (ensures (append t1 t2 == t3))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]

val trace_assoc: t1:trace -> t2:trace -> t3:trace
                 -> Lemma (requires (Some? (rest_trace t2 t1) /\ Some? (rest_trace t3 t2)))
                          (ensures (Some? (rest_trace t2 t1) /\ Some? (rest_trace t3 t2) /\ Some? (rest_trace t3 t1) /\
                                    Some.v (rest_trace t3 t1) == append (Some.v (rest_trace t2 t1))
                                                                       (Some.v (rest_trace t3 t2))))
                    [SMTPat (rest_trace t2 t1); SMTPat (rest_trace t3 t2)]

val last_elt_singleton_lemma: t:trace{Cons? t}
                              -> Lemma (requires (all_but_last t == []))
                                       (ensures (t == [last_elt t]))
                                 [SMTPat (last_elt t); SMTPat (all_but_last t)]

val snoc_last_elt_lemma: elt:telt -> t:trace
                         -> Lemma (requires (True))
                                  (ensures (last_elt (t @ [elt]) == elt))
                            [SMTPat (last_elt (t @ [elt]))]

val snoc_all_but_last_lemma: elt:telt -> t:trace
                             -> Lemma (requires (True))
                                      (ensures (all_but_last (t @ [elt]) == t))
                            [SMTPat (all_but_last (t @ [elt]))]

val all_but_last_append_lemma: t:trace{Cons? t} ->
                               Lemma (requires (True))
                                     (ensures (append (all_but_last t) ([last_elt t]) == t))
                               [SMTPat (append (all_but_last t) ([last_elt t]))]

(**********)

(* open FStar.Heap *)

(* //let moderef : ref (option mode) = alloc None (\* private *\) *)
(* assume val moderef : ref mode *)

(* let traceref: ref trace = alloc [] *)

(* //kind requires         = mode -> Type *)
(* //kind ensures (a:Type) = mode -> a -> trace -> Type *)

(* type wys_encoding (a:Type) (req:mode -> Type) (ens:mode -> a -> trace -> Type) (p:a -> heap -> Type) (h0:heap) = *)
(*   req (sel h0 moderef) /\ *)
(*   (forall x h1. (sel h1 moderef = sel h0 moderef /\ Some? (rest_trace (sel h1 traceref) (sel h0 traceref)) /\ *)
(*                  ens (sel h0 moderef) x (Some.v (rest_trace (sel h1 traceref) (sel h0 traceref)))) ==> p x h1) *)

(* effect Wys (a:Type) (req:mode -> Type) (ens:mode -> a -> trace -> Type) = *)
(*   STATE a (fun (p:a -> heap -> Type) (h0:heap) -> wys_encoding a req ens p h0) *)

(* open FStar.Relational *)
(* open FStar.Comp *)

(* //kind requires2         = double mode -> Type *)
(* //kind ensures2 (a:Type) = double mode -> a -> double trace -> Type *)

(* type wys2_encoding (a:Type) (req:double mode -> Type) (ens:double mode -> a -> double trace -> Type) (p:a -> heap2 -> Type) (h0:heap2) = *)
(*   req (R (sel (R.l h0) moderef) (sel (R.r h0) moderef)) /\ *)
(*   (forall x h1. (sel (R.l h1) moderef = sel (R.l h0) moderef /\ *)
(*                  sel (R.r h1) moderef = sel (R.r h0) moderef /\ *)
(*                  Some? (rest_trace (sel (R.l h1) traceref) (sel (R.l h0) traceref)) /\ *)
(*                  Some? (rest_trace (sel (R.r h1) traceref) (sel (R.r h0) traceref)) /\ *)
(*                  ens (R (sel (R.l h0) moderef) (sel (R.r h0) moderef)) x *)
(*                      (R (Some.v (rest_trace (sel (R.l h1) traceref) (sel (R.l h0) traceref))) *)
(*                         (Some.v (rest_trace (sel (R.r h1) traceref) (sel (R.r h0) traceref))))) ==> p x h1) *)

(* effect Wys2 (a:Type) (req:double mode -> Type) (ens:double mode -> a -> double trace -> Type) = *)
(*   STATE2 a (fun (p:a -> heap2 -> Type) (h0:heap2) -> wys2_encoding a req ens p h0) *)
(*            (fun (p:a -> heap2 -> Type) (h0:heap2) -> wys2_encoding a req ens p h0) *)

(* assume val compose_wys2: #a:Type -> #b:Type *)
(*                          -> #req0:(mode -> Type) ->#req1:(mode -> Type) *)
(*                          -> #ens0:(mode -> a -> trace -> Type) -> #ens1:(mode -> b -> trace -> Type) *)
(*                          -> $f0:(unit -> Wys a req0 ens0) *)
(*                          -> $f1:(unit -> Wys b req1 ens1) *)
(*                          -> Wys2 (rel a b) (fun m0     -> req0 (R.l m0) /\ req1 (R.r m0)) *)
(*                                           (fun m0 r t -> ens0 (R.l m0) (R.l r) (R.l t) /\ *)
(*                                                       ens1 (R.r m0) (R.r r) (R.r t)) *)

(**********)
type box: Type -> prins -> Type

val v_of_box : #a:Type -> #ps:prins -> box a ps -> GTot a

type can_box: a:Type -> ps:prins -> Type

assume Canbox_nat   : (forall ps. can_box nat ps)
assume Canbox_int   : (forall ps. can_box int ps)
assume Canbox_bool  : (forall ps. can_box bool ps)
assume Canbox_prin  : (forall ps. can_box prin ps)
assume Canbox_prins : (forall ps. can_box prins ps)
assume Canbox_eprins: (forall ps. can_box eprins ps)
assume Canbox_box   : (forall (a:Type) (ps':prins) (ps:prins).
                       subset ps' ps ==> can_box (box a ps') ps)
assume Canbox_option: (forall (a:Type) ps. can_box a ps ==>
                                           can_box (option a) ps)
assume Canbox_prod  : (forall (a:Type) (b:Type) ps.
                         (can_box a ps /\ can_box b ps) ==> can_box (a * b) ps)
assume Canbox_list  : (forall (a:Type) ps. can_box a ps ==> can_box (list a) ps)

(* assume Canbox_rel   : (forall (a:Type) (b:Type) ps. *)
(*                          (can_box a ps  /\ can_box b ps) ==> can_box (rel a b) ps) *)

(**********)

type wire: Type -> eprins -> Type

val w_contains: #a:Type -> #eps:eprins -> prin -> wire a eps -> GTot bool
val w_empty   : #a:Type -> GTot (w:wire a (empty ()){forall p. not (w_contains p w)})
val w_select  : #a:Type -> #eps:eprins -> p:prin -> w:wire a eps{w_contains p w} -> GTot a
val w_const_on: #a:Type -> eps:eprins -> x:a
                -> GTot (w:wire a eps{forall p. ((b2t (mem p eps)) <==> (b2t (w_contains p w))) /\
                                                ((b2t (w_contains p w)) ==> (w_select p w == x))})

(* TODO: FIXME: Make this ghost, add a concat to the OrdMap lib and use that for computation *)
val w_concat  :
  #a:Type -> #eps1:eprins -> #eps2:eprins
  -> w1:wire a eps1 -> w2:wire a eps2{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> Tot (w:wire a (union eps1 eps2)
          {forall p. (w_contains p w1 ==> (w_contains p w /\ w_select p w == w_select p w1)) /\
                     (w_contains p w2 ==> (w_contains p w /\ w_select p w == w_select p w2)) /\
                     (w_contains p w  ==> (w_contains p w1 \/ w_contains p w2))})

val w_dom: #a:Type -> #ps:prins -> w:wire a ps -> GTot (ps:eprins{forall p. (b2t (mem p ps)) <==> (b2t (w_contains p w))})

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
                       subset eps ps ==> can_box (wire a eps) ps)

assume Can_wire_implies_can_box: forall (a:Type) ps. can_wire a ==> can_box a ps

val w_contains_lemma: a:Type -> eps:prins -> w:wire a eps -> p:prin
                      -> Lemma (requires (True)) (ensures (w_contains #a #eps p w =
		                                       mem p eps))
		        [SMTPat (w_contains #a #eps p w)]

(**********)

type sh: Type -> Type

type can_sh: Type -> Type

assume Cansh_nat : can_sh nat
assume Cansh_int : can_sh int

val v_of_sh: #a:Type -> sh:sh a -> GTot a
val ps_of_sh: #a:Type -> sh:sh a -> GTot prins

(**********)

type delPar (m:mode) (ps:prins) = Mode.m m = Par /\ subset ps (Mode.ps m)

val as_par: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> $f:(unit -> Wys a req_f ens_f)
            -> Wys (box a ps) (fun m0     -> req_f (Mode Par ps) /\
                                             delPar m0 ps        /\
                                             can_box a ps)
                              (fun m0 r t -> Cons? t /\ Cons.tl t == [] /\
                                             TScope? (Cons.hd t)       /\
                                             TScope.ps (Cons.hd t) = ps  /\
                                             ens_f (Mode Par ps) (v_of_box r) (TScope.t (Cons.hd t)))

(*****)

type decSec (m:mode) (ps:prins) = ps = Mode.ps m
(* TODO: FIXME: the output should be added to trace ONLY IF current mode is Par *)
val as_sec: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> $f:(unit -> Wys a req_f ens_f)
            -> Wys a (fun m0     -> req_f (Mode Sec ps) /\ decSec m0 ps)
                     (fun m0 r t -> Cons? t /\ last_elt t == TMsg #a r /\
                                    ens_f (Mode Sec ps) r (all_but_last t))
                                    
(*****)

type canUnboxPC (mode_ps:eprins) (ps:prins) = b2t (subset mode_ps ps)

type canUnboxP (m:mode) (ps:prins) = Mode.m m = Par /\ canUnboxPC (Mode.ps m) ps

val unbox_p: #a:Type -> #ps:prins -> x:box a ps
             -> Wys a (fun m0     -> canUnboxP m0 ps)
                      (fun m0 r t -> r == v_of_box x /\ t == [])

(*****)

(* Ideally we can do with not (intersect (Mode.ps m) ps = empty
 * but that requires examples to have to help prove this.
 * Metatheory is more precise, in that it needs intersection as non-empty *)

type canUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ subset ps (Mode.ps m)

val unbox_s: #a:Type -> #ps:prins -> x:box a ps
             -> Wys a (fun m0     -> canUnboxS m0 ps)
                      (fun m0 r t -> r == v_of_box x /\ t == [])

(*****)

type canbox (a:Type) (mode_ps:prins) (ps:prins) =
  can_box a ps /\ subset ps mode_ps

val box_v: #a:Type -> ps:prins -> x:a
         -> Wys (box a ps) (fun m0     -> canbox a (Mode.ps m0) ps)
                           (fun m0 r t -> v_of_box r == x /\ t == [])

(*****)

type canMkwireP (a:Type) (m:mode) (ps':prins) (eps:eprins) =
  Mode.m m = Par /\ can_wire a /\ canUnboxPC eps ps' /\ subset eps (Mode.ps m)

val mkwire_p: #a:Type -> #ps':prins -> eps:eprins -> x:box a ps'
              -> Wys (wire a eps) (fun m0     -> canMkwireP a m0 ps' eps)
                                  (fun m0 r t -> r == w_const_on #a eps (v_of_box #a #ps' x) /\ t == [])

(*****)

type canMkwireS (a:Type) (m:mode) (eps:eprins) =
  Mode.m m = Sec /\ can_wire a /\ subset eps (Mode.ps m)

val mkwire_s: #a:Type -> eps:eprins -> x:a
              -> Wys (wire a eps) (fun m0     -> canMkwireS a m0 eps)
                                  (fun m0 r t -> r == w_const_on #a eps x /\ t == [])

(*****)

type canProjwireP (#a:Type) (#eps:eprins) (m:mode) (x:wire a eps) (p:prin) =
  Mode.m m = Par /\ Mode.ps m = singleton p /\ w_contains p x

val projwire_p: #a:Type -> #eps:eprins -> p:prin -> x:wire a eps{w_contains p x}
                -> Wys a (fun m0     -> canProjwireP m0 x p)
                         (fun m0 r t -> r == w_select p x /\ t == [])

(*****)

type canProjwireS (#a:Type) (#eps:eprins) (m:mode) (x:wire a eps) (p:prin) =
  (b2t (Mode.m m = Sec)) /\ (b2t (mem p (Mode.ps m))) /\ (b2t (w_contains p x))

val projwire_s: #a:Type -> #eps:eprins -> p:prin -> x:wire a eps{w_contains p x}
                -> Wys a (fun m0     -> canProjwireS m0 x p)
                         (fun m0 r t -> r == w_select p x /\ t == [])

(*****)

type canConcatwire (#a:Type) (#eps1:eprins) (#eps2:eprins) (x:wire a eps1) (y:wire a eps2) =
  forall p. w_contains p x ==> not (w_contains p y)

val concat_wire: #a:Type -> #eps_x:eprins -> #eps_y:eprins
                 -> x:wire a eps_x -> y:wire a eps_y{canConcatwire x y}
                 -> Wys (wire a (union eps_x eps_y)) (fun m0     -> canConcatwire x y)
                                                     (fun m0 r t -> r == w_concat x y /\ t == [])

(*****)

val mk_sh: #a:Type -> x:a
           -> Wys (sh a) (fun m0     -> m0.m = Sec /\ can_sh a)
	                (fun m0 r t -> v_of_sh r == x /\ ps_of_sh r = m0.ps /\ t == [])

val comb_sh: #a:Type -> x:sh a
             -> Wys a (fun m0     -> m0.m = Sec /\ ps_of_sh x = m0.ps)
	             (fun m0 r t -> v_of_sh x == r /\ t == [])

(*****)

(* val main: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type) *)
(*           -> ps:prins *)
(*           -> $f:(unit -> Wys a req_f ens_f) *)
(*           -> All a (fun h0      -> req_f (Mode Par ps)) *)
(*                    (fun h0 r h1 -> V? r /\ ens_f (Mode Par ps) (V.v r) (sel h1 traceref)) *)

(*****)

(* these are also ffi calls, and are handled in the extraction *)

val w_read_int: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                     (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r t -> t == [])
val w_read_int_tuple: unit -> Wys (int * int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> t == [])

val w_read_int_list: unit -> Wys (list int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> t == [])

val alice  : prin
val bob    : prin
val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

(*****)

val wprint: #a:Type -> x:a -> ML unit
