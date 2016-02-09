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
let rec rest_trace t1 t2 = match t2 with
  | []     -> Some t1
  | hd::tl ->
    match t1 with
      | []       -> None
      | hd'::tl' ->
        if hd = hd' then rest_trace tl' tl else None

val last_elt: t:trace{is_Cons t} -> Tot telt
let rec last_elt (Cons hd tl) = match tl with
  | [] -> hd
  | _  -> last_elt tl

val all_but_last: t:trace{is_Cons t} -> Tot trace
let rec all_but_last (Cons hd tl) = match tl with
  | []       -> []
  | hd'::tl' -> hd::(all_but_last tl)

val equal_trace_rest_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (b2t (t1 = t2)))
                                     (ensures (rest_trace t1 t2 = Some []))
                               [SMTPat (rest_trace t1 t2)]
let rec equal_trace_rest_lemma t1 t2 = match t2 with
  | []     -> ()
  | hd::tl ->
    match t1 with
      | hd'::tl' -> equal_trace_rest_lemma tl tl'

val rest_equal_trace_lemma: t1:trace -> t2:trace
                            -> Lemma (requires (rest_trace t1 t2 = Some []))
                                     (ensures (b2t (t1 = t2)))
                               [SMTPat (rest_trace t1 t2)]
let rec rest_equal_trace_lemma t1 t2 = match t2 with
  | []     -> ()
  | hd::tl ->
    match t1 with
      | hd'::tl' -> if hd = hd' then rest_equal_trace_lemma tl' tl else ()
      | []       -> ()

val append_rest_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (append t1 t2 = t3))
                                (ensures (is_Some (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) = t2))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]
let rec append_rest_lemma t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t3 with
      | _::tl' -> append_rest_lemma tl t2 tl'

val rest_append_lemma: t1:trace -> t2:trace -> t3:trace
                       -> Lemma (requires (is_Some (rest_trace t3 t1) /\ Some.v (rest_trace t3 t1) = t2))
                                (ensures (append t1 t2 = t3))
                          [SMTPat (rest_trace t3 t1); SMTPat (append t1 t2)]
let rec rest_append_lemma t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t3 with
      | _::tl' -> rest_append_lemma tl t2 tl'

val trace_assoc: t1:trace -> t2:trace -> t3:trace
                 -> Lemma (requires (is_Some (rest_trace t2 t1) /\ is_Some (rest_trace t3 t2)))
                          (ensures (is_Some (rest_trace t2 t1) /\ is_Some (rest_trace t3 t2) /\ is_Some (rest_trace t3 t1) /\
                                    Some.v (rest_trace t3 t1) = append (Some.v (rest_trace t2 t1))
                                                                       (Some.v (rest_trace t3 t2))))
                    [SMTPat (rest_trace t2 t1); SMTPat (rest_trace t3 t2)]
let rec trace_assoc t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t2 with
      | _::tl' ->
        match t3 with
          | _::tl'' -> trace_assoc tl tl' tl''

val last_elt_singleton_lemma: t:trace{is_Cons t}
                              -> Lemma (requires (all_but_last t = []))
                                       (ensures (t = [last_elt t]))
                                 [SMTPat (last_elt t); SMTPat (all_but_last t)]
let last_elt_singleton_lemma t = ()

val snoc_last_elt_lemma: elt:telt -> t:trace
                         -> Lemma (requires (True))
                                  (ensures (last_elt (t @ [elt]) = elt))
                            [SMTPat (last_elt (t @ [elt]))]
let rec snoc_last_elt_lemma elt t = match t with
  | []     -> ()
  | hd::tl -> snoc_last_elt_lemma elt tl

val snoc_all_but_last_lemma: elt:telt -> t:trace
                             -> Lemma (requires (True))
                                      (ensures (all_but_last (t @ [elt]) = t))
                            [SMTPat (all_but_last (t @ [elt]))]
let rec snoc_all_but_last_lemma elt t = match t with
  | []     -> ()
  | hd::tl -> snoc_all_but_last_lemma elt tl

val all_but_last_append_lemma: t:trace{is_Cons t} ->
                               Lemma (requires (True))
                                     (ensures (append (all_but_last t) ([last_elt t]) = t))
                               [SMTPat (append (all_but_last t) ([last_elt t]))]
let rec all_but_last_append_lemma (Cons hd tl) = match tl with
  | [] -> ()
  | _  -> all_but_last_append_lemma tl

open FStar.Heap
assume val moderef : ref mode
assume val traceref : ref trace

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
abstract type Box: Type -> prins -> Type =
  |Mk_box: #a:Type -> x:a -> ps:prins -> Box a ps

abstract val v_of_box : #a:Type -> #ps:prins -> Box a ps -> GTot a
let v_of_box (#a:Type) #ps x = Mk_box.x x

assume type can_box: a:Type -> ps:prins -> Type
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
type Wire (a:Type) (eps:eprins) = m:OrdMap.ordmap prin a p_cmp{forall p. mem p eps = OrdMap.contains p m}


abstract val w_contains: #a:Type -> #eps:eprins -> prin -> =w:Wire a eps -> GTot bool
let w_contains (#a:Type) #eps p x = OrdMap.contains p x

abstract val w_empty   : #a:Type -> GTot (w:Wire a (empty ()){forall p. not (w_contains #a #(empty()) p w)})
let w_empty (#a:Type) = OrdMap.empty

abstract val w_select  : #a:Type -> #eps:eprins -> p:prin -> w:Wire a eps{w_contains p w} -> GTot a
let w_select (#a:Type) #eps p x = Some.v (OrdMap.select p x)

abstract val w_const_on: #a:Type -> eps:eprins -> x:a
                -> GTot (w:Wire a eps{forall p. (mem p eps <==> w_contains p w) /\
                                                (w_contains p w ==> w_select p w = x)})
let w_const_on (#a:Type) eps x = OrdMap.const_on eps x


val w_concat_helper:
  #a:Type -> #eps1:eprins -> #eps2:eprins
  -> w1:Wire a eps1 -> w2:Wire a eps2{forall p. w_contains #a #eps1 p w1 ==> not (w_contains #a #eps2 p w2)}
  -> ps:eprins{forall p. mem p ps ==> OrdMap.contains p w1}
  -> Tot (w:Wire a (union ps eps2)
          {forall p.(mem p ps ==> (w_contains #a #(union ps eps2) p w /\
                                   w_select #a #(union ps eps2) p w = w_select #a #eps1 p w1)) /\
                    (w_contains #a #eps2 p w2 ==> (w_contains #a #(union ps eps2) p w /\
                                                   w_select #a #(union ps eps2) p w = w_select #a #eps2 p w2)) /\
                    (w_contains #a #(union ps eps2) p w  ==> (mem p ps \/ w_contains #a #eps2 p w2))})
     (decreases (OrdSet.size ps))
let rec w_concat_helper (#a:Type) #eps1 #eps2 w1 w2 eps =
  if eps = empty () then w2
  else
    let Some p = OrdSet.choose eps in
    let w = w_concat_helper #a #eps1 #eps2 w1 w2 (OrdSet.remove p eps) in
    OrdMap.update p (Some.v (OrdMap.select p w1)) w

(* TODO: FIXME: Make this ghost, add a concat to the OrdMap lib and use that for computation *)
abstract val w_concat  :
  #a:Type -> #eps1:eprins -> #eps2:eprins
  -> w1:Wire a eps1 -> w2:Wire a eps2{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> Tot (w:Wire a (union eps1 eps2)
          {forall p. (w_contains p w1 ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                     (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                     (w_contains p w  ==> (w_contains p w1 \/ w_contains p w2))})
let w_concat (#a:Type) #eps1 #eps2 w1 w2 = w_concat_helper #a #eps1 #eps2 w1 w2 (OrdMap.dom w1)

abstract val w_dom: #a:Type -> #ps:prins -> w:Wire a ps -> GTot (ps:eprins{forall p. mem p ps <==> w_contains p w})
let w_dom (#a:Type) #eps w = OrdMap.dom w

val w_contains_lemma: a:Type -> eps:prins -> w:Wire a eps -> p:prin
                      -> Lemma (requires (True)) (ensures (w_contains #a #eps p w =
		                                       mem p eps))
		        [SMTPat (w_contains #a #eps p w)]
let w_contains_lemma (a:Type) eps w p = ()


assume type can_wire: Type -> Type
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

(**********)
type Sh: Type -> Type

type can_sh: Type -> Type

assume Cansh_nat : can_sh nat
assume Cansh_int : can_sh int

assume val v_of_sh: #a:Type -> sh:Sh a -> GTot a
assume val ps_of_sh: #a:Type -> sh:Sh a -> GTot prins
(**********)


type DelPar (m:mode) (ps:prins) = Mode.m m = Par /\ subset ps (Mode.ps m)
type DelSec (m:mode) (ps:prins) = ps = Mode.ps m
type CanUnboxPC (mode_ps:eprins) (ps:prins) = b2t (subset mode_ps ps)
type CanUnboxP (m:mode) (ps:prins) = Mode.m m = Par /\ CanUnboxPC (Mode.ps m) ps
type CanUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ subset ps (Mode.ps m)
type CanBox (a:Type) (mode_ps:prins) (ps:prins) =
  can_box a ps /\ subset ps mode_ps
type CanMkWireP (a:Type) (m:mode) (ps':prins) (eps:eprins) =
  Mode.m m = Par /\ can_wire a /\ CanUnboxPC eps ps' /\ subset eps (Mode.ps m)
type CanMkWireS (a:Type) (m:mode) (eps:eprins) =
  Mode.m m = Sec /\ can_wire a /\ subset eps (Mode.ps m)
type CanProjWireP (#a:Type) (#eps:eprins) (m:mode) (x:Wire a eps) (p:prin) =
  Mode.m m = Par /\ Mode.ps m = singleton p /\ w_contains #a #eps p x
type CanProjWireS (#a:Type) (#eps:eprins) (m:mode) (x:Wire a eps) (p:prin) =
  Mode.m m = Sec /\ mem p (Mode.ps m) /\ w_contains #a #eps p x
type CanConcatWire (#a:Type) (#eps_x:eprins) (#eps_y:eprins) (x:Wire a eps_x) (y:Wire a eps_y) =
  forall p. w_contains #a #eps_x p x ==> not (w_contains #a #eps_y p y)


abstract val as_par: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys (Box a ps) (fun m0     -> req_f (Mode Par ps) /\
                                             DelPar m0 ps        /\
                                             can_box a ps)
                              (fun m0 r t -> is_Cons t /\ Cons.tl t = [] /\
                                             is_TScope (Cons.hd t)       /\
                                             TScope.ps (Cons.hd t) = ps  /\
                                             ens_f (Mode Par ps) (v_of_box r) (TScope.t (Cons.hd t)))
let as_par ps f =
  let m0 = ST.read moderef in
  let t0 = ST.read traceref in
  let _ = assert (DelPar m0 ps) in
  ST.write moderef (Mode Par ps);
  let x = f () in
  let t1 = ST.read traceref in
  let t_diff = rest_trace t1 t0 in
  ST.write moderef m0;
  ST.write traceref (append t0 [ TScope ps (Some.v t_diff) ]);
  Mk_box x ps

(*****)

(* TODO: FIXME: the output should be added to trace ONLY IF current mode is Par *)
val as_sec: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
            -> ps:prins
            -> =f:(unit -> Wys a req_f ens_f)
            -> Wys a (fun m0     -> req_f (Mode Sec ps) /\ DelSec m0 ps)
                     (fun m0 r t -> is_Cons t /\ last_elt t = TMsg #a r /\
                                    ens_f (Mode Sec ps) r (all_but_last t))
let as_sec ps f =
  let m0 = ST.read moderef in
  let t0 = ST.read traceref in
  let _ = assert (DelSec m0 ps) in
  ST.write moderef (Mode Sec ps);
  let x = f () in
  let t1 = ST.read traceref in
  let t_diff = rest_trace t1 t0 in
  let t' = append (Some.v t_diff) [TMsg x] in
  ST.write moderef m0;
  ST.write traceref (append t0 t');
  x

(*****)
val unbox_p: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0     -> CanUnboxP m0 ps)
                      (fun m0 r t -> r = v_of_box x /\ t = [])

let unbox_p (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxP m0 ps);
  Mk_box.x x

(*****)

(* Ideally we can do with not (intersect (Mode.ps m) ps = empty
 * but that requires examples to have to help prove this.
 * Metatheory is more precise, in that it needs intersection as non-empty *)

val unbox_s: #a:Type -> #ps:prins -> x:Box a ps
             -> Wys a (fun m0     -> CanUnboxS m0 ps)
                      (fun m0 r t -> r = v_of_box x /\ t = [])
let unbox_s (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxS m0 ps);
  Mk_box.x x

(*****)

val box: #a:Type -> ps:prins -> x:a
         -> Wys (Box a ps) (fun m0     -> CanBox a (Mode.ps m0) ps)
                           (fun m0 r t -> v_of_box r = x /\ t = [])
let box (#a:Type) ps x =
  let m0 = ST.read moderef in
  assert (CanBox a (Mode.ps m0) ps);
  Mk_box x ps

(*****)
val mkwire_p: #a:Type -> #ps':prins -> eps:eprins -> x:Box a ps'
              -> Wys (Wire a eps) (fun m0     -> CanMkWireP a m0 ps' eps)
                                  (fun m0 r t -> r = w_const_on #a eps (v_of_box #a #ps' x) /\ t = [])
let mkwire_p (#a:Type) #ps' eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireP a m0 ps' eps);
  OrdMap.const_on #prin #a #p_cmp eps (Mk_box.x x)

(*****)
val mkwire_s: #a:Type -> eps:eprins -> x:a
              -> Wys (Wire a eps) (fun m0     -> CanMkWireS a m0 eps)
                                  (fun m0 r t -> r = w_const_on #a eps x /\ t = [])
let mkwire_s (#a:Type) eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireS a m0 eps);
  OrdMap.const_on eps x

(*****)
val projwire_p: #a:Type -> #eps:eprins -> p:prin -> x:Wire a eps{w_contains p x}
                -> Wys a (fun m0     -> CanProjWireP m0 x p)
                         (fun m0 r t -> r = w_select p x /\ t = [])
let projwire_p (#a:Type) #eps p x =
  let m0 = ST.read moderef in
  assert (CanProjWireP #a #eps m0 x p);
  Some.v (OrdMap.select p x)

(*****)
val projwire_s: #a:Type -> #eps:eprins -> p:prin -> x:Wire a eps{w_contains p x}
                -> Wys a (fun m0     -> CanProjWireS m0 x p)
                         (fun m0 r t -> r = w_select p x /\ t = [])
let projwire_s (#a:Type) #eps p x =
  let m0 = ST.read moderef in
  assert (CanProjWireS #a #eps m0 x p);
  Some.v (OrdMap.select p x)

(*****)
val concat_wire: #a:Type -> #eps_x:eprins -> #eps_y:eprins
                 -> x:Wire a eps_x -> y:Wire a eps_y{CanConcatWire x y}
                 -> Wys (Wire a (union eps_x eps_y)) (fun m0     -> CanConcatWire x y)
                                                     (fun m0 r t -> r = w_concat x y /\ t = [])
let concat_wire (#a:Type) #eps1 #eps2 x y = w_concat #a #eps1 #eps2 x y

(*****)

assume val mk_sh: #a:Type -> x:a
           -> Wys (Sh a) (fun m0     -> m0.m = Sec /\ can_sh a)
	                (fun m0 r t -> v_of_sh r = x /\ ps_of_sh r = m0.ps /\ t = [])

assume val comb_sh: #a:Type -> x:Sh a
             -> Wys a (fun m0     -> m0.m = Sec /\ ps_of_sh x = m0.ps)
	             (fun m0 r t -> v_of_sh x = r /\ t = [])

(*****)

val main: #a:Type -> #req_f:(mode -> Type) -> #ens_f:(mode -> a -> trace -> Type)
          -> ps:prins
          -> =f:(unit -> Wys a req_f ens_f)
          -> All a (fun h0      -> req_f (Mode Par ps))
                   (fun h0 r h1 -> is_V r /\ ens_f (Mode Par ps) (V.v r) (sel h1 traceref))

let main ps f =
  ST.write moderef (Mode Par ps);
  ST.write traceref [];
  f ()

(*****)

(* these are also ffi calls, and are handled in the extraction *)

assume val w_read_int: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                     (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r t -> b2t (t = []))
assume val w_read_int_tuple: unit -> Wys (int * int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> b2t (t = []))

assume val w_read_int_list: unit -> Wys (list int) (fun m0 -> Mode.m m0 = Par /\
                                                 (exists p. Mode.ps m0 = singleton p))
                                         (fun m0 r t -> b2t (t = []))

assume val alice  : prin
assume val bob    : prin
assume val charlie: prin

assume PrinsAxiom: alice =!= bob /\ bob =!= charlie /\ charlie =!= alice

(*****)

assume val wprint: #a:Type -> x:a -> ML unit
