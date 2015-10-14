(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Prins --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst st2.fst ordset.fsi ordmap.fsi ../prins.fsi ffi.fst wysteria.fsi
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

let rec rest_trace t1 t2 = match t2 with
  | []     -> Some t1
  | hd::tl ->
    match t1 with
      | []       -> None
      | hd'::tl' ->
        if hd = hd' then rest_trace tl' tl else None

let rec last_elt (Cons hd tl) = match tl with
  | [] -> hd
  | _  -> last_elt tl

let rec all_but_last (Cons hd tl) = match tl with
  | []       -> []
  | hd'::tl' -> hd::(all_but_last tl)

let rec equal_trace_rest_lemma t1 t2 = match t2 with
  | []     -> ()
  | hd::tl ->
    match t1 with
      | hd'::tl' -> equal_trace_rest_lemma tl tl'

let rec rest_equal_trace_lemma t1 t2 = match t2 with
  | []     -> ()
  | hd::tl ->
    match t1 with
      | hd'::tl' -> if hd = hd' then rest_equal_trace_lemma tl' tl else ()
      | []       -> ()

let rec append_rest_lemma t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t3 with
      | _::tl' -> append_rest_lemma tl t2 tl'

let rec rest_append_lemma t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t3 with
      | _::tl' -> rest_append_lemma tl t2 tl'

let rec trace_assoc t1 t2 t3 = match t1 with
  | []     -> ()
  | hd::tl ->
    match t2 with
      | _::tl' ->
        match t3 with
          | _::tl'' -> trace_assoc tl tl' tl''

let last_elt_singleton_lemma t = ()

let rec snoc_last_elt_lemma elt t = match t with
  | []     -> ()
  | hd::tl -> snoc_last_elt_lemma elt tl

let rec snoc_all_but_last_lemma elt t = match t with
  | []     -> ()
  | hd::tl -> snoc_all_but_last_lemma elt tl

let rec all_but_last_append_lemma (Cons hd tl) = match tl with
  | [] -> ()
  | _  -> all_but_last_append_lemma tl

let moderef = Wysteria.moderef

let traceref = Wysteria.traceref

type Box: Type -> prins -> Type =
  |Mk_box: #a:Type -> x:a -> ps:prins -> Box a ps

let v_of_box (#a:Type) #ps x = Mk_box.x x

type can_box: a:Type -> ps:prins -> Type

type Wire (a:Type) (eps:eprins) = m:OrdMap.ordmap prin a p_cmp{forall p. mem p eps = OrdMap.contains p m}

let w_contains (#a:Type) #eps p x = OrdMap.contains p x
let w_empty (#a:Type) = OrdMap.empty
let w_select (#a:Type) #eps p x = Some.v (OrdMap.select p x)
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

let w_concat (#a:Type) #eps1 #eps2 w1 w2 = w_concat_helper #a #eps1 #eps2 w1 w2 (OrdMap.dom w1)
let w_dom (#a:Type) #eps w = OrdMap.dom w

let w_contains_lemma (a:Type) eps w p = ()

type can_wire: Type -> Type

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

let as_par ps f =
  let m0 = ST.read moderef in
  let t0 = ST.read traceref in
  let _ = assert (DelPar (Some.v m0) ps) in
  ST.write moderef (Some (Mode Par ps));
  let x = f () in
  let t1 = ST.read traceref in
  let t_diff = rest_trace t1 t0 in
  ST.write moderef m0;
  ST.write traceref (append t0 [ TScope ps (Some.v t_diff) ]);
  Mk_box x ps

let as_sec ps f =
  let m0 = ST.read moderef in
  let t0 = ST.read traceref in
  let _ = assert (DelSec (Some.v m0) ps) in
  ST.write moderef (Some (Mode Sec ps));
  let x = f () in
  let t1 = ST.read traceref in
  let t_diff = rest_trace t1 t0 in
  let t' = append (Some.v t_diff) [TMsg x] in
  ST.write moderef m0;
  ST.write traceref (append t0 t');
  x

let unbox_p (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxP (Some.v m0) ps);
  Mk_box.x x

let unbox_s (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxS (Some.v m0) ps);
  Mk_box.x x

let box (#a:Type) ps x =
  let m0 = ST.read moderef in
  assert (CanBox a (Mode.ps (Some.v m0)) ps);
  Mk_box x ps

let mkwire_p (#a:Type) #ps' eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireP a (Some.v m0) ps' eps);
  OrdMap.const_on #prin #a #p_cmp eps (Mk_box.x x)

let mkwire_s (#a:Type) eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireS a (Some.v m0) eps);
  OrdMap.const_on eps x

let projwire_p (#a:Type) #eps p x =
  let m0 = ST.read moderef in
  assert (CanProjWireP #a #eps (Some.v m0) x p);
  Some.v (OrdMap.select p x)

let projwire_s (#a:Type) #eps p x =
  let m0 = ST.read moderef in
  assert (CanProjWireS #a #eps (Some.v m0) x p);
  Some.v (OrdMap.select p x)

let concat_wire (#a:Type) #eps1 #eps2 x y = w_concat #a #eps1 #eps2 x y

let main ps f =
  ST.write moderef (Some (Mode Par ps));
  ST.write traceref [];
  f ()
