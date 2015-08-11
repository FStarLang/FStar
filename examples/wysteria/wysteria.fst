(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/ordset.fsi $LIB/ordmap.fsi $LIB/list.fst wysteria.fsi
 --*)

module Wysteria

type prin = nat

let p_cmp p1 p2 = p1 <= p2

type eprins = OrdSet.ordset prin p_cmp

let empty = OrdSet.empty #prin #p_cmp

type prins = s:eprins{s =!= empty}

let mem p s = OrdSet.mem #prin #p_cmp p s
let singleton p =
  let s = OrdSet.singleton #prin #p_cmp p in
  let _ = assert (not (s = empty)) in
  s
let subset s1 s2 = OrdSet.subset #prin #p_cmp s1 s2

val empty_union_lem: #a:Type -> #f:OrdSet.cmp a -> s1:OrdSet.ordset a f -> s2:OrdSet.ordset a f
                     -> Lemma (requires (True)) (ensures (OrdSet.union s1 s2 = OrdSet.empty ==>
                                                          (s1 = OrdSet.empty /\ s2 = OrdSet.empty)))
let empty_union_lem (#a:Type) #f s1 s2 = ()

let union s1 s2 =
  empty_union_lem s1 s2;
  OrdSet.union #prin #p_cmp s1 s2

let size s = OrdSet.size #prin #p_cmp s
let choose s = Some.v (OrdSet.choose #prin #p_cmp s)
let remove p s = OrdSet.remove #prin #p_cmp p s

type as_mode =
  | Par
  | Sec

type mode =
 | Mode: m:as_mode -> ps:prins -> mode

let moderef = Wysteria.moderef

type Box: Type -> prins -> Type =
  |Mk_box: #a:Type -> x:a -> ps:prins -> Box a ps

let v_of_box (#a:Type) #ps x = Mk_box.x x

type can_box: a:Type -> ps:prins -> Type

type Wire (a:Type) = OrdMap.ordmap prin a p_cmp

let w_contains (#a:Type) p x = OrdMap.contains p x
let w_empty (#a:Type) = OrdMap.empty
let w_select (#a:Type) p x = Some.v (OrdMap.select p x)
let w_const_on (#a:Type) eps x = OrdMap.const_on eps x

val w_concat_helper:
  #a:Type -> w1:Wire a -> w2:Wire a{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> ps:eprins{forall p. mem p ps ==> OrdMap.contains p w1}
  -> Tot (w:Wire a
          {forall p.(mem p ps ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                    (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                    (w_contains p w  ==> (mem p ps \/ w_contains p w2))})
     (decreases (OrdSet.size ps))
let rec w_concat_helper w1 w2 eps =
  if eps = empty then w2
  else
    let Some p = OrdSet.choose eps in
    let w = w_concat_helper w1 w2 (OrdSet.remove p eps) in
    OrdMap.update p (Some.v (OrdMap.select p w1)) w

let w_concat (#a:Type) w1 w2 = w_concat_helper #a w1 w2 (OrdMap.dom w1)
let w_dom (#a:Type) w = OrdMap.dom w

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
type CanProjWireP (#a:Type) (m:mode) (x:Wire a) (p:prin) =
  Mode.m m = Par /\ Mode.ps m = singleton p /\ w_contains p x
type CanProjWireS (#a:Type) (m:mode) (x:Wire a) (p:prin) =
  Mode.m m = Sec /\ mem p (Mode.ps m) /\ w_contains p x
type CanConcatWire (#a:Type) (x:Wire a) (y:Wire a) =
  forall p. w_contains p x ==> not (w_contains p y)

let as_par ps f =
  let m0 = ST.read moderef in
  assert (DelPar (Some.v m0) ps);
  ST.write moderef (Some (Mode Par ps));
  let x = f () in
  ST.write moderef m0;
  Mk_box x ps

let as_sec ps f =
 let m0 = ST.read moderef in
 assert (DelSec (Some.v m0) ps);
 ST.write moderef (Some (Mode Sec ps));
 let x = f () in
 ST.write moderef m0;
 x

let unbox_p (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxP (Some.v m0) ps);
  Mk_box.x x

let unbox_s (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxS (Some.v m0) ps);
  Mk_box.x x

let box (#a:Type) x ps =
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

let projwire_p (#a:Type) p x =
  let m0 = ST.read moderef in
  assert (CanProjWireP (Some.v m0) x p);
  Some.v (OrdMap.select p x)

let projwire_s (#a:Type) p x =
  let m0 = ST.read moderef in
  assert (CanProjWireS (Some.v m0) x p);
  Some.v (OrdMap.select p x)

let concat_wire x y = w_concat x y

let main (#a:Type) (#req_f:(mode -> Type)) (#ens_f:(mode -> a -> Type)) ps f =
  ST.write moderef (Some (Mode Par ps));
  f () (* TODO: FIXME: expected to write V (f ()), also if try is_Err then fails *)
