(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/ordset.fsi $LIB/ordmap.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst wysteria.fsi
 --*)

module Wysteria

open OrdMap
open OrdSet

type prin = nat

let p_cmp p1 p2 = p1 <= p2

type prins = s:ordset prin p_cmp{not (s = empty)}

type eprins = ordset prin p_cmp

type as_mode =
  | Par
  | Sec

type mode =
 | Mode: m:as_mode -> ps:prins -> mode

let moderef : ref mode = Wysteria.moderef

type Box: Type -> prins -> Type =
  |Mk_box: #a:Type -> x:a -> ps:prins -> Box a ps

let v_of_box (#a:Type) #ps x = Mk_box.x x

type Wire (a:Type) = ordmap prin a p_cmp

let w_contains (#a:Type) p x = contains p x
let w_empty (#a:Type) = OrdMap.empty
let w_select (#a:Type) p x = Some.v (select p x)
let w_const_on (#a:Type) eps x = admit ()

val w_concat_helper:
  #a:Type -> w1:Wire a -> w2:Wire a{forall p. w_contains p w1 ==> not (w_contains p w2)}
  -> ps:eprins{forall p. mem p ps ==> contains p w1}
  -> Tot (w:Wire a
          {forall p.(mem p ps ==> (w_contains p w /\ w_select p w = w_select p w1)) /\
                    (w_contains p w2 ==> (w_contains p w /\ w_select p w = w_select p w2)) /\
                    (w_contains p w  ==> (mem p ps \/ w_contains p w2))})            
     (decreases (size ps))
let rec w_concat_helper w1 w2 eps =
  if eps = empty then w2
  else
    let Some p = choose eps in
    let w = w_concat_helper w1 w2 (remove p eps) in
    update p (Some.v (select p w1)) w

let w_concat (#a:Type) w1 w2 = w_concat_helper #a w1 w2 (dom w1)

(**********)

type can_box: a:Type -> ps:prins -> Type

type can_wire: Type -> Type

type DelPar (m:mode) (ps:prins) = Mode.m m = Par /\ subset ps (Mode.ps m)

type DelSec (m:mode) (ps:prins) = ps = Mode.ps m

type CanUnboxPC (mode_ps:eprins) (ps:prins) = b2t (subset mode_ps ps)

type CanUnboxP (m:mode) (ps:prins) = Mode.m m = Par /\ CanUnboxPC (Mode.ps m) ps

type CanUnboxS (m:mode)(ps:prins) =
  Mode.m m = Sec /\ not (intersect (Mode.ps m) ps = empty)

type CanBoxP (a:Type) (m:mode) (ps:prins) =
  Mode.m m = Par /\ can_box a ps /\ subset ps (Mode.ps m)

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

(**********)

let as_par ps f =
  let m0 = ST.read moderef in
  assert (DelPar m0 ps);
  ST.write moderef (Mode Par ps);
  let x = f () in
  ST.write moderef m0;
  Mk_box x ps

let as_sec ps f =
 let m0 = ST.read moderef in
 assert (DelSec m0 ps);
 ST.write moderef (Mode Sec ps);
 let x = f () in
 ST.write moderef m0;
 x

let unbox_p (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxP m0 ps);
  Mk_box.x x

let unbox_s (#a:Type) #ps x =
  let m0 = ST.read moderef in
  assert (CanUnboxS m0 ps);
  Mk_box.x x

let box_p (#a:Type) x ps =
  let m0 = ST.read moderef in
  assert (CanBoxP a m0 ps);
  Mk_box x ps

let mkwire_p (#a:Type) #ps' eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireP a m0 ps' eps);
  w_const_on #a eps (Mk_box.x x)

let mkwire_s (#a:Type) eps x =
  let m0 = ST.read moderef in
  assert (CanMkWireS a m0 eps);
  w_const_on eps x

(*let mkwire_ss ps x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ CanMkWireSS ps (Mode.ps m0));
  const_on (singleton (Mk_box.v ps)) x*)

let projwire_p (#a:Type) x p =
  let m0 = ST.read moderef in
  assert (CanProjWireP m0 x p);
  w_select p x

let projwire_s (#a:Type) x p =
  let m0 = ST.read moderef in
  assert (CanProjWireS m0 x p);
  w_select p x

let concat_wire x y = w_concat x y

(**********)

(*type Share: Type -> Type =
  | Mk_sh: #a:Type -> x:a -> ps:prins -> Share a

let v_of_sh x = Mk_sh.x x

let ps_of_sh x = Mk_sh.ps x

let mk_share x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec);
  Mk_sh x (Mode.ps m0)

let comb_share x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ Mode.ps m0 = ps_of_sh x);
  Mk_sh.x x*)

(**********)
