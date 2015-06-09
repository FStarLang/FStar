(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/map.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst wysteria.fsi
 --*)

module Wysteria

open Set
open Map
open Heap

open Prims.STATE

(*AR: do we need to copy all these from .fsi ?*)
type prin    (* abstract *)

type prins = set prin

type p_or_s =
  | Par
  | Sec

type mode =
  | Mode: p_or_s:p_or_s -> ps:prins -> mode

let moderef : ref mode = Wysteria.moderef

type Wire (a:Type) = Map.t prin a

type Box: Type -> Type =
  |Mk_box: #a:Type -> v:a -> ps:prins -> Box a

let v_of_box x = Mk_box.v x

let ps_of_box x = Mk_box.ps x

type DelPar (m:mode) (ps:prins) =
  Mode.p_or_s m = Par /\ subset ps (Mode.ps m)

type DelSec (m:mode) (ps:prins) = ps = (Mode.ps m)

type CanUnboxP (#a:Type) (x:Box a) (mode_ps:prins) = b2t (subset mode_ps (ps_of_box x))

type CanUnboxS (#a:Type) (x:Box a) (ps:prins) = b2t (subset (ps_of_box x) ps)

type CanBoxP (#a:Type) (ps:prins) (mode_ps:prins) = b2t (subset ps mode_ps)

type CanMkWireP (#a:Type) (ps:prins) (x:Box a) (mode_ps: prins) =
  CanUnboxP x ps /\ subset ps mode_ps

type CanMkWireS (ps:Box prins) (mode_ps:prins) =
  CanUnboxP ps mode_ps /\ subset (v_of_box ps) mode_ps

type CanMkWireSS (ps:Box prin) (mode_ps:prins) =
  CanUnboxP ps mode_ps /\ mem (v_of_box ps) mode_ps

type CanProjWireP (#a:Type) (x:Wire a) (p:prin) (mode_ps:prins) =
  mode_ps = singleton p /\ Map.contains x p

type CanProjWireS (#a:Type) (x:Wire a) (p:prin) (mode_ps:prins) =
  mem p mode_ps /\ Map.contains x p

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

(* check_marker *)

let unbox_p x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Par /\ CanUnboxP x (Mode.ps m0));
  Mk_box.v x

let unbox_s x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ CanUnboxS x (Mode.ps m0));
  Mk_box.v x

let box_p x ps =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Par /\ CanBoxP ps (Mode.ps m0));
  Mk_box x ps

let mkwire_p ps x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Par /\ CanMkWireP ps x (Mode.ps m0));
  const_on ps (Mk_box.v x)

let mkwire_s ps x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ CanMkWireS ps (Mode.ps m0));
  const_on (Mk_box.v ps) x

let mkwire_ss ps x =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ CanMkWireSS ps (Mode.ps m0));
  const_on (singleton (Mk_box.v ps)) x

let projwire_p x p =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Par /\ CanProjWireP x p (Mode.ps m0));
  Map.sel x p

let projwire_s x p =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Sec /\ CanProjWireS x p (Mode.ps m0));
  Map.sel x p

let concat_wire x y = Map.concat x y

type Share: Type -> Type =
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
  Mk_sh.x x

(**********)

let dom_of_wire w = admit ()

let rec list_to_set l =
  match l with
    | []     -> Set.empty
    | hd::tl -> union (singleton hd) (list_to_set tl)
