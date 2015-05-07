module Wysteria

open Set
open Heap

open Prims.STATE

type prin    (* abstract *)

type prins = set prin

type p_or_s =
  | Par
  | Sec

type mode =
  | Mode: p_or_s:p_or_s -> ps:prins -> mode

assume logic val moderef:ref mode

kind Requires         = mode -> Type
kind Ensures (a:Type) = a -> mode -> Type

(* writing it in wp style gets stuck, probably needs extensionality of postconditions *)
effect Wys (a:Type) (req:Requires) (ens:Ensures a) =
  ST a (fun h0 -> req (sel h0 moderef)) (fun h0 x h1 -> sel h1 moderef = sel h0 moderef /\ ens x (sel h0 moderef))

(* defining this shorthand doesn't work, e.g. in with_mode it says expected unit -> Wys bool got unit -> Wys_m bool *)
effect Wys_m (a:Type) (m:mode) ('post:a -> Type) =
  Wys a (fun m0 -> b2t (m0 = m)) (fun x m0 -> 'post x)

type Wire (a:Type) = Map.t prin a

type Box: Type -> Type =
  |Mk_box: #a:Type -> v:a -> m:mode -> Box a

type CanDelegate (m1:mode) (m2:mode) =
  (Mode.p_or_s m2 = Par /\ Mode.p_or_s m1 = Par /\ Subset (Mode.ps m2) (Mode.ps m1)) \/
  (Mode.p_or_s m2 = Sec /\ Mode.ps m2 = Mode.ps m1)

type CanUnbox : #a:Type -> ps:prins -> v:Box a -> Type =
  fun (a:Type) (ps:prins) (v:Box a) -> Subset ps (Mode.ps (Mk_box.m v))

val with_mode: #a:Type -> #req:Requires -> #ens:Ensures a -> m:mode -> =f:(unit -> Wys a req ens) ->
  Wys (Box a) (fun m0 -> CanDelegate m0 m /\ req m) (fun x m0 -> Mk_box.m x = Mode (Mode.p_or_s m0) (Mode.ps m) /\
                                                                 ens (Mk_box.v x) m)
let with_mode m f =
  let m0 = ST.read moderef in
  assert (CanDelegate m0 m);
  ST.write moderef m;
  let x = f () in
  ST.write moderef m0;
  Mk_box x (Mode (Mode.p_or_s m0) (Mode.ps m))

val unbox: #a:Type -> v:Box a ->
  Wys a (fun m0 -> CanUnbox (Mode.ps m0) v) (fun x m0 -> b2t (x = Mk_box.v v))
let unbox (a:Type) (v:Box a) =
  let m0 = ST.read moderef in
  assert (CanUnbox (Mode.ps m0) v);
  Mk_box.v v

val mk_wire: #a:Type -> ps:prins -> v:Box a ->
  Wys (Wire a) (fun m0 -> Subset ps (Mode.ps m0) /\
                          Mode.p_or_s m0 = Par ==> CanUnbox ps v /\
                          Mode.p_or_s m0 = Sec ==> CanUnbox (Mode.ps m0) v)
               (fun x m0 -> b2t (x = Map.const_on ps (Mk_box.v v)))
let mk_wire ps v =
  let m0 = ST.read moderef in
  assert (Subset ps (Mode.ps m0) /\
          Mode.p_or_s m0 = Par ==> CanUnbox ps v /\
          Mode.p_or_s m0 = Sec ==> CanUnbox (Mode.ps m0) v);
  Map.const_on ps (Mk_box.v v)

val project_wire: #a:Type -> v:Wire a -> p:prin ->
  Wys a (fun m0 -> Mode.p_or_s m0 = Par ==> Mode.ps m0 = singleton p /\
                   Mode.p_or_s m0 = Sec ==> mem p (Mode.ps m0) /\
                   Map.contains v p)
        (fun x m0 -> b2t (x = Map.sel v p))
let project_wire v p =
  let m0 = ST.read moderef in
  assert (Mode.p_or_s m0 = Par ==> Mode.ps m0 = singleton p /\
          Mode.p_or_s m0 = Sec ==> mem p (Mode.ps m0) /\
          Map.contains v p);
  Map.sel v p

val concat_wire: #a:Type -> v1:Wire a -> v2:Wire a ->
  Wys (Wire a) (fun m0 -> Map.DisjointDom prin a v1 v2) (fun x m0 -> b2t (x = Map.concat v1 v2))
let concat_wire (a:Type) v1 v2 =
  assert (Map.DisjointDom prin a v1 v2);
  Map.concat v1 v2

type says : #a:Type -> p:prin -> x:a -> Type

assume val read: #a:Type -> unit ->
  Wys a (fun m0 -> Mode.p_or_s m0 = Par /\
                   (exists p. Mode.ps m0 = singleton p))
        (fun x m0 -> (forall p. Mode.ps m0 = singleton p ==> says p x))
