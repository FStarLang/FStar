module Bug419

kind Relation (v: Type) = v -> v -> Type
type path (v: Type) (r: v -> v -> Type): v -> v -> Type =
  | Refl: x:v -> path v r x x
  | Step: x:v -> y:v -> z:v -> r x y -> path v r y z -> path v r x z

type is_root (v: Type) (f: Relation v) (x: v) =
  forall y. ~(f x y)
type is_repr (v: Type) (f: Relation v) (x: v) (r: v) =
  path v f x r /\ is_root v f r

type confined (v: Type) (d: Set.set v) (f: Relation v) =
  forall (x: v) (y: v). path v f x y ==> Set.mem x d /\ Set.mem y d
type functional (v: Type) (f: Relation v) =
  forall (x: v) (y: v) (z: v). f x z /\ f y z ==> x = y
type defined (v: Type) (rel: Relation v) =
  forall (x: v). exists (r: v). rel x r

type is_dsf (v: Type) (d: Set.set v) (f: Relation v) =
  confined v d f /\ functional v f /\ defined v (is_repr v f)

val path_same_repr:
  v:Type -> d:Set.set v -> f:Relation v ->
  x:v -> r:v -> z:v -> p_1:path v f x z -> p_2:path v f x r -> Lemma
    (requires (is_dsf v d f /\ is_root v f r))
    (ensures (is_repr v f z r))
    (decreases %[p_1, p_2])
let rec path_same_repr (v: Type) d (f: Relation v) x r z p_1 p_2 =
  match p_1, p_2 with
  | Refl _, Refl _ ->
    admit ()
