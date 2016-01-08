(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Squash;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Squash.fsti
  --*)
module UnionFind


(** 1. Axiomatization of a disjoint set forest (§4 of FP's paper). *)

(* Taken from [metatheory/attic/norm.fst]. See CH's comments in there. *)
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
  forall (x: v) (y: v) (z: v). f x y /\ f x z ==> y = z
type defined (v: Type) (rel: Relation v) =
  forall (x: v). exists (r: v). rel x r

type is_dsf (v: Type) (d: Set.set v) (f: Relation v) =
  confined v d f /\ functional v f /\ defined v (is_repr v f)


(* In FP's development, the following variables are implicit: [v], [f], [x],
   [z] (and [compress] means [compress v f x z]). *)
type compress (v: Type) (f: Relation v) (x: v) (z: v) : Relation v =
  fun (a: v) (b: v) ->
    (a <> x /\ f a b) \/ (a = x /\ b = z)


val compress_preserves_other_edges:
  v:Type -> f:Relation v -> x:v -> z:v ->
  u:v -> w:v -> Lemma
    (requires (f u w /\ u <> x))
    (ensures (compress v f x z u w))
let compress_preserves_other_edges (v: Type) (f: Relation v) _ _ _ _ =
  ()

(* Now [y] is implicit, and [f x y] is implicit too. *)
val compress_preserves_roots:
  v:Type -> f:Relation v -> x:v -> y:v -> z:v -> r:v -> Lemma
    (requires (is_root v f r /\ f x y))
    (ensures (is_root v (compress v f x z) r))
let compress_preserves_roots (v: Type) (f: Relation v) _ _ _ _ =
  ()

let bind = Squash.bind_squash
let return = Squash.return_squash


val path_same_root:
  v:Type -> d:Set.set v -> f:Relation v ->
  x:v -> z:v -> r:v -> p:path v f x z -> Lemma
    (requires (is_repr v f x r /\ is_dsf v d f))
    (ensures (is_repr v f z r))
    (decreases p)
let rec path_same_root (v: Type) d (f: Relation v) x z r p =
  match p with
  | Refl _ ->
      ()
  | Step _ y _ f_xy path_yz ->
      Squash.give_proof #(is_repr v f z r) (
        bind (Squash.get_proof (path v f x r)) (fun p' ->
          match p' with
          | Step _ y' _ _ path_yr ->
              (* JP: this assert is important for Z3, apparently *)
              assert (y = y');
              let _: path v f y r = path_yr in
              path_same_root v d f y z r path_yz;
              Squash.get_proof (is_repr v f z r)
              ))


(* Now [d] is implicit, [is_dsf d f] and [path f y z] too. *)
val compress_preserves_path_to_roots:
  v:Type -> d:Set.set v -> f:Relation v ->
  x:v -> y:v -> z:v ->
  u:v -> r:v -> p: path v f u r -> Lemma
    (requires (f x y /\ path v f y z /\ is_dsf v d f /\ is_root v f r))
    (ensures (path v (compress v f x z) u r))
    (decreases p)
let rec compress_preserves_path_to_roots (v: Type) d (f: Relation v) x y z u r p =
  if x = u then begin
    Squash.give_proof (return #(path v f x r) p);
    assert (path v f x r);
    assert (is_repr v f x r);
    (* Inject a proof of [path v f x z] in the context. *)
    Squash.give_proof (
      bind (Squash.get_proof (f x y)) (fun proof_x_y ->
      bind (Squash.get_proof (path v f y z)) (fun proof_path_y_z ->
      (* JP: The implicit argument has to be provided here (I guess otherwise
         unification comes up with something else?). *)
      return #(path v f x z) (Step x y z proof_x_y proof_path_y_z))));
    assert (path v f x z);
    admit ()
  end else begin
    match p with
    | Refl _ ->
        (* JP: Inference should be able to figure out the desired post-condition?! *)
        Squash.give_proof (return #(path v (compress v f x z) u r) (Refl u))
    | Step _ u' _ _ p' ->
        (* [u] and [u'] are in relation. *)
        compress_preserves_other_edges v f x z u u';
        (* There is a path from [u'] to [r]. *)
        compress_preserves_path_to_roots v d f x y z u' r p';
        (* We need to construct a proof witness (z3 won't do it for us);
           however, the [Step] case requires a proof witness for the two
           lemmas above; therefore, we use [Squash] to name these proof
           witnesses. *)
        Squash.give_proof (
          bind (Squash.get_proof (compress v f x z u u')) (fun proof_u_u' ->
          bind (Squash.get_proof (path v (compress v f x z) u' r)) (fun proof_path_u'_r ->
          return (Step u u' r proof_u_u' proof_path_u'_r))))
  end


val compress_preserves_is_repr:
  v:Type -> d:Set.set v -> f:Relation v ->
  x:v -> y:v -> z:v -> u:v -> r:v -> Lemma
    (requires (is_dsf v d f /\ f x y /\ is_repr v f y z /\ is_repr v f u r))
    (ensures (is_repr v (compress v f x z) u r))
let compress_preserves_is_repr (v: Type) d (f: Relation v) x y z u r =
  compress_preserves_roots v f x y z r;
  compress_preserves_path_to_roots v d f x y z u r;
  ()


type elem = ref content
and content =
| Link: elem -> content
| Root: nat -> content


val find: x:elem ->
  ST elem
    (requires (fun _ -> True))
    (ensures (fun h_0 y h_1 ->
      is_Root (Heap.sel h_1 y) /\
      (forall z. is_Link (Heap.sel h_0 z) ==> is_Link (Heap.sel h_1 z)) /\
      (forall z. is_Root (Heap.sel h_0 z) ==> is_Root (Heap.sel h_1 z))))
let rec find x =
  match !x with
  | Link r ->
      let r' = find r in
      x := Link r';
      r'
  | Root _ ->
      x


val link: x:elem -> y:elem ->
  ST elem
    (requires (fun h -> is_Root (Heap.sel h x) /\ is_Root (Heap.sel h y)))
    (ensures (fun _ _ _ -> True))
let link x y =
  if x = y then
    x
  else match !x, !y with
  | Root rx, Root ry ->
      if rx < ry then begin
        x := Link y; y
      end else if rx > ry then begin
        y := Link x; x
      end else begin
        y := Link x;
        x := Root (rx + 1);
        x
      end


val union: elem -> elem -> St elem
let union x y =
  let rx = find x in
  let ry = find y in
  let t = !ry in
  link rx ry


val equiv: elem -> elem -> St bool
let equiv x y =
  find x = find y
