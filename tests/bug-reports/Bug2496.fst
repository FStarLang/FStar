module Bug2496

open FStar.List.Tot
open FStar.FunctionalExtensionality

let has_elements (#ty: eqtype) (f: ty ^-> bool) (xs: list ty) : prop =
  forall x. f x == x `mem` xs

type set (ty: eqtype) = f:(ty ^-> bool){exists xs. f `has_elements` xs}

let intro_set (#ty: eqtype) (f: ty ^-> bool) (xs: Ghost.erased (list ty))
: Pure (set ty)
    (requires f `has_elements` xs)
    (ensures fun _ -> True)
= Classical.exists_intro (fun xs -> f `has_elements` xs) xs;
  f 

let set_as_list (#ty: eqtype) (s: set ty): GTot (list ty) =
  FStar.IndefiniteDescription.indefinite_description_ghost (list ty) (has_elements s)

let empty (ty: eqtype): set ty = intro_set (on_dom ty (fun _ -> false)) []

let insert (#ty: eqtype) (x: ty) (s: set ty): set ty =
  intro_set (on_dom _ (fun x' -> x = x' || s x')) (x :: set_as_list s)

let singleton (#ty: eqtype) (x: ty) : set ty =
  insert x (empty ty)

let includes (#ty: eqtype) (s: set ty) (x: ty) : bool =
  s x


let singleton_includes_argument_lemma ()
: Lemma (forall (ty: eqtype) (r: ty). includes (singleton r) r) =
  ()

#push-options "--z3cliopt 'smt.qi.eager_threshold=100' --query_stats --fuel 1 --ifuel 1"
#restart-solver
let singleton_includes_argument_lemma_bad ()
: Lemma (forall (ty: eqtype) (r: ty). includes (singleton r) r) 
= introduce forall (ty: eqtype) (r: ty). includes (singleton r) r
  with ()


