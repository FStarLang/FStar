module Bug2641

open FStar.List.Tot
open FStar.Tactics.Typeclasses

//
// Original report by Cezar and Theo
//
// The original repro was phrased in terms of an indexed effect FREEwp built
// from the free monad below.  Indexed effects are gone, so we use the free
// monad directly (with `let!` notation).
//

noeq
type free (a:Type u#a) : Type u#(max a 1) =
| Return : a -> free a
| PartialCall : (pre:prop) -> cont:((squash pre) -> free u#a a) -> free a

let rec free_bind (#a:Type u#a) (#b:Type u#b) (l:free a) (k: a -> free b) : free b =
  match l with
  | Return x -> k x
  | PartialCall pre fnc ->
    PartialCall pre (fun _ -> free_bind (fnc ()) k)

let ( let! ) (#a:Type u#a) (#b:Type u#b) (l:free a) (k: a -> free b) : free b =
  free_bind l k

let partial_call (pre:prop) : free (squash pre) =
  PartialCall pre (fun x -> Return x)

(** *** Spec **)

(** monotonicity seems relevant **)
let hist_monotonic0 (a:Type) (wp:(a -> prop) -> prop) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

let hist a = wp:((a -> prop) -> prop){hist_monotonic0 a wp}

val hist_ord (#a : Type) : hist a -> hist a -> prop
let hist_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

let hist_return (x:'a) : hist 'a =
  fun p -> p x

let hist_bind (#a #b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun p -> w (fun r -> kw r p)

let partial_call_wp (pre:prop) : hist (squash pre) =
  fun p -> pre /\ p ()

(** *** Effect observation **)

val theta : #a:Type -> free a -> hist a
let rec theta m =
  match m with
  | Return x -> hist_return x
  | PartialCall pre k ->
    hist_bind (partial_call_wp pre) (fun r -> theta (k r))

let dm_free (a:Type) (wp:hist a) =
  tree:(free a){wp `hist_ord` theta tree}

val dm_free_return : (a:Type) -> (x:a) -> dm_free a (hist_return x)
let dm_free_return a x = Return x

val lemma_monad_morphism  :
  a: Type ->
  b: Type ->
  v: free a ->
  f: (x: a -> free b) ->
  Lemma (hist_bind (theta v) (fun x -> theta (f x)) `hist_ord` theta (free_bind v f))
let rec lemma_monad_morphism a b v f =
  match v with
  | Return _ -> ()
  | PartialCall pre k ->
    calc (hist_ord) {
      hist_bind (theta (PartialCall pre k)) (fun x -> theta (f x));
      == { _ by (FStar.Tactics.compute ()) }
      hist_bind (hist_bind (partial_call_wp pre) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { _ by (FStar.Tactics.compute ()) }
      hist_bind (partial_call_wp pre) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      `hist_ord` {
        let rhs1 : squash pre -> hist b = fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)) in
        let rhs2 : squash pre -> hist b = fun r -> theta (free_bind (k r) f) in
        introduce forall (r:squash pre). (rhs1 r) `hist_ord` (rhs2 r) with begin
          lemma_monad_morphism _ _ (k r) f
        end
      }
      theta (PartialCall pre (fun r -> free_bind (k r) f));
      `hist_ord` { _ by (FStar.Tactics.compute ()) }
      theta (free_bind (PartialCall pre k) f);
    }

val dm_free_bind  :
  a: Type ->
  b: Type ->
  wp_v: hist a ->
  wp_f: (_: a -> Tot (hist b)) ->
  v: dm_free a wp_v ->
  f: (x: a -> Tot (dm_free b (wp_f x))) ->
  Tot (dm_free b (hist_bind wp_v wp_f))
let dm_free_bind a b wp_v wp_f v f =
  lemma_monad_morphism a b v f;
  free_bind v f

val dm_free_subcomp :
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_free a wp1 ->
  Pure (dm_free a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_free_subcomp a wp1 wp2 f = f

class compilable (t:Type) = {
  comp_type : Type;
  compile: t -> comp_type
}

instance compile_option (t:Type) {| d1:compilable t |} : compilable (option t) = {
  comp_type = option (d1.comp_type);
  compile = (fun x ->
    match x with
    | Some r -> Some (compile r)
    | None -> None)
}

[@@ expect_failure [19]]
let test_assert_false
  (t1:Type)
  (t2:Type)
  {| d2:compilable t2 |}
  (f:(t1 -> free (option t2)))
  (x:t1) :
  Lemma False =
  let _ : dm_free (option d2.comp_type) (hist_bind (fun p -> forall r . p r)
                                                   (fun (r:option t2) -> hist_return (compile #(option t2) #(compile_option t2 #d2) r))) =
       (let! v = f x in Return (compile #(option t2) #(compile_option t2 #d2) v)) in
  assert (False)


//
// A repro without using typeclasses etc.
//

let compile_option2 : (option int -> option int) =
  fun x -> match x with
        | None -> None
        | Some r -> Some r

[@@ expect_failure [19]]
let test_assert_false2
  (f:(unit -> free (option int))) :
  Lemma False =
  let _ : dm_free (option int) (hist_bind (fun p -> forall r . p r)
                                        (fun (r:option int) -> hist_return ((compile_option2 r)))) =
       (let! eff_val = f () in
        Return (compile_option2 eff_val)) in
  assert False
