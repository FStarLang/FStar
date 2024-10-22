module Bug2641

open FStar.List.Tot
open FStar.Tactics.Typeclasses

//
// Original report by Cezar and Theo
//

noeq
type free (a:Type u#a) : Type u#(max a 1) =
| Return : a -> free a
| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free u#a a) -> free a

let rec free_bind (#a:Type u#a) (#b:Type u#b) (l:free a) (k: a -> free b) : free b =
  match l with
  | Return x -> k x
  | PartialCall pre fnc ->
    PartialCall pre (fun _ -> free_bind (fnc ()) k)

(** *** Spec **)
(** monotonicity seems relevant **)
let hist a = wp:(pure_wp' a){pure_wp_monotonic0 a wp}

val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

let hist_return (x:'a) : hist 'a =
  fun p -> p x

let hist_bind (#a #b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun p -> w (fun r -> kw r p)

let wp_lift_pure_hist (w : pure_wp 'a) : hist 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  w

let partial_call_wp (pre:pure_pre) : hist (squash pre) = 
  let wp' : pure_wp' (squash pre) = fun p -> pre /\ p () in
  wp'


(** *** Dijkstra Monad **)
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

val lift_pure_dm_free :
  a: Type ->
  w: pure_wp a ->
  f: (_: eqtype_as_type unit -> PURE a w) ->
  Tot (dm_free a (wp_lift_pure_hist w))
let lift_pure_dm_free a w f =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  PartialCall (as_requires w) (fun proof -> Return (f proof))

total
reifiable
reflectable
effect {
  FREEwp (a:Type) (wp : hist a) 
  with {
       repr       = dm_free
     ; return     = dm_free_return
     ; bind       = dm_free_bind 
     ; subcomp    = dm_free_subcomp
     }
}

sub_effect PURE ~> FREEwp = lift_pure_dm_free

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
  (f:(t1 -> FREEwp (option t2) (fun p -> (forall r. p r)))) 
  (x:t1) : 
  Lemma False =
  let _ : dm_free (option d2.comp_type) (hist_bind (fun p -> forall r . p r)
                                                   (fun (r:option t2) -> hist_return (compile #(option t2) #(compile_option t2 #d2) r))) =
       reify (compile #(option t2) #(compile_option t2 #d2) (f x)) in
  assert (False)


//
// A repro without using typeclasses etc.
//

let compile_option2 : (option int -> option int) =
  fun x -> match x with
        | None -> None
        | Some r -> Some r

[@@ expect_failure [19]]
let test_assert_false
  (f:(unit -> FREEwp (option int) (fun p -> (forall r. p r)))) : 
  Lemma False =
  let _ : dm_free (option int) (hist_bind (fun p -> forall r . p r)
                                        (fun (r:option int) -> hist_return ((compile_option2 r)))) =
       reify (let eff_val = f () in
              compile_option2 eff_val) in
  assert False
