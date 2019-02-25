module Predicates

open FStar.Tactics

class has_stronger (a:Type)= {
  stronger : a -> a -> Type
}

(* These instances are in reverse order of generality so tcresolve
 * solves correctly. We should add priorities. *)

instance stronger_def #a : has_stronger a = {
  stronger = (==)
}

instance _ : has_stronger Type = {
  stronger = fun p q -> p ==> q
}

instance _ : has_stronger Type0 = {
  stronger = fun p q -> p ==> q
}

instance stronger_gtot_arr (_ : has_stronger 'a) (_ : has_stronger 'b) : has_stronger ('a -> GTot 'b) = {
  stronger = fun f1 f2 -> forall x1 x2. x1 `stronger` x2 ==> f1 x1 `stronger` f2 x2
}

instance stronger_arr (_ : has_stronger 'a) (_ : has_stronger 'b) : has_stronger ('a -> 'b) = {
  stronger = fun f1 f2 -> forall x1 x2. x1 `stronger` x2 ==> f1 x1 `stronger` f2 x2
}

//instance stronger_arr' #a #b (_ : has_stronger b) : has_stronger (a -> b) = {
//  stronger = fun f1 f2 -> forall x. f1 x `stronger` f2 x
//}

class has_monotonic (a:Type) = {
  monotonic : a -> Type
}

instance monotonic_from_stronger #a (_ : has_stronger a) : has_monotonic a = {
  monotonic = fun x -> stronger x x
}

let test1 (p : pure_wp 'a) = monotonic p

let test2 (wp : pure_wp 'a) (f : 'a -> pure_wp 'b)
  : Lemma (requires (monotonic wp /\ monotonic f))
          (ensures (monotonic (pure_bind_wp range_0 _ _ wp f))) = ()

(* GM: Why the hell do I have to write down this type? *)
(* Without it, we get:
   (Error) Prims.GTot (*?u39*) _ is not a subtype of the expected type Prims.GTot (pure_wp _) *)
let test3 () : Lemma (monotonic #(
      r1: range ->
      a: Type ->
      b: Type ->
      wp1: pure_wp a ->
      wp2: (_: a -> Prims.GTot (pure_wp b)) ->
      p: pure_post b
    -> Prims.Tot pure_pre)
 pure_bind_wp) = ()

[@expect_failure]
let _ = assert (monotonic (fun p -> p ==> False))
