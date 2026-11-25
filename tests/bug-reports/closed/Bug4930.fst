module Bug4930

(* FStarLang/FStar#4930: [clearly_inhabited] judged a singleton refinement
   [x:t{x == e}] inhabited whenever [t] was, without checking that [e] has
   type [t]. With [t] itself a refinement, [x:(y:int{y == 0}){x == 1}] is
   empty, yet [exists] over it simplified to [True], proving [False].
   [clearly_inhabited] no longer considers refinements at all. *)

[@@expect_failure [19]]
let bad_exists () : Lemma False =
  assert_norm (exists (x:(y:int{y == 0}){x == 1}). True);
  FStar.Classical.exists_elim False #(x:(y:int{y == 0}){x == 1}) #(fun _ -> True) () (fun _ -> ())

[@@expect_failure [19]]
let bad_nonempty () : Lemma False =
  assert_norm (nonempty (x:(y:int{y == 0}){x == 1}));
  FStar.Classical.exists_elim False #(x:(y:int{y == 0}){x == 1}) #nonempty_tag () (fun _ -> ())

[@@expect_failure [19]]
let bad_arrow () : Lemma False =
  assert_norm (exists (f:int -> (y:(z:int{z == 0}){y == 1})). True);
  FStar.Classical.exists_elim False #(int -> (y:(z:int{z == 0}){y == 1})) #(fun _ -> True) () (fun f -> let _ = f 0 in ())

(* A divergent top-level definition ending in a literal still needs no
   witness: its inferred refinement is dropped before [nonempty] is checked. *)
let rec loop (n:nat) : Dv int = if n = 0 then 1 else loop (n - 1)
let d = loop 3
