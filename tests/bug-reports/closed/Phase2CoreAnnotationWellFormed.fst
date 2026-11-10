module Phase2CoreAnnotationWellFormed

(* The well-formedness of a top-level let's type annotation must be checked.
   Before #4605, phase 1 checked the annotation in admit mode (dropping its
   guard) and phase 2 skipped re-checking it (TcTerm.check_lbtyp), so an
   ill-typed annotation was trusted.

   Here, [fun _ -> ()] is ascribed [unit -> squash False], whose guard is
   [False]. Once the guard is dropped, the SMT encoding asserts a typing axiom
   for the lambda at that arrow type, from which the body proves [False]. The
   old F* accepted [bad] and then [let falso () : Lemma False = bad]. *)

[@@"opaque_to_smt"]
let id (#a:Type) (x:a) : a = x

[@@expect_failure [19]]
let bad : squash (id #(unit -> squash False) (fun _ -> ()) () == () ==> False) = ()
