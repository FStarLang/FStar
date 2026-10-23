module Phase2CoreLambdaResidual

(* The same lambda, elaborated twice with residual types [bool] and [_:bool{...}], must be
   encoded to the same SMT term: Core erases refinements from lambda residual types. *)
assume val bare (f: (int -> int -> bool)) (x:int) : bool
assume val spec (o: int -> int -> prop) (x:int) : bool
assume val correct (o: int -> int -> prop)
  (f: (x:int -> y:int -> Pure bool True (fun z -> z == true <==> o x y))) (x:int)
  : Lemma (spec o x == bare f x)

let po (o: int -> int -> bool) (x y:int) : prop = o x y == true

let test (o: int -> int -> bool) : Pure (int -> bool) True (fun g -> forall x. g x == spec (po o) x) =
  Classical.forall_intro (correct (po o) (fun x1 x2 -> o x1 x2));
  let p' = bare (fun x1 x2 -> o x1 x2) in
  assert (forall x. p' x == spec (po o) x);
  p'
