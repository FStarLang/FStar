module NoMethod

open FStar.Tactics.Typeclasses

class c (a : Type) = {
  foo : a -> a;

  [@@@no_method]
  bar : a -> a;
}

instance c_int : c int = {
  foo = (fun x -> x + 1);
  bar = (fun x -> x - 1);
}

let _ = foo 1

(* This fails, there's no global bar. *)
[@@expect_failure [72]]
let _ = bar 1

(* But it can still be accessed via the dictionary. *)
let foobar #t {| d : c t |} : t -> t = 
  fun x -> d.bar (foo x)
