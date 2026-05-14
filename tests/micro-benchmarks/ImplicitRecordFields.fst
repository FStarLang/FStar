module ImplicitRecordFields

(* An implicit field, to be solved by unification. *)
noeq
type dyn = {
  #t : Type0;
  x : t;
}

let xx : dyn = { x = 1; }
let yy : dyn = { t = _; x = 1; }

(* The constructor also has an implicit for the relevant field. *)
let _ = assert (xx == Mkdyn 1)

(* Projectors are still there. *)
let _ = assert (xx.t == int)
let _ = assert (xx.x == 1)
let _ = assert (Mkdyn?.t xx == int)
let _ = assert (Mkdyn?.x xx == 1)

(* Any of the fields can be matched. *)
let test0 () =
  match xx with
  | {x} -> assert (x == 1)
  | {t; x} -> assert (x == 1)
  | {t} -> ()

(* In a typeclass, with a meta implicit for a field. *)
open FStar.Tactics

class deq (a : Type) = {
  eq : a -> a -> bool;

  #[easy_fill ()]
  eq_ok : (x:a) -> (y:a) -> eq x y -> x == y;
}

let test #t {| deq t |} (x:t) (y:t) : unit =
  if eq x y then (
    eq_ok x y ();
    assert (x == y)
  )

instance test1 : deq int = {
  eq = (fun x y -> x = y);
}

[@@expect_failure [118]]
instance test1' : deq int = {
  eq_ok = (fun _ _ _ -> ());
}

instance test2 : deq int = {
  eq = (fun x y -> x = y);
  eq_ok = (fun _ _ _ -> ())
}

instance test3 : deq int = {
  eq = (fun x y -> false);
}

[@@expect_failure [19]]
instance test4 : deq int = {
  eq = (fun x y -> true);
}

(* Multiple implicit fields. *)
noeq
type multi_imp = {
  #a : Type0;
  #b : Type0;
  va : a;
  vb : b;
}

let mi1 : multi_imp = { va = 1; vb = true; }
let mi2 : multi_imp = { a = int; va = 1; vb = true; }
let mi3 : multi_imp = { a = int; b = bool; va = 1; vb = true; }

let _ = assert (mi1.va == 1)
let _ = assert (mi1.vb == true)

(* Record update syntax preserves implicit fields. *)
let mi4 = { mi1 with va = 2; }
let _ = assert (mi4.va == 2)
let _ = assert (mi4.vb == true)

(* Projecting the implicit field. *)
let _ = assert (mi1.a == int)
let _ = assert (mi1.b == bool)

(* Missing explicit field should still be an error. *)
[@@expect_failure [118]]
let bad_missing_explicit : dyn = { t = int }

(* Pattern matching: only match some fields. *)
let match_multi (m : multi_imp{m.a == int}) : int =
  match m with
  | { va = v } -> v + 0  // only matching one explicit field

(* Implicit field with a dependency on another field. *)
noeq
type dep_imp = {
  #n : nat;
  v : (x:nat{x < n});
}

let di1 : dep_imp = { n = 10; v = 5; }
let _ = assert (di1.n == 10)

(* If n cannot be inferred, it should fail. *)
[@@expect_failure [66]]
let di_bad : dep_imp = { v = 0; }

(* Fields given out of order. *)
let mi_ooo : multi_imp = { vb = "hello"; va = 42; }
let _ = assert (mi_ooo.a == int)
let _ = assert (mi_ooo.b == string)
