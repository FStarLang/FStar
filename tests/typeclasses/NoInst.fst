module NoInst

open FStar.Tactics.Typeclasses

[@@fundeps [1]]
class has_pts_to (p x : Type) = {
  pts_to : p -> x -> prop;
}

assume val ref : Type0 -> Type0

instance has_pts_to_ref (x : Type) : has_pts_to (ref x) x = {
  pts_to = (fun r x -> True);
}

type frac a = | Fraction : int -> a -> frac a
[@@noinst]
instance has_pts_to_frac (p x : Type) (d : has_pts_to p x) : has_pts_to p (frac x) = {
  pts_to = (fun _ _ -> True);
}

type frac2 a = | Fraction2 : int -> a -> frac2 a
[@@noinst]
instance has_pts_to_frac2 (p x : Type) (d : has_pts_to p x) : has_pts_to p (frac2 x) = {
  pts_to = (fun _ _ -> True);
}

(* This has to fail, but it has to fail *quickly*. *)
[@@expect_failure [228]]
let test (x:int) y = pts_to x y

let test1 (x : ref int) = pts_to x 2
let test2 (x : ref int) = pts_to x (Fraction 2 42)
