module Max

val max : int -> int -> Tot int
let max x y = if x > y then x else y

(* intensional using assert *)
val max_with_assert : x:int -> y:int -> Tot int
let max_with_assert x y =
  let i = if x > y then x else y in
  assert (i >= x && i >= y && (i = x || i = y));
  i  (* return i *)

(* intensional using refinement types *)
val max_ref_type : x:int -> y:int ->
                     Tot (i:int{i >= x && i >= y && (i = x || i = y)})
let max_ref_type x y = if x > y then x else y

(* extensional using assert *)
let max_correct1 = assert (forall x y.
      max x y >= x && max x y >= y && (max x y = x || max x y = y))

(* extensional using refinement types *)
val max_correct2 : x:int -> y:int ->
      u:unit{max x y >= x  && max x y >= y && (max x y = x || max x y = y)}
let max_correct2 x y = ()

(* extensional using Lemma *)
val max_correct3 : x:int -> y:int ->
      Lemma (ensures (max x y >= x && max x y >= y
                      && (max x y = x || max x y = y)))
let max_correct3 x y = ()
