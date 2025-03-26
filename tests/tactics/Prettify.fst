module Prettify

open FStar.Tactics.PrettifyType { entry, named }
open FStar.Bijection

(* Note the parenthesis, we don't yet support tuple3, 4, etc. *)
type myty =
  either ((int & int) & (int & string)) bool

%splice[
  myty_pretty;
  myty_pretty_left;
  myty_pretty_right;
  Mkmyty_pretty0;
  Mkmyty_pretty1
] (entry "_pretty" (`%myty))

(* Sanity check *)
let right (x : myty) : r:myty_pretty{myty_pretty_right x == r} =
  match x with
  | Inl ((x, y), (z, s)) -> Mkmyty_pretty0 x y z s
  | Inr b -> Mkmyty_pretty1 b

let left (x : myty_pretty) : r:myty{myty_pretty_left x == r} =
  match x with
  | Mkmyty_pretty0 x y z s -> Inl ((x, y), (z, s))
  | Mkmyty_pretty1 b -> Inr b

(* Named test: *)
type named_ty =
  either
    (named "Case1" ((named "x" int & int) & (named "y" int & string)))
    (named "Case2" (named "b" bool))

%splice[
  named_ty_pretty;
  Case1;
  Case2;
  named_ty_pretty_bij;
] (entry "_pretty" (`%named_ty))

// test bijection

let _ = assert (Inl ((1, 2), (3, "a")) >> named_ty_pretty_bij == Case1 1 2 3 "a")
let _ = assert (Case2 false << named_ty_pretty_bij == Inr false)

(* This test doesn't work.. apparently the projectors from a spliced
type can't be called? *)
// let test (i : named_ty_pretty) =
//   match i with
//   | Case1 _ _ _ _ ->
//     let _ = Case1?.x i in
//     let _ = Case1?.y i in
//     ()
//   | Case2 _ ->
//     let _ = Case2?.b i in
//     ()

type t2 = tuple2 int int
%splice[t2_pretty] (entry "_pretty" (`%t2))

type t3 = tuple2 int (either bool string)
%splice[t3_pretty] (entry "_pretty" (`%t3))

type t4 = either t3 (tuple2 int (either bool string))
%splice[t4_pretty; t4_pretty_left_right] (entry "_pretty" (`%t4))

let inv (x:t4) = t4_pretty_left_right x

type t5 =
  either (int -> int) <|
  either int <|
  string

[@@1]
noextract
noeq (* will only go to the generated type. *)
unfold
%splice[t5_quals; t5_quals_left_right] (entry "_quals" (`%t5))

type big =
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  either int <|
  string

%splice[] (entry "_pretty" (`%big))


type bigger =
  either (
  either (
  either (
  either (
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  either (tuple2 (tuple2 (tuple2 int int) (tuple2 int int)) (tuple2 (tuple2 int int) (tuple2 int int))) <|
  string
  ) bool
  ) bool
  ) bool
  ) bool

[@@no_auto_projectors] // makes it a bit faster
%splice[] (entry "_pretty" (`%bigger))
