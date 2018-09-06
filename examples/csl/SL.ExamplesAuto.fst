module SL.ExamplesAuto

open SL.Base
open SL.AutoTactic

let swap_wp (r1 r2:ref int) = fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> y <*> r2 |> x)

(* #set-options "--tactic_trace_d 2 --debug SL.ExamplesAuto" *)

//#set-options "--tactic_trace"

let swap (r1 r2:ref int) : ST unit (swap_wp r1 r2) [tosref r1; tosref r2] by (sl_auto ())
  = let x = !r1 in
    let y = !r2 in
    r1 := y;
    r2 := x

let rotate_wp (r1 r2 r3:ref int)
  = fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\ p () (r1 |> z <*> r2 |> x <*> r3 |> y)

let rotate (r1 r2 r3:ref int) : ST unit (rotate_wp r1 r2 r3) [tosref r1; tosref r2; tosref r3] by (sl_auto ())
  = swap r2 r3;
    swap r1 r2

let test (r1 r2:ref int) : ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p x m) [tosref r1; tosref r2] by (sl_auto ())
  = !r1

(*
 * two commands
 *)
let write_read (r1 r2:ref int) : ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p y (r1 |> 2 <*> r2 |> y)) [tosref r1; tosref r2] by (sl_auto ())
  = r1 := 2;
    !r2

let read_write (r1 r2:ref int) : ST unit (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> x <*> r2 |> x)) [tosref r1; tosref r2] by (sl_auto ())
  = let x = !r1 in
    r2 := x

let cond_test (r:ref int) (b:bool) : ST unit (fun p m -> exists x. m == r |> x /\ ((b   ==> p () (r |> 1)) /\
                                                                      (~ b ==> p () (r |> 2)))) [tosref r]
  by (sl_auto ())

  = if b then r := 1 else r := 2

let rotate_left_or_right (r1 r2 r3:ref int) (b:bool)
  : ST unit (fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\
                              ((b   ==> p () (r1 |> z <*> r2 |> x <*> r3 |> y)) /\
 			      (~ b ==> p () (r1 |> y <*> r2 |> z <*> r3 |> x)))) [tosref r1; tosref r2; tosref r3]
  by (sl_auto ())

  = if b then rotate r1 r2 r3 else rotate r3 r2 r1
