(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module SL.ExamplesAuto

open SL.Base
open SL.AutoTactic

let swap_wp (r1 r2:ref int) = fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> y <*> r2 |> x)

let swap (r1 r2:ref int) : ST unit (swap_wp r1 r2) [ii r1; ii r2] by (sl_auto ())
  = let x = !r1 in
    let y = !r2 in
    r1 := y;
    r2 := x

let rotate_wp (r1 r2 r3:ref int)
  = fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\ p () (r1 |> z <*> r2 |> x <*> r3 |> y)

let rotate (r1 r2 r3:ref int) : ST unit (rotate_wp r1 r2 r3) [ii r1; ii r2; ii r3] by (sl_auto ())
  = swap r2 r3;
    swap r1 r2

let test (r1 r2:ref int) : ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p x m) [ii r1; ii r2] by (sl_auto ())
  = !r1

(*
 * two commands
 *)
let write_read (r1 r2:ref int) : ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p y (r1 |> 2 <*> r2 |> y)) [ii r1; ii r2] by (sl_auto ())
  = r1 := 2;
    !r2

let read_write (r1 r2:ref int) : ST unit (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> x <*> r2 |> x)) [ii r1; ii r2] by (sl_auto ())
  = let x = !r1 in
    r2 := x

let cond_test (r:ref int) (b:bool) : ST unit (fun p m -> exists x. m == r |> x /\ ((b   ==> p () (r |> 1)) /\
                                                                      (~ b ==> p () (r |> 2)))) [ii r]
  by (sl_auto ())

  = if b then r := 1 else r := 2

let rotate_left_or_right (r1 r2 r3:ref int) (b:bool)
  : ST unit (fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\
                              ((b   ==> p () (r1 |> z <*> r2 |> x <*> r3 |> y)) /\
                               (~ b ==> p () (r1 |> y <*> r2 |> z <*> r3 |> x)))) [ii r1; ii r2; ii r3]
  by (sl_auto ())

  = if b then rotate r1 r2 r3 else rotate r3 r2 r1
