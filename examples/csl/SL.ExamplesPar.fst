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
module SL.ExamplesPar

open SL.Base
open SL.AutoTactic

let left  r () : ST int (fun p m -> exists v. m == r |> v /\ p 1 (r |> v)) [ii r] by (sl_auto ()) = 1
let right r () : ST int (fun p m -> exists v. m == r |> v /\ p 2 (r |> v)) [ii r] by (sl_auto ()) = 2

let par1 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [] by (sl_auto ())
=
  let (x, y) = par (left r) (right s) in
  x + y

let par2 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [ii r; ii s] by (sl_auto ())
=
  let (x, y) = par (left s) (right r) in
  x + y


let par3 (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z

(* Funny, the VC for this is much smaller and verifies a lot quicker *)
#push-options "--use_two_phase_tc false"
let par3' (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z
#pop-options

let ret (x:'a) () : ST 'a (fun p m -> m == emp /\ p x m) [] =
  x

let set_to_2 (r : ref int) () : ST int (fun p m -> exists v. m == (r |> v) /\ p 1 (r |> 2)) [ii r] =
  r := 2;
  1

(* Actually changing a reference *)
let par_set (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> 2)) [ii r] by (sl_auto ())
=
  let (x, y) = par (set_to_2 r) (ret 2) in
  x + y
