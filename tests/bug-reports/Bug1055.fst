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
module Bug1055

open FStar.ST
open FStar.All

(*
 * F* now checks that top-level unannotated effectful functions have a trivial precondition
 *)

let test1_f (_:unit{false}) : ML unit = ()
(*
 * Fails since it has a non-trivial precondition (false)
 *)
[@expect_failure]
let test1_g () = test1_f (); assert false

(*
 * But will succeed with an explicit annotation
 *)
let test1_g_with_spec ()
  : All unit (fun _ -> False) (fun _ _ _ -> True)
  = test1_f (); assert false


type test2_filename = string
let test2_canWrite (f:test2_filename) = false
let test2_write (f:test2_filename{test2_canWrite f}) (s: string) : ML unit =
  FStar.IO.print_string "A"

[@expect_failure]
let test2_dynamicChecking () =
  test2_write "demo/password" "junk"

[@expect_failure]
let test2_dynamicChecking2 () =
  assert False;
  test2_write "demo/password" "junk"

[@expect_failure]
let test3_write (#a:Type) (r:ref a) = r := 42

[@expect_failure]
let test4_append_to2 (#a:Type) (xs:list a) = ignore(alloc 5); 2 :: xs


(*
 * This works because it has a trivial precondition,
 *   In addition, its postcondition is available to the callers, see test5_client below
 *)
let test5_write (r:ref int) = r := 42

let test5_client (r:ref int) =
  test5_write r;
  let h = ST.get () in
  assert (Heap.sel h r == 42)

(*
 * Partial applications or just renaming works as expected
 *)
let test6_f (x:ref int) (y:int)
  : ST unit
    (requires fun h -> Heap.sel h x == y)
    (ensures fun _ _ _ -> True)
  = ()

let test6_g = test6_f  //the inferred type of test6_g is same as test6_f

let test6_h (x:ref int) = test6_f x  //the inferred type of test6_h is also as expected (application of x to test6_f)

[@expect_failure]
let test6_i (x:ref int) (y:int) = test6_f x y  //this fails since non-trivial precondition
