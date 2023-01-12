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
module ReflectionMisc

open FStar.Tactics

let mk (#a: Type u#a) (u: universe_view) (#[exact (pack_ln (Tv_Type (pack_universe u)))]r: a) (): a = r
let univs (_: Type u#a) (_: Type u#b): _ = 
  assert (mk (Uv_Name ("a", range_of 1)) () == Type u#a);
  assert (mk (
    Uv_Max [
      pack_universe (Uv_Name ("a", range_of 1))
    ]
  ) () == Type u#a);
  assert (mk (
    Uv_Max [
      pack_universe (Uv_Name ("a", range_of 1));
      pack_universe (Uv_Name ("b", range_of 1));
    ]
  ) () == Type u#(max a b));
  assert (mk (
    Uv_Max [
      pack_universe (Uv_Succ (pack_universe (Uv_Name ("a", range_of 1))));
      pack_universe (Uv_Name ("b", range_of 1));
    ]
  ) () == Type u#(max (a+1) b));
  assert (mk (
    Uv_Succ (pack_universe (Uv_Max [
      pack_universe (Uv_Name ("a", range_of 1));
      pack_universe (Uv_Name ("b", range_of 1));
    ]))
  ) () == Type u#(1+(max a b)));
  assert (mk (
    Uv_Succ (pack_universe (Uv_Max [
      pack_universe (Uv_Name ("a", range_of 1));
      pack_universe (Uv_Name ("b", range_of 1));
      pack_universe Uv_Zero
    ]))
  ) () == Type u#(1+(max a b)))

let tm = `(1,2)

let _ = assert True
            by (let r = destruct_tuple tm in
                match r with
                | Some [a;b]  -> guard (a `term_eq` (`1));
                                 guard (b `term_eq` (`2))
                | _ -> fail "")

//
//Returns a Type u#1
//  By reflecting on int -> Tot<0> int,
//  Taking the universe from Tot
//  And applying Succ to it
//
// let get_u () : Tac term =
//   let t = `(int -> Tot u#0 int) in
//   match inspect t with
//   | Tv_Arrow _ c ->
//     (match inspect_comp c with
//      | C_Total _ u _ -> pack_ln (Tv_Type (pack_universe (Uv_Succ u)))
//      | _ -> fail "2")
//   | _ -> fail "3"

// let test0 (#[exact (get_u ())]t:Type u#2) () : Type u#2 = t
// let test1 () = test0 ()

// let test2 (#[exact (get_u ())]t:Type u#1) () : Type u#1 = t
// [@@ expect_failure [228]]
// let test3 () = test2 ()
