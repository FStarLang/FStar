(*
   Copyright 2023 Microsoft Research

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

module MatchBasic
#lang-pulse
open Pulse.Lib.Pervasives


fn test1 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  (* let v = n; *)
  match n {
    0 -> { 1 }
    _ -> { 0 }
  }
}



fn test2 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  let v = n;
  match n {
    0 -> { 1 }
    x -> { x }
  }
}



fn test3 (n:nat)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    0 -> { 1 }
    x -> { let y = x+1; y }
  }
}



// FIXME: Need to qualifiy the constructors or otherwise they desugar to
// the (not yet in scope) type below. Only in batch mode apparently.

fn test3_5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Prelude.None -> { (-1) }
    Prelude.Some x -> { x }
  }
}


noeq
type optionint =
  | None
  | Some of int


fn test4 (n:optionint) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    None -> { 0 }
    Some x -> { x }
  }
}



fn test5 (n:option int) (z:bool)
  requires emp
  returns r:int
  ensures emp
{
  match n {
    Prelude.None -> { (-1) }
    Prelude.Some x -> { x }
  }
}



fn listid (xs : list int)
  requires emp
  returns r:(list int)
  ensures emp
{
  match xs {
    [] -> { Nil #int }
    hd :: tl -> { Cons #int hd tl }
  }
}



fn hd (xs : list int)
  requires emp
  returns r:(int)
  ensures emp
{
  match xs {
    [] -> { 0 }
    hd :: tl -> { let t = tl; hd }
  }
}



fn tl (xs : list int)
  requires emp
  returns r:(list u#0 int)
  ensures emp
{
  match xs {
    [] -> { Nil #int }
    hd :: tl -> { tl }
  }
}


[@@expect_failure [19]]
fn incomplete (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    [] -> { 1 }
  }
}



fn partial_complete (xs : (xs:list int{List.Tot.length xs == 0}))
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    [] -> { 1 }
  }
}



fn breq_1 (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    [] -> { assert (pure (List.Tot.length xs == 0)); 0 } // works because of branch eq
    _ :: _ -> { 1 } // assert (pure (isCons xs)); cons_hd xs }
  }
}



fn breq_2 (xs : list int)
  requires emp
  returns r:int
  ensures emp
{
  match xs {
    [] -> { assert (pure (List.Tot.length xs == 0)); 0 }
    _ :: _ -> { Cons?.hd xs }
  }
}

