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

module Bug45
#lang-pulse

open Pulse.Main
open Pulse.Lib.Pervasives

assume val domain : a:Type -> (a -> slprop) -> Type

assume val spawn :
 (#a:Type) -> (#pre : slprop) -> (#post : (a -> slprop)) ->
 ($f : unit -> stt a pre post) ->
 stt (domain a post) pre (fun _ -> emp)

assume val join :
  (#a:Type) -> (#post : (a -> slprop)) ->
  domain a post ->
  stt a emp post

let rec fib0 (n:nat) : nat =
  if n < 2 then n
  else fib0 (n-1) + fib0 (n-2)

let just #a (x:a) : stt a emp (fun _ -> emp) =
  sub_stt _ _ (magic()) (magic ()) (Pulse.Lib.Core.return_stt_noeq x (fun _ -> emp))


fn pth (n:pos) ()
  requires emp
  returns n:nat
  ensures emp
{
  fib0 (n-1)
}


[@@expect_failure]

fn pfib (n:nat)
  requires emp
  returns n:nat
  ensures emp
{
  if (n < 20) {
    fib0 n
  } else {
    //let c = (fun () -> just #_ (fib0 (n-1))) <: unit -> stt nat emp (fun _ -> emp);
    // let th = spawn #nat #emp #(fun _ -> emp) c;
    let th = spawn #nat #emp #(fun (n:nat) -> emp) (pth n);
    let r = 123; // fib (n-2) + join th;
    r
  }
}

