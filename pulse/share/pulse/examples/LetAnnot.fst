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

module LetAnnot
#lang-pulse

open Pulse.Lib.Pervasives

(* This module just contains some unit tests for annotations on letbindings. *)
#lang-pulse


fn test1 (_:unit) requires emp returns _:unit ensures emp {
  let x : nat = 42;
  ()
}


[@@expect_failure]

fn test2 (_:unit) requires emp returns _:unit ensures emp {
  let x : bool = 42;
  ()
}


[@@expect_failure]

fn test3 (_:unit) requires emp returns _:unit ensures emp {
  let x : pos = -1;
  ()
}



fn testmut1 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : nat = 42;
  ()
}


[@@expect_failure]

fn testmut2 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : bool = 42;
  ()
}


[@@expect_failure]

fn testmut3 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : pos = -1;
  ()
}



fn ret (#a:Type0) (x:a) requires emp returns x:a ensures emp {
  x
}



fn testst1 (_:unit) requires emp returns _:unit ensures emp {
  let x : int = ret 42;
  (* NB: This will not work at any type other than int (currently).
  The annotation is not used for inference of stateful assignments,
  and for them the annotated type must syntactically match the
  computed one. *)
  ()
}


[@@expect_failure]

fn testst2 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : bool = 42;
  ()
}


[@@expect_failure]

fn testst3 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : pos = -1;
  ()
}

