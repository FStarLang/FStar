(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
(* compilation (3):
   fsc -r bin\Seq.dll -r bin\FSeq.dll -o bin\wrapper.exe --platform:x86 wrapper.fs
   *)

module Wrapper
  open Sequence

  let l = Cons("f", Cons("st", Cons("ar OK!\n", Nil))) in
  let l2 = transtofst l in
  FSeq.printf_fst l2
  (* let l3 = Tofs.transtofs l2 
  printf_fs l3 *)
