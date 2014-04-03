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
(* compilation (1):
   fsc --platform:x86 --target:library -o bin\Seq.dll seq.fs
   *)   
   
module Sequence
  type seq<'a> =
  | Nil
  | Cons of 'a * seq<'a>

  (* For each constructor to be used from F*, write a function that wraps
     the constructor application *)
  (* F# erases units to void, sometimes, therefore 
     don't use unit in functions to be called from F* *)
  let mkNil (b:bool) = Nil
  (* Tupled arguments to F# constructors should be curried
     in the wrapped constructor *)
  let mkCons (hd:'a) (tl:seq<'a>) = Cons(hd, tl)
  
  let rec transtofst (l:seq<'a>) : FSeq.fseq<'a> =
    match l with
    | Nil -> new FSeq.FNil<'a>() :> FSeq.fseq<'a> (* F# expects explict upcasts  for .NET *)
    | Cons(h, t) -> new FSeq.FCons<'a>(h, transtofst t) :> FSeq.fseq<'a>

  let rec printf_fs (l:seq<string>) =
    match l with
    | Nil -> ()
    | Cons(h, t) -> printf "%s" h; printf_fs t
