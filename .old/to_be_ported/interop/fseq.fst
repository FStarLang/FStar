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
(* compilation (2):
   fstar --genIL --odir bin --dotnet4 fseq.fst
   *)

module FSeq
  type fseq 'a =
  | FNil : fseq 'a
  | FCons : 'a -> fseq 'a -> fseq 'a
  
  type principal = string
  and var = principal

  extern reference Seq {language="F#";
                        dll="Seq";
			namespace="";
			classname="Sequence"}
  extern Seq type seq :: * => *
  extern Seq val mkNil : bool -> seq 'a
  extern Seq val mkCons : 'a -> seq 'a -> seq 'a
  
  val transtofs : fseq 'a -> seq 'a
  let rec transtofs (fl:fseq 'a) : seq 'a =
    match fl with
	| FNil -> mkNil false
	| FCons(h, t) -> mkCons h (transtofs t)
  
  (* then some more F* code... *)
	
  val printf_fst : fseq string -> unit
  let rec printf_fst (l:fseq string) =
    match l with
	| FNil -> ()
	| FCons(h, t) -> print_string h; printf_fst t
