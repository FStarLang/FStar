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
module Benton2004.Aux

type rel (t: Type0) = t -> t -> GTot Type0

(* NOTE: I declare this `holds` here to prevent Z3 from looping. (`abstract` is not enough.) *)

val holds (#t: Type0) (p: rel t) (s s' : t) : GTot Type0
val holds_equiv (#t: Type0) (p: rel t) (s s' : t) : Lemma
  (holds p s s' <==> p s s')
