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
module IntNormalization

open FStar.UInt32
open FStar.Tactics.V2

(* Testing that the normalizer reduces these equalities *)

let by_red () : Tac unit =
    norm [primops; delta];
    trivial ()

let _ = assert (0ul = 0ul)      by by_red ()
let _ = assert (0ul == 0ul)     by by_red ()
let _ = assert (0ul === 0ul)    by by_red ()

let _ = assert (0ul <> 1ul)     by by_red ()
let _ = assert (~(0ul == 1ul))  by by_red ()
let _ = assert (0ul =!= 1ul)    by by_red ()
