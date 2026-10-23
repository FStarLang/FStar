(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Hash

open FStarC.Effect

(* An OCaml [int]. *)
type hash_code = FStarC.SmallInt.t

[@@custard_extern "Z.of_int"]
let to_int _ = admit ()

[@@custard_extern "(fun (x:int) y -> Z.of_int (x - y))"]
let cmp_hash _ _ = admit ()

(* NB: F* integers are unbounded, so we cannot use Z.to_int here: it raises
   Z.Overflow on large literals (e.g. 0xffffffffffffffff).  Small integers are
   immediate in Zarith though, and are their own hash: this is on the path of
   every term construction, so avoid the C call for them. *)
[@@custard_extern "(fun i -> if Obj.is_int (Obj.repr i) then (Obj.magic i : int) else Z.hash i)"]
let of_int _ = admit ()

[@@custard_extern "BatHashtbl.hash"]
let of_string _ = admit ()

(* The combining step of MurmurHash64A, on OCaml's 63-bit integers.

   This runs on every term construction (term hash codes are computed eagerly,
   see FStarC.Syntax.Syntax.mk), so it should be cheap: it used to be Bob
   Jenkins' 96-bit mix (http://burtleburtle.net/bob/hash/doobs.html), whose
   long dependency chain cost about three times as much, and which had more
   collisions in our tests.  Simpler mixes, e.g. the one from Lean
   (src/runtime/hash.h), produce many collisions on terms such as those in
   tests/FStar.Tests.Pars.test_hashes. *)
[@@custard_extern "(fun (a:int) (b:int) -> let k = b * 0x1bd1e9955bd1e995 in let k = k lxor (k lsr 31) in let k = k * 0x1bd1e9955bd1e995 in (a lxor k) * 0x1bd1e9955bd1e995)"]
let mix _ _ = admit ()

[@@custard_extern "string_of_int"]
let string_of_hash_code _ = admit ()
