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
module Crypto.Symmetric.Poly1305.Parameters

#reset-options "--max_fuel 8"

(* Standard platform integer size *)
inline_for_extraction let platform_size : pos = 64
(* Integer size after multiplication *)
inline_for_extraction let platform_wide : pos = 64
(* Canonical number of limbs *)
inline_for_extraction let norm_length : pos = 5
inline_for_extraction let nlength : FStar.UInt32.t = 5ul
(* Canonical number of bytes *)
inline_for_extraction let bytes_length : pos = 17
inline_for_extraction let blength : FStar.UInt32.t = assert_norm (17 < pow2 32); 17ul
(* Representation template *)
inline_for_extraction val templ: nat -> Tot pos
inline_for_extraction let templ = fun x -> 26
