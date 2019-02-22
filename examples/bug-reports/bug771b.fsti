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
module Bug771b

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

val len: pos
val clen: l:FStar.UInt32.t{FStar.UInt32.v l = len}

val template: idx:nat{idx < len} -> Tot pos
val ctemplate: idx:nat{idx < len} -> Tot (x:FStar.UInt32.t{template idx = FStar.UInt32.v x}) // works
