(*
   Copyright 2025 Microsoft Research

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
module Pulse.Lib.SmallType
module U = Pulse.Lib.Raise

// Type class of types that can be stored in a reference
[@@Tactics.Typeclasses.tcclass; erasable]
let small_type = U.raisable u#a u#3

inline_for_extraction noextract
instance small_type_non_info : Pulse.Lib.NonInformative.non_informative (small_type u#a) =
  U.raisable_non_info

instance small_type0 : small_type u#0 = U.raisable_inst
instance small_type1 : small_type u#1 = U.raisable_inst u#1 u#3
instance small_type2 : small_type u#2 = U.raisable_inst u#2 u#3
instance small_type3 : small_type u#3 = U.raisable_inst u#3 u#3

instance of_small_type {| inst : small_type u#a |} : U.raisable u#a u#3 = inst
