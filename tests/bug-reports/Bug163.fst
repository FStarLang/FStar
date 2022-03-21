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
module Bug163

open FStar.ST

val swap_add_sub : #int:Type -> r1:(ref int) -> r2:(ref int) -> ST unit
      (requires (fun h -> True))
      (ensures (fun h' _ h -> True))
let swap_add_sub #int r1 r2 =
  write r1 (read r1 + read r2);
  write r2 (read r1 - read r2);
  write r1 (read r1 - read r2)
