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
module Bug400

val bar : (u:unit & unit) -> Tot unit
let bar p =
  let r1 = fst (p, p) in    (* fails *)
  let r1, _ = p, p in (* also fails *)
  let r1 = p in       (* works *)
  let (|_, _|) = r1 in
  ()
