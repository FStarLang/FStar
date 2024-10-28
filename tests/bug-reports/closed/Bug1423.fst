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
module Bug1423

open FStar.List.Tot

val subset_filter: #a: eqtype -> f: (a -> Tot bool) -> l: list a ->
  Lemma (requires True) (ensures (subset (filter f l) l))
let subset_filter #_ f l =
  let rec aux l' = match l' with
  | [] -> ()
  | h :: t -> ()
  in aux (filter f l); admit ()
