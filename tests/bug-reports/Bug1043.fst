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
module Bug1043

open FStar.List

let rec memP_append #a (x: a) (l: list a) :
  Lemma (List.memP x l ==>
         (exists (l1 l2: list a). l == l1 @ (x :: l2))) =
    match l with
    | [] -> ()
    | h :: t ->
      FStar.Classical.or_elim
        #(x == h)
        #(memP x t)
        #(fun _ -> exists (l1 l2: list a). l == l1 @ (x :: l2))
        (fun _ -> assert (l == [] @ (x :: t)))
        (fun _ -> let (l1, l2) = memP_append x t in ())
