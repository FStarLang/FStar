(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module Microsoft.FStar.LazySet

//TODO: Use a better representation for the underlying set instead of lists?

type iset<'t> = 
  | Set of list<'t>
  | Delayed of (('t -> 't -> bool) -> list<set<'t>>)
and set<'t> = ref<iset<'t>>

let minus_l eq l1 l2     = l1 |> List.partition (fun x -> l2 |> Util.for_some (eq x)) |> snd
let intersect_l eq l1 l2 = l1 |> List.partition (fun x -> l2 |> Util.for_some (eq x)) |> fst
let union_l eq l1 l2     = (minus_l eq l1 l2)@l2

let rec claim eq (f:set<'a>) = match !f with 
  | Set l -> l
  | Delayed fs -> 
    let l = fs eq |> List.fold_left (fun out f -> union_l eq (claim eq f) out) [] in
    f := Set l;
    l

let set_of_thunk t = Util.mk_ref <| Delayed (fun eq -> [t()])
let set_of_list (l:list<'a>) = Util.mk_ref (Set l)

let list_of_set eq (l:set<'a>) = claim eq l

let union (s1:set<'a>) (s2:set<'a>) = Util.mk_ref <| Delayed (fun eq -> [s1;s2])

let difference (s1:set<'a>) (s2:set<'a>) = Util.mk_ref <| Delayed (fun eq -> 
    let l1 = claim eq s1 in 
    let l2 = claim eq s2 in
    [Util.mk_ref <| Set (minus_l eq l1 l2)])

let intersection (s1:set<'a>) (s2:set<'a>) = Util.mk_ref <|
    Delayed (fun eq -> 
        let l1 = claim eq s1 in
        let l2 = claim eq s2 in
        [Util.mk_ref <| Set (intersect_l eq l1 l2)])
