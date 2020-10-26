(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author(s): N. Swamy, A. Fromherz
*)
module LList.Invariant
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (cell a);
  data: a;
}
#pop-options


let next (c:cell 'a) : t 'a = c.next
let data (c:cell 'a) : 'a = c.data
let mk_cell (n: t 'a) (d:'a) = {
  next = n;
  data = d
}
let hd l = Cons?.hd l
let tl l = Cons?.tl l

let null_llist (#a:Type)  = admit()
let ptr_eq (#a:Type) (x y:t a) = admit()


////////////////////////////////////////////////////////////////////////////////
// Main llist invariant
////////////////////////////////////////////////////////////////////////////////
let rec llist' (#a:Type) (ptr:t a)
                         (l:list (cell a))
    : Tot slprop (decreases l)
    =
    match l with
    | [] ->
      pure (ptr == null_llist)

    | hd :: tl ->
      pure (ptr =!= null_llist) `star`
      pts_to ptr full_perm hd `star`
      llist' (next hd) tl
let llist = llist'


(* Helper lemmas/rewritings *)

let intro_llist_nil a =
  change_slprop emp (llist null_llist [])
    (fun m -> pure_interp (null_llist #a == null_llist) m;
           norm_spec [delta; zeta] ((llist (null_llist #a) [])))

let intro_llist_cons #a ptr hd tl =
  intro_pure (ptr =!= null_llist);
  change_slprop (pure (ptr =!= null_llist) `star`
                 pts_to ptr full_perm hd `star`
                 llist' (next hd) tl)
                (llist ptr (hd::tl))
                (fun _ -> norm_spec [delta;zeta] (llist ptr (hd::tl)))

let elim_llist_cons #a ptr hd tl =
  change_slprop (llist ptr (hd::tl))
    (pure (ptr =!= null_llist) `star`
      pts_to ptr full_perm hd `star`
      llist' (next hd) tl)
    (fun _ -> ());
  drop (pure (ptr =!= null_llist))
