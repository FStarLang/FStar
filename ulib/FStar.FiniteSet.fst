(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: John Li
*)
module FStar.FiniteSet

open FStar.List.Tot
open FStar.FunctionalExtensionality

let has_elements (#a:eqtype) (f: a ^-> bool) (xs: list a): prop =
  forall x. f x == x `mem` xs

// Finite sets
let set (a:eqtype) = f:(a ^-> bool){exists xs. f `has_elements` xs}

let set_as_list (s: set 'a): GTot (list 'a) =
  FStar.IndefiniteDescription.indefinite_description_ghost (list 'a)
    (has_elements s)

let intro_set (#a:eqtype) (f: a ^-> bool) (xs: Ghost.erased (list a))
: Pure (set a)
    (requires f `has_elements` xs)
    (ensures fun _ -> True)
= Classical.exists_intro (fun xs -> f `has_elements` xs) xs;
  f 

let mem #a x s = s x

let emptyset #a: set a = intro_set (on_dom a (fun _ -> false)) []

let insert x (s: set 'a): set 'a =
  intro_set (on_dom _ (fun x' -> x = x' || s x')) (x :: set_as_list s)

let set_remove (#a:eqtype) x (s: a ^-> bool): (a ^-> bool) =
  on_dom _ (fun x' -> not (x = x') && s x')

let rec list_remove (#a:eqtype) x (xs: list a) = match xs with
  | [] -> []
  | x' :: xs ->
    if x = x' then list_remove x xs
    else x' :: list_remove x xs
module L = FStar.List.Tot
let rec list_remove_spec (#a:eqtype) f x (xs: list a)
: Lemma
    (requires f `has_elements` xs)
    (ensures set_remove x f `has_elements` list_remove x xs)
    (decreases xs)
= match xs with
  | [] -> ()
  | x' :: xs ->
    let g: (a ^-> bool) = on_dom _ (fun x -> x `L.mem` xs) in
    let f': (a ^-> bool) = on_dom _ (fun x'' -> x'' = x' || g x'') in
    assert (f `feq` f');
    assert (g `has_elements` xs);
    list_remove_spec g x xs;
    assert (set_remove x g `has_elements` list_remove x xs)

let remove x (s: set 'a): set 'a =
  list_remove_spec s x (set_as_list s);
  intro_set (set_remove x s) (list_remove x (set_as_list s))

let insert_remove x (s: set 'a)
: Lemma (requires s x == true) (ensures insert x (remove x s) == s)
  [SMTPat (insert x (remove x s))]
= assert (insert x (remove x s) `feq` s)

let remove_insert x (s: set 'a)
: Lemma (requires s x == false) (ensures remove x (insert x s) == s)
  [SMTPat (remove x (insert x s))]
= assert (remove x (insert x s) `feq` s)

