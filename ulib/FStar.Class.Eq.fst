(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Class.Eq

open FStar.Tactics.Typeclasses
module Raw = FStar.Class.Eq.Raw

let decides_eq (#a:Type) (f : a -> a -> bool) : prop =
  forall x y. f x y <==> x == y

class deq a = {
  raw : Raw.deq a;
  eq_dec : squash (decides_eq raw.eq);
}

(* Superclass *)
instance deq_raw_deq (a:Type) (d:deq a) : Raw.deq a = d.raw

let eq (#a:Type) {| d : deq a |} (x y : a) : bool =
  d.raw.eq x y

let eq_instance_of_eqtype (#a:eqtype) {| Raw.deq a |} : deq a = {
  raw = Raw.eq_instance_of_eqtype #a;
  eq_dec = ();
}

instance int_has_eq : deq int = eq_instance_of_eqtype
instance unit_has_eq : deq unit = eq_instance_of_eqtype
instance bool_has_eq : deq bool = eq_instance_of_eqtype
instance string_has_eq : deq string = eq_instance_of_eqtype

let eqList_ok (#a:Type) (d : deq a) : Lemma (decides_eq #(list a) (Raw.eqList d.raw.eq)) =
  let rec aux (xs ys : list a) : Lemma (Raw.eqList d.raw.eq xs ys <==> xs == ys) =
    match xs, ys with
    | x::xs, y::ys ->
      aux xs ys
    | [], [] -> ()
    | _ -> ()
  in
  Classical.forall_intro_2 aux;
  ()

instance eq_list (d : deq 'a) : deq (list 'a) = {
  raw = Raw.eq_list d.raw;
  eq_dec = eqList_ok d;
}

instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a & 'b) = {
  raw = solve;
  eq_dec = ();
}

instance eq_option (_ : deq 'a) : deq (option 'a) = {
  raw = solve;
  eq_dec = ();
}

val (=) : #a:Type -> {| deq a |} -> a -> a -> bool
let (=) = eq
