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
module FStar.Class.Eq.Raw

class deq a = {
  eq : a -> a -> bool;
}

let eq_instance_of_eqtype (#a:eqtype) : deq a = {
  eq = (fun x y -> x = y)
}

// FIXME: It would be easier to have a single eqtype instance,
// but resolution will sometimes use for any type, even though
// it should not.
instance int_has_eq : deq int = eq_instance_of_eqtype
instance unit_has_eq : deq unit = eq_instance_of_eqtype
instance bool_has_eq : deq bool = eq_instance_of_eqtype
instance string_has_eq : deq string = eq_instance_of_eqtype

let rec eqList #a (eq : a -> a -> bool) (xs ys : list a) : Tot bool =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> eq x y && eqList eq xs ys
  | _, _ -> false

instance eq_list (_ : deq 'a) : deq (list 'a) = {
  eq = eqList eq;
}

instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a & 'b) = {
  eq = (fun (a,b) (c,d) -> eq a c && eq b d)
}

instance eq_option (_ : deq 'a) : deq (option 'a) = {
  eq = (fun o1 o2 ->
    match o1, o2 with
    | None, None -> true
    | Some x, Some y -> eq x y
    | _, _ -> false);
}

val (=) : #a:Type -> {| deq a |} -> a -> a -> bool
let (=) = eq
