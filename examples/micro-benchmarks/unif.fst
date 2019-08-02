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
module UnificationTests

type bar : int -> Type
type foo =
  | MkFoo : x:int -> bar x -> foo

let test_pat (f:foo) = match f with
  | MkFoo a b -> a

type baz =
  | MkBaz : x:int -> y:int{y >= x} -> baz

let test_baz (b:baz) = match b with
  | MkBaz x y -> x

let test_baz2 (MkBaz _ _) x y = MkBaz x y

let proj_some x = Some.v x

type snat =
  | Z
  | S of snat

let rec flex_flex_same_var_patterns (a:Type) (env:a) n binders  =
  match n with
  | Z -> flex_flex_same_var_patterns a env n binders
  | S m -> flex_flex_same_var_patterns a env m binders

(* let resolve_flex_flex_non_pattern a b = *)
(*   let f x y = () in *)
(*   f a b *)

let rec test_dependent_subeffect x : int =
  let id t = t in
  test_dependent_subeffect' id x
                            
and test_dependent_subeffect' (id:(int -> int)) args : int = 0

let rec test_closed_rigid_instance (env:'a) k : int = let _ = test_closed_rigid_instance' env 0 in k
and test_closed_rigid_instance' ('b:Type) (env2:'b) args : int = args

let rec test_closed_flex_flex a b c = test_closed_flex_flex' b c
and     test_closed_flex_flex' y z = 0

let rec test_closed_imitate  (a:Type) (b:a) c: list int = test_closed_imitate' a b []
and     test_closed_imitate' (x:Type) (y:x) z: list int = z

let rec test_projection (a:Type) (g: a -> a) =
  let h x =
    let y = test_projection' x in g y in
  ()
and test_projection' (b:Type) (x:b) = x


let rec test_flex_flex_one_pattern (a:Type) (g: a -> a) =
  let h x =
    let _, y = test_flex_flex_one_pattern' x in g y in
  ()
and test_flex_flex_one_pattern' (b:Type) (x:b) = failwith "stub"


let rec test_flex_flex_one_pattern_inf_kind (a:Type) (g: a -> a) =
  let h x =
    let _, y = test_flex_flex_one_pattern_inf_kind' x in g y in
  ()
and test_flex_flex_one_pattern_inf_kind' (x:'b) = failwith "stub"

let rec test_flex_flex_equiv_non_patterns (a:Type) (g:a -> unit) : unit =
  let h x =
    let _, x2 =
      let _, x1 = test_flex_flex_equiv_non_patterns' x in
      0, x1 in
    ()
  in
  ()
    
and test_flex_flex_equiv_non_patterns' (y:'b) = failwith "stub"

type t (a:Type) = 
  | A of a
let h x =
  let x1 = 
    let x2 = failwith "" in A 0
  in match x1 with 
    | A a -> ()
