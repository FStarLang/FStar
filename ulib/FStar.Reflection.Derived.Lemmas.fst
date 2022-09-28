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
module FStar.Reflection.Derived.Lemmas

open FStar.Reflection.Types
open FStar.Reflection.Builtins
open FStar.Reflection.Data
open FStar.Reflection.Derived

val uncurry : ('a -> 'b -> 'c) -> ('a * 'b -> 'c)
let uncurry f (x, y) = f x y

val curry : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
let curry f x y = f (x, y)

// A glorified `id`
val list_ref : (#a:Type) -> (#p:(a -> Type)) -> (l:list a) ->
                    Pure (list (x:a{p x}))
                         (requires (forall_list p l))
                         (ensures (fun _ -> True))
let rec list_ref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_ref #a #p xs

(*
 * The way back is not stricly true: the list of arguments could grow.
 * It's annoying to even state
 *)
val collect_app_order' : (args:list argv) -> (tt:term) -> (t:term) ->
            Lemma (requires (forall_list (fun a -> fst a << tt) args)
                             /\ t << tt)
                  (ensures (forall_list (fun a -> fst a << tt) (snd (collect_app' args t)))
                           /\ fst (collect_app' args t) << tt)
                  (decreases t)
let rec collect_app_order' args tt t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' (r::args) tt l
    | _ -> ()

val collect_app_order : (t:term) ->
            Lemma (ensures (forall (f:term). forall (s:list argv). (f,s) == collect_app t ==>
                              (f << t /\ forall_list (fun a -> fst a << t) (snd (collect_app t)))
                           \/ (f == t /\ s == [])))
let collect_app_order t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' [r] t l
    | _ -> ()


val collect_app_ref : (t:term) -> (h:term{h == t \/ h << t}) * list (a:argv{fst a << t})
let collect_app_ref t =
    let h, a = collect_app t in
    collect_app_order t;
    h, list_ref #_ #(fun a -> fst a << t) a
