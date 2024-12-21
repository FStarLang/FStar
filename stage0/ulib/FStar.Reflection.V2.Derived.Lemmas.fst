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
module FStar.Reflection.V2.Derived.Lemmas

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data
open FStar.Reflection.V2.Collect
open FStar.List.Tot

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

let forallP (p: 'a -> Type) (l: list 'a): Type
  = forall (x: 'a). memP x l ==> p x
// Precedence relation on the element of a list
unfold let (<<:) (l: list 'a) (r: 'r)
  = forallP (fun x -> x << r) l

// A glorified `id`
val list_ref : (#a:Type) -> (#p:(a -> Type)) -> (l:list a) ->
                    Pure (list (x:a{p x}))
                         (requires (forallP p l))
                         (ensures (fun _ -> True))
let rec list_ref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_ref #a #p xs

val collect_app_order' : (args:list argv) -> (tt:term) -> (t:term) ->
             Lemma (requires args <<: tt /\ t << tt)
                   (ensures (let fn, args' = collect_app_ln' args t in
                             args' <<: tt /\ fn << tt))
                   (decreases t)
let rec collect_app_order' args tt t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' (r::args) tt l
    | _ -> ()

val collect_app_order : (t:term) ->
            Lemma (ensures (forall (f:term). forall (s:list argv). (f,s) == collect_app_ln t ==>
                              (f << t /\ s <<: t)
                            \/ (f == t /\ s == [] /\ ~(Tv_App? (inspect_ln t)))))
let collect_app_order t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' [r] t l
    | _ -> ()

val collect_app_ref : (t:term) -> (h:term{h == t \/ h << t}) & list (a:argv{fst a << t})
let collect_app_ref t =
    let h, a = collect_app_ln t in
    collect_app_order t;
    h, list_ref a

(**** [collect_abs_ln t] is smaller than [t] *)
let rec collect_abs_order' (bds: binders) (tt t: term)
  : Lemma (requires t << tt /\ bds <<: tt)
          (ensures (let bds', body = collect_abs' bds t in
                    (bds' <<: tt /\ body << tt)))
          (decreases t)
  = match inspect_ln_unascribe t with
    | Tv_Abs b body -> collect_abs_order' (b::bds) tt body
    | _ -> ()

val collect_abs_ln_order : (t:term) ->
            Lemma (ensures forall bds body.
                           (bds, body) == collect_abs_ln t ==>
                                (body << t /\ bds <<: t)
                              \/ (body == t /\ bds == [])
                  )
let collect_abs_ln_order t =
    match inspect_ln_unascribe t with
    | Tv_Abs b body -> collect_abs_order' [b] t body;
                      let bds, body = collect_abs' [] t in
                      Classical.forall_intro (rev_memP bds)
    | _ -> ()

val collect_abs_ln_ref : (t:term) -> list (bd:binder{bd << t}) & (body:term{body == t \/ body << t})
let collect_abs_ln_ref t =
    let bds, body = collect_abs_ln t in
    collect_abs_ln_order t;
    list_ref bds, body



(**** [collect_arr_ln_bs t] is smaller than [t] *)
let rec collect_arr_order' (bds: binders) (tt: term) (c: comp)
  : Lemma (requires c << tt /\ bds <<: tt)
          (ensures (let bds', c' = collect_arr' bds c in
                    bds' <<: tt /\ c' << tt))
          (decreases c)
  = match inspect_comp c with
    | C_Total ret ->
        ( match inspect_ln_unascribe ret with
        | Tv_Arrow b c -> collect_arr_order' (b::bds) tt c
        | _ -> ())
    | _ -> ()

val collect_arr_ln_bs_order : (t:term) ->
            Lemma (ensures forall bds c.
                           (bds, c) == collect_arr_ln_bs t ==>
                                (c << t /\ bds <<: t)
                              \/ (c == pack_comp (C_Total t) /\ bds == [])
                  )
let collect_arr_ln_bs_order t =
  match inspect_ln_unascribe t with
  | Tv_Arrow b c -> collect_arr_order' [b] t c;
                   Classical.forall_intro_2 (rev_memP #binder);
                   inspect_pack_comp_inv (C_Total t)
  | _ -> inspect_pack_comp_inv (C_Total t)

val collect_arr_ln_bs_ref : (t:term) -> list (bd:binder{bd << t})
                                     & (c:comp{ c == pack_comp (C_Total t) \/ c << t})
let collect_arr_ln_bs_ref t =
    let bds, c = collect_arr_ln_bs t in
    collect_arr_ln_bs_order t;
    list_ref bds, c
