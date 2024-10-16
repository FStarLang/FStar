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
module FStar.Reflection.V2.Collect

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

let rec inspect_ln_unascribe (t:term) : tv:term_view{tv << t /\ notAscription tv} =
    match inspect_ln t with
    | Tv_AscribedT t' _ _ _
    | Tv_AscribedC t' _ _ _ -> inspect_ln_unascribe t'
    | tv -> tv

// (* Helpers for dealing with nested applications and arrows *)
let rec collect_app_ln' (args : list argv) (t : term) : Tot (term & list argv) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_App l r ->
        collect_app_ln' (r::args) l
    | _ -> (t, args)

val collect_app_ln : term -> term & list argv
let collect_app_ln = collect_app_ln' []

let rec collect_arr' (bs : list binder) (c : comp) : Tot (list binder & comp) (decreases c) =
    begin match inspect_comp c with
    | C_Total t ->
        begin match inspect_ln_unascribe t with
        | Tv_Arrow b c ->
            collect_arr' (b::bs) c
        | _ ->
            (bs, c)
        end
    | _ -> (bs, c)
    end

val collect_arr_ln_bs : typ -> list binder & comp
let collect_arr_ln_bs t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t)) in
    (List.Tot.Base.rev bs, c)

val collect_arr_ln : typ -> list typ & comp
let collect_arr_ln t =
    let bs, c = collect_arr_ln_bs t in
    List.Tot.Base.map (fun b -> (inspect_binder b).sort) bs, c

let rec collect_abs' (bs : list binder) (t : term) : Tot (list binder & term) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs_ln : term -> list binder & term
let collect_abs_ln t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.Base.rev bs, t')