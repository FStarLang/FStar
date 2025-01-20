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
module FStar.Reflection.V1.Derived

open FStar.Stubs.Reflection.Types
open FStar.Reflection.Const
open FStar.Stubs.Reflection.V1.Builtins
open FStar.Stubs.Reflection.V1.Data
open FStar.Order
open FStar.Stubs.VConfig

let bv_of_binder (b : binder) : bv = (inspect_binder b).binder_bv

let rec inspect_ln_unascribe (t:term) : tv:term_view{tv << t /\ notAscription tv} =
    match inspect_ln t with
    | Tv_AscribedT t' _ _ _
    | Tv_AscribedC t' _ _ _ -> inspect_ln_unascribe t'
    | tv -> tv

(*
 * AR: add versions that take attributes as arguments?
 *)
let mk_binder (bv : bv) (sort : typ) : binder =
  pack_binder {
    binder_bv=bv;
    binder_qual=Q_Explicit;
    binder_attrs=[];
    binder_sort = sort;
  }

let mk_implicit_binder (bv : bv) (sort : typ) : binder =
  pack_binder {
    binder_bv=bv;
    binder_qual=Q_Implicit;
    binder_attrs=[];
    binder_sort = sort;
  }

let type_of_binder (b : binder) : typ =
    (inspect_binder b).binder_sort

val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns

(* Helpers for dealing with nested applications and arrows *)
let rec collect_app_ln' (args : list argv) (t : term) : Tot (term & list argv) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_App l r ->
        collect_app_ln' (r::args) l
    | _ -> (t, args)

val collect_app_ln : term -> term & list argv
let collect_app_ln = collect_app_ln' []

let rec mk_app (t : term) (args : list argv) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack_ln (Tv_App t x)) xs

// Helper for when all arguments are explicit
let mk_e_app (t : term) (args : list term) : Tot term =
    let e t = (t, Q_Explicit) in
    mk_app t (List.Tot.Base.map e args)

let u_unk : universe = pack_universe Uv_Unk

let rec mk_tot_arr_ln (bs: list binder) (cod : term) : Tot term (decreases bs) =
    match bs with
    | [] -> cod
    | (b::bs) -> pack_ln (Tv_Arrow b (pack_comp (C_Total (mk_tot_arr_ln bs cod))))

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
    List.Tot.Base.map type_of_binder bs, c

let rec collect_abs' (bs : list binder) (t : term) : Tot (list binder & term) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs_ln : term -> list binder & term
let collect_abs_ln t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.Base.rev bs, t')

let fv_to_string (fv:fv) : string = implode_qn (inspect_fv fv)

let mk_stringlit (s : string) : term =
    pack_ln (Tv_Const (C_String s))

let mk_strcat (t1 t2 : term) : term =
    mk_e_app (pack_ln (Tv_FVar (pack_fv ["Prims"; "strcat"]))) [t1; t2]

let mk_cons (h t : term) : term =
   mk_e_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [h; t]

let mk_cons_t (ty h t : term) : term =
   mk_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [(ty, Q_Implicit); (h, Q_Explicit); (t, Q_Explicit)]

let rec mk_list (ts : list term) : term =
    match ts with
    | [] -> pack_ln (Tv_FVar (pack_fv nil_qn))
    | t::ts -> mk_cons t (mk_list ts)

let mktuple_n (ts : list term{List.Tot.Base.length ts <= 8}) : term =
    match List.Tot.Base.length ts with
    | 0 -> pack_ln (Tv_Const C_Unit)
    | 1 -> let [x] = ts in x
    | n -> begin
           let qn = match n with
                    | 2 -> mktuple2_qn
                    | 3 -> mktuple3_qn
                    | 4 -> mktuple4_qn
                    | 5 -> mktuple5_qn
                    | 6 -> mktuple6_qn
                    | 7 -> mktuple7_qn
                    | 8 -> mktuple8_qn
           in mk_e_app (pack_ln (Tv_FVar (pack_fv qn))) ts
           end

let destruct_tuple (t : term) : option (list term) =
    let head, args = collect_app_ln t in
    match inspect_ln head with
    | Tv_FVar fv ->
        if List.Tot.Base.mem
                (inspect_fv fv) [mktuple2_qn; mktuple3_qn; mktuple4_qn; mktuple5_qn;
                                 mktuple6_qn; mktuple7_qn; mktuple8_qn]
        then Some (List.Tot.Base.concatMap (fun (t, q) ->
                                      match q with
                                      | Q_Explicit -> [t]
                                      | _ -> []) args)
        else None
    | _ -> None

let mkpair (t1 t2 : term) : term =
    mktuple_n [t1;t2]

let rec head (t : term) : term =
    match inspect_ln t with
    | Tv_Match t _ _
    | Tv_Let _ _ _ _ t _
    | Tv_Abs _ t
    | Tv_Refine _ _ t
    | Tv_App t _
    | Tv_AscribedT t _ _ _
    | Tv_AscribedC t _ _ _ -> head t

    | Tv_Unknown
    | Tv_Uvar _ _
    | Tv_Const _
    | Tv_Type _
    | Tv_Var _
    | Tv_BVar _
    | Tv_FVar _
    | Tv_UInst _ _
    | Tv_Arrow _ _
    | Tv_Unsupp -> t

(** Checks if a term `t` is equal to some FV (a top level name).
Ignores universes and ascriptions. *)
let is_fvar (t : term) (nm:string) : bool =
    match inspect_ln_unascribe t with
    | Tv_FVar fv
    | Tv_UInst fv _ -> implode_qn (inspect_fv fv) = nm
    | _ -> false

(** Checks if a term `t` is equal to any FV (a top level name) from
those given in the list. Ignores universes and ascriptions. *)
let rec is_any_fvar (t : term) (nms:list string) : bool =
    match nms with
    | [] -> false
    | v::vs -> is_fvar t v || is_any_fvar t vs

let is_uvar (t : term) : bool =
    match inspect_ln (head t) with
    | Tv_Uvar _ _ -> true
    | _ -> false

let binder_set_qual (q:aqualv) (b:binder) : Tot binder =
  let bview = inspect_binder b in
  pack_binder {bview with binder_qual=q}

(** Set a vconfig for a sigelt *)
val add_check_with : vconfig -> sigelt -> Tot sigelt
let add_check_with vcfg se =
  let attrs = sigelt_attrs se in
  let vcfg_t = embed_vconfig vcfg in
  let t = `(check_with (`#vcfg_t)) in
  set_sigelt_attrs (t :: attrs) se

let un_uinst (t:term) : term =
  match inspect_ln t with
  | Tv_UInst fv _ -> pack_ln (Tv_FVar fv)
  | _ -> t

(* Returns [true] iff the term [t] is just the name [nm], though
possibly universe-instantiated and applied to some implicit arguments.
*)
let rec is_name_imp (nm : name) (t : term) : bool =
    begin match inspect_ln_unascribe t with
    | Tv_FVar fv
    | Tv_UInst fv _ ->
        if inspect_fv fv = nm
        then true
        else false
    | Tv_App l (_, Q_Implicit) ->
        is_name_imp nm l
    | _ -> false
    end

(* If t is of the shape [squash t'], return [Some t'],
otherwise [None]. *)
let unsquash_term (t : term) : option term =
    match inspect_ln_unascribe t with
    | Tv_App l (r, Q_Explicit) ->
        if is_name_imp squash_qn l
        then Some r
        else None
    | _ -> None

(* As [unsquash_term], but returns the original term if
[t] is not a squash. *)
let maybe_unsquash_term (t : term) : term =
    match unsquash_term t with
    | Some t' -> t'
    | None -> t
