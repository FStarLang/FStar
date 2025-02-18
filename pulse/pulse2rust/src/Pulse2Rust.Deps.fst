(*
   Copyright 2023 Microsoft Research

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

module Pulse2Rust.Deps

open FStarC
open FStarC.Util
open FStarC.List
open FStarC.Effect

open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env
open Pulse2Rust.Extract

open RustBindings

open FStarC.Class.Setlike

module S = FStarC.Extraction.ML.Syntax


let empty_defs : reachable_defs = RBSet.empty ()
let singleton (p:S.mlpath) : reachable_defs = singleton (S.string_of_mlpath p)

let reachable_defs_list (#a:Type) (f:a -> reachable_defs) (l:list a) : reachable_defs =
  List.fold_left (fun defs x -> union defs (f x)) (empty ()) l

let reachable_defs_option (#a:Type) (f:a -> reachable_defs) (o:option a) : reachable_defs =
  match o with
  | None -> empty_defs
  | Some x -> f x

let rec reachable_defs_mlty (t:S.mlty) : reachable_defs =
  let open S in
  match t with
  | MLTY_Var _ -> empty_defs
  | MLTY_Fun (t1, _, t2) -> union (reachable_defs_mlty t1) (reachable_defs_mlty t2)
  | MLTY_Named (tps, p) ->
    union (reachable_defs_list reachable_defs_mlty tps) (singleton p)
  | MLTY_Tuple ts -> reachable_defs_list reachable_defs_mlty ts
  | MLTY_Top
  | MLTY_Erased -> empty_defs

let reachable_defs_mltyscheme ((_, t):S.mltyscheme) : reachable_defs =
  reachable_defs_mlty t

let rec reachable_defs_mlpattern (p:S.mlpattern) : reachable_defs =
  let open S in
  match p with
  | MLP_Wild
  | MLP_Const _
  | MLP_Var _ -> empty_defs
  | MLP_CTor (c, ps) ->
    union (singleton c) (reachable_defs_list reachable_defs_mlpattern ps)
  | MLP_Branch ps -> reachable_defs_list reachable_defs_mlpattern ps
  | MLP_Record (syms, fs) ->
    union (Class.Setlike.singleton (String.concat "." syms))
          (reachable_defs_list (fun (_, p) -> reachable_defs_mlpattern p) fs)
  | MLP_Tuple ps -> reachable_defs_list reachable_defs_mlpattern ps

let rec reachable_defs_expr' (e:S.mlexpr') : reachable_defs =
  let open S in
  match e with
  | MLE_Const _
  | MLE_Var _ -> empty_defs
  | MLE_Name p -> singleton p
  | MLE_Let (lb, e) -> union (reachable_defs_mlletbinding lb) (reachable_defs_expr e)
  | MLE_App (e, es) ->
    union (reachable_defs_expr e) (reachable_defs_list reachable_defs_expr es)
  | MLE_TApp (e, ts) ->
    union (reachable_defs_expr e) (reachable_defs_list reachable_defs_mlty ts)
  | MLE_Fun (args, e) ->
    union (reachable_defs_list (fun b -> reachable_defs_mlty b.S.mlbinder_ty) args)
          (reachable_defs_expr e)
  | MLE_Match (e, bs) ->
    union (reachable_defs_expr e)
          (reachable_defs_list reachable_defs_mlbranch bs)
  | MLE_Coerce (e, t1, t2) ->
    union (reachable_defs_expr e)
          (union (reachable_defs_mlty t1) (reachable_defs_mlty t2))
  | MLE_CTor (p, es) ->
    union (singleton p)
          (reachable_defs_list reachable_defs_expr es)
  | MLE_Seq es
  | MLE_Tuple es -> reachable_defs_list reachable_defs_expr es
  | MLE_Record (p, n, fs) ->
    union (Class.Setlike.singleton (String.concat "." (p@[n])))
          (reachable_defs_list (fun (_, e) -> reachable_defs_expr e) fs)
  | MLE_Proj (e, _) -> reachable_defs_expr e
  | MLE_If (e1, e2, e3_opt) ->
    union (reachable_defs_expr e1)
          (union (reachable_defs_expr e2)
                 (reachable_defs_option reachable_defs_expr e3_opt))
  | MLE_Raise (p, es) ->
    union (singleton p)
          (reachable_defs_list reachable_defs_expr es)
  | MLE_Try (e, bs) -> union (reachable_defs_expr e)
                             (reachable_defs_list reachable_defs_mlbranch bs)

and reachable_defs_expr (e:S.mlexpr) : reachable_defs =
  union (reachable_defs_expr' e.expr)
        (reachable_defs_mlty e.mlty)

and reachable_defs_mlbranch ((p, wopt, e):S.mlbranch) : reachable_defs =
  union (reachable_defs_mlpattern p)
        (union (reachable_defs_option reachable_defs_expr wopt)
               (reachable_defs_expr e))

and reachable_defs_mllb (lb:S.mllb) : reachable_defs =
  union (reachable_defs_option reachable_defs_mltyscheme lb.mllb_tysc)
        (reachable_defs_expr lb.mllb_def)

and reachable_defs_mlletbinding ((_, lbs):S.mlletbinding) : reachable_defs =
  reachable_defs_list reachable_defs_mllb lbs

let reachable_defs_mltybody (t:S.mltybody) : reachable_defs =
  let open S in
  match t with
  | MLTD_Abbrev t -> reachable_defs_mlty t
  | MLTD_Record fs ->
    reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) fs
  | MLTD_DType cts ->
    reachable_defs_list (fun (_, dts) -> reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) dts) cts

let reachable_defs_one_mltydecl (t:S.one_mltydecl) : reachable_defs =
  reachable_defs_option reachable_defs_mltybody t.tydecl_defn

let reachable_defs_mltydecl (t:S.mltydecl) : reachable_defs =
  reachable_defs_list reachable_defs_one_mltydecl t

let reachable_defs_mlmodule1 (m:S.mlmodule1) : reachable_defs =
  let open S in
  let defs =
    match m.mlmodule1_m with
    | MLM_Ty t -> reachable_defs_mltydecl t
    | MLM_Let lb -> reachable_defs_mlletbinding lb
    | MLM_Exn (_, args) ->
      reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) args
    | MLM_Top e -> reachable_defs_expr e
    | MLM_Loc _ -> empty_defs in
  // print2 "reachable defs for %s are %s\n"
    // (S.mlmodule1_to_string m)
    // (reachable_defs_to_string defs);
  defs

let reachable_defs_decls (decls:S.mlmodule) : reachable_defs =
  reachable_defs_list reachable_defs_mlmodule1 decls

let decl_reachable (reachable_defs:reachable_defs) (mname:string) (d:S.mlmodule1) : bool =
  let open S in
  match d.mlmodule1_m with
  | MLM_Ty t ->
    List.existsb (fun ty_decl -> mem (mname ^ "." ^ ty_decl.tydecl_name) reachable_defs) t
  | MLM_Let (_, lbs) ->
    List.existsb (fun lb -> mem (mname ^ "." ^ lb.mllb_name) reachable_defs) lbs
  | MLM_Exn (p, _) -> false
  | MLM_Top _ -> false
  | MLM_Loc _ -> false

let rec topsort (d:dict) (grey:list string) (black:list string) (root:string)
  : (list string & list string) =  // grey and black
  let grey = root::grey in
  let deps = root |> SMap.try_find d |> must |> (fun (deps, _, _) -> deps) in
  let deps = deps |> List.filter (fun f -> List.mem f (SMap.keys d) && not (f = root)) in
  if List.existsb (fun d -> List.mem d grey) deps
  then failwith (format1 "cyclic dependency: %s" root);
  let deps = deps |> List.filter (fun f -> not (List.mem f black)) in
  let grey, black = List.fold_left (fun (grey, black) dep ->
    topsort d grey black dep) (grey, black) deps in
  List.filter (fun g -> not (g = root)) grey,
  (if List.mem root black then black else root::black)

let rec topsort_all (d:dict) (black:list string)
  : list string =
  
  if List.for_all (fun f -> List.contains f black) (SMap.keys d)
  then black
  else
    let rem = List.filter (fun f -> not (List.contains f black)) (SMap.keys d) in
    let root = List.nth rem (List.length rem - 1) in
    let grey, black = topsort d [] black root in
    if List.length grey <> 0
    then failwith "topsort_all: not all files are reachable";
    topsort_all d black
