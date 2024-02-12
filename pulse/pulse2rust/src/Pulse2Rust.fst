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

module Pulse2Rust

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env
open Pulse2Rust.Extract

open RustBindings

module S = FStar.Extraction.ML.Syntax
module EUtil = FStar.Extraction.ML.Util

module UEnv = FStar.Extraction.ML.UEnv

let empty_defs : reachable_defs = Set.empty ()
let singleton (p:S.mlpath) : reachable_defs = Set.singleton (S.string_of_mlpath p)

let reachable_defs_list (#a:Type) (f:a -> reachable_defs) (l:list a) : reachable_defs =
  List.fold_left (fun defs x -> Set.union defs (f x)) (Set.empty ()) l

let reachable_defs_option (#a:Type) (f:a -> reachable_defs) (o:option a) : reachable_defs =
  match o with
  | None -> empty_defs
  | Some x -> f x

let rec reachable_defs_mlty (t:S.mlty) : reachable_defs =
  let open S in
  match t with
  | MLTY_Var _ -> empty_defs
  | MLTY_Fun (t1, _, t2) -> Set.union (reachable_defs_mlty t1) (reachable_defs_mlty t2)
  | MLTY_Named (tps, p) ->
    Set.union (reachable_defs_list reachable_defs_mlty tps) (singleton p)
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
    Set.union (singleton c) (reachable_defs_list reachable_defs_mlpattern ps)
  | MLP_Branch ps -> reachable_defs_list reachable_defs_mlpattern ps
  | MLP_Record (syms, fs) ->
    Set.union (Set.singleton (String.concat "." syms))
              (reachable_defs_list (fun (_, p) -> reachable_defs_mlpattern p) fs)
  | MLP_Tuple ps -> reachable_defs_list reachable_defs_mlpattern ps

let rec reachable_defs_expr' (e:S.mlexpr') : reachable_defs =
  let open S in
  match e with
  | MLE_Const _
  | MLE_Var _ -> empty_defs
  | MLE_Name p -> singleton p
  | MLE_Let (lb, e) -> Set.union (reachable_defs_mlletbinding lb) (reachable_defs_expr e)
  | MLE_App (e, es) ->
    Set.union (reachable_defs_expr e) (reachable_defs_list reachable_defs_expr es)
  | MLE_TApp (e, ts) ->
    Set.union (reachable_defs_expr e) (reachable_defs_list reachable_defs_mlty ts)
  | MLE_Fun (args, e) ->
    Set.union (reachable_defs_list (fun b -> reachable_defs_mlty b.S.mlbinder_ty) args)
              (reachable_defs_expr e)
  | MLE_Match (e, bs) ->
    Set.union (reachable_defs_expr e)
              (reachable_defs_list reachable_defs_mlbranch bs)
  | MLE_Coerce (e, t1, t2) ->
    Set.union (reachable_defs_expr e)
              (Set.union (reachable_defs_mlty t1) (reachable_defs_mlty t2))
  | MLE_CTor (p, es) ->
    Set.union (singleton p)
               (reachable_defs_list reachable_defs_expr es)
  | MLE_Seq es
  | MLE_Tuple es -> reachable_defs_list reachable_defs_expr es
  | MLE_Record (p, n, fs) ->
    Set.union (Set.singleton (String.concat "." (p@[n])))
              (reachable_defs_list (fun (_, e) -> reachable_defs_expr e) fs)
  | MLE_Proj (e, _) -> reachable_defs_expr e
  | MLE_If (e1, e2, e3_opt) ->
    Set.union (reachable_defs_expr e1)
              (Set.union (reachable_defs_expr e2)
                         (reachable_defs_option reachable_defs_expr e3_opt))
  | MLE_Raise (p, es) ->
    Set.union (singleton p)
              (reachable_defs_list reachable_defs_expr es)
  | MLE_Try (e, bs) -> Set.union (reachable_defs_expr e)
                                 (reachable_defs_list reachable_defs_mlbranch bs)

and reachable_defs_expr (e:S.mlexpr) : reachable_defs =
  Set.union (reachable_defs_expr' e.expr)
            (reachable_defs_mlty e.mlty)

and reachable_defs_mlbranch ((p, wopt, e):S.mlbranch) : reachable_defs =
  Set.union (reachable_defs_mlpattern p)
            (Set.union (reachable_defs_option reachable_defs_expr wopt)
                       (reachable_defs_expr e))

and reachable_defs_mllb (lb:S.mllb) : reachable_defs =
  Set.union (reachable_defs_option reachable_defs_mltyscheme lb.mllb_tysc)
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

let mlmodule1_name (m:S.mlmodule1) : list S.mlsymbol =
  let open S in
  match m.mlmodule1_m with
  | MLM_Ty l -> List.map (fun t -> t.tydecl_name) l
  | MLM_Let (_, lbs) -> List.map (fun lb -> lb.mllb_name) lbs
  | MLM_Exn (s, _) -> [s]
  | MLM_Top _
  | MLM_Loc _ -> []

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
    List.existsb (fun ty_decl ->Set.mem (mname ^ "." ^ ty_decl.tydecl_name) reachable_defs) t
  | MLM_Let (_, lbs) ->
    List.existsb (fun lb -> Set.mem (mname ^ "." ^ lb.mllb_name) reachable_defs) lbs
  | MLM_Exn (p, _) -> false
  | MLM_Top _ -> false
  | MLM_Loc _ -> false

let extract_one
  (g:env)
  (mname:string)
  (gamma:list UEnv.binding)
  (decls:S.mlmodule) : string & env =
  // let (deps, gamma, decls)  : (list string & list UEnv.binding & S.mlmodule) =
  //   match load_value_from_file file with
  //   | Some r -> r
  //   | None -> failwith "Could not load file" in

  // print2 "Loaded file %s with deps: %s\n" file (String.concat "; " deps);  
  let items, env = List.fold_left (fun (items, g) d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    // print1 "Decl deps: %s\n"
    //   (String.concat "\n" (reachable_defs_mlmodule1 d |> Set.elems));
    if not (decl_reachable g.reachable_defs mname d)
    then begin
      // print1 "decl %s is not reachable\n" (String.concat ";" (mlmodule1_name d));
      // if mname = "Pulse.Lib.HashTable.Type"
      // then print1 "decl %s is not reachable\n" (S.mlmodule1_to_string d);
      items, g
    end
    else
    // let _ = print1 "decl %s is reachable\n" (String.concat ";" (mlmodule1_name d)) in
    //
    // NOTE: Rust extraction of discriminators doesn't work for unit variants
    //       (i.e. variants that do not have payloads)
    //       Because we always have a wild card argument to these patterns in discriminator body
    //       In OCaml it works fine.
    //       In Rust it is an error
    //       Should fix it in a better way
    //       For now, just not extracting them ... that too with a hack on names
    //
    match d.S.mlmodule1_m with
    | S.MLM_Let (S.NonRec, [{mllb_name}])
      when starts_with mllb_name "uu___is_" ||
           starts_with mllb_name "__proj__" -> items, g
    | S.MLM_Let lb ->
      let f, g = extract_top_level_lb g lb in
      // print_string "Extracted to:\n";
      // print_string (RustBindings.fn_to_rust f ^ "\n");
      items@[f],
      g
    | S.MLM_Loc _ -> items, g
    | S.MLM_Ty td ->
      let d_items, g = extract_mltydecl g d.S.mlmodule1_attrs td in
      items@d_items, g
    | _ -> fail_nyi (format1 "top level decl %s" (S.mlmodule1_to_string d))
  ) ([], g) decls in
  
  let f = mk_file "a.rs" items in
  let s = RustBindings.file_to_rust f in
  s, env

// let collect_reachable_defs (files:list string) (roots:list string) : reachable_defs =
//   let files = List.filter (fun x -> List.mem x roots) files in
//   reachable_defs_list (fun f ->
//     let (_, _, decls)  : (list string & list UEnv.binding & S.mlmodule) =
//       match load_value_from_file f with
//       | Some r -> r
//       | None -> failwith "Could not load file" in
//     reachable_defs_mlmodule decls) files

let file_to_module_name (f:string) : string =
  let suffix = ".ast" in
  let s = basename f in
  let s = String.substring s 0 (String.length s - String.length suffix) in
  replace_chars s '_' "."

let rec topsort (d:dict) (grey:list string) (black:list string) (root:string)
  : (list string & list string) =  // grey and black
  let grey = root::grey in
  let deps = root |> smap_try_find d |> must |> (fun (deps, _, _) -> deps) in
  let deps = deps |> List.filter (fun f -> List.mem f (smap_keys d) && not (f = root)) in
  if List.existsb (fun d -> List.mem d grey) deps
  then failwith (format1 "cyclic dependency: %s" root);
  let deps = deps |> List.filter (fun f -> not (List.mem f black)) in
  let grey, black = List.fold_left (fun (grey, black) dep ->
    topsort d grey black dep) (grey, black) deps in
  List.filter (fun g -> not (g = root)) grey,
  (if List.mem root black then black else root::black)

let rec topsort_all (d:dict) (black:list string)
  : list string =
  
  if List.for_all (fun f -> List.contains f black) (smap_keys d)
  then black
  else
    let rem = List.filter (fun f -> not (List.contains f black)) (smap_keys d) in
    let root = List.nth rem (List.length rem - 1) in
    let grey, black = topsort d [] black root in
    if List.length grey <> 0
    then failwith "topsort_all: not all files are reachable";
    topsort_all d black

let read_all_ast_files (files:list string) : dict =
  let d = smap_create 100 in
  files |> List.iter (fun f ->
    let contents  : (list string & list UEnv.binding & S.mlmodule) =
      match load_value_from_file f with
      | Some r -> r
      | None -> failwith (format1 "Could not load file %s" f) in
    smap_add d (file_to_module_name f) contents);
  d

let build_decls_dict (d:dict) : smap S.mlmodule1 =
  let dd = smap_create 100 in
  smap_iter d (fun module_nm (_, _, decls) ->
    List.iter (fun (decl:S.mlmodule1) ->
      List.iter (fun decl_nm ->
        smap_add dd (module_nm ^ "." ^ decl_nm) decl
      ) (mlmodule1_name decl)
    ) decls
  );
  dd

let rec collect_reachable_defs_aux
  (dd:smap S.mlmodule1)
  (worklist:reachable_defs)
  (reachable_defs:reachable_defs) =

  if Set.is_empty worklist
  then reachable_defs
  else let hd::_ = Set.elems worklist in
       let worklist = Set.remove hd worklist in
      //  print1 "Adding %s to reachable_defs\n" hd;
       let reachable_defs = Set.add hd reachable_defs in
       let worklist =
         let hd_decl = smap_try_find dd hd in
         match hd_decl with
         | None -> worklist
         | Some hd_decl ->
           let hd_reachable_defs = reachable_defs_mlmodule1 hd_decl in
           hd_reachable_defs |> Set.elems |> List.fold_left (fun worklist def ->
             if Set.mem def reachable_defs ||
                Set.mem def worklist
             then worklist
             else Set.add def worklist
           ) worklist in
       collect_reachable_defs_aux dd worklist reachable_defs

let collect_reachable_defs (d:dict) (root_module:string) : reachable_defs =
  let dd = build_decls_dict d in
  let root_decls = smap_try_find d root_module |> must |> (fun (_, _, decls) -> decls) in
  let worklist = List.fold_left (fun worklist decl ->
    Set.addn
      (decl |> mlmodule1_name |> List.map (fun s -> root_module ^ "." ^ s))
      worklist
  ) empty_defs root_decls in
  collect_reachable_defs_aux dd worklist empty_defs

let rust_file_name (mname:string) =
  let s = replace_char mname '.' '_' |> String.lowercase in
  strcat s ".rs"

let header = "////
////
//// This file is generated by the Pulse2Rust tool
////
////\n"

let extract (files:list string) (odir:string) : unit =
  let d = read_all_ast_files files in
  //
  // reversed order in which decls should be emitted,
  //   i.e., main function first
  //
  let all_modules = topsort_all d [] in
  let root_module::_ = all_modules in
  let reachable_defs = collect_reachable_defs d root_module in
  let g = empty_env d all_modules reachable_defs in
  let _, all_rust_files = List.fold_left (fun (g, all_rust_files) f ->
    let (_, bs, ds) = smap_try_find d f |> must in
    let s, g = extract_one g f bs ds in
    let rust_fname = concat_dir_filename odir (rust_file_name f) in
    let rust_f = open_file_for_writing rust_fname in
    append_to_file rust_f header;
    append_to_file rust_f s;
    close_out_channel rust_f;
    g, rust_fname::all_rust_files
  ) (g, []) all_modules in
  
  print1 "\n\nExtracted: %s\n\n" (String.concat " " all_rust_files)
