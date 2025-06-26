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

open FStarC
open FStarC.Util
open FStarC.List
open FStarC.Effect

open Pulse2Rust.Deps
open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env
open Pulse2Rust.Extract

open RustBindings

open FStarC.Class.Setlike

module S = FStarC.Extraction.ML.Syntax

module UEnv = FStarC.Extraction.ML.UEnv

let mlmodule1_name (m:S.mlmodule1) : list S.mlsymbol =
  let open S in
  match m.mlmodule1_m with
  | MLM_Ty l -> List.map (fun t -> t.tydecl_name) l
  | MLM_Let (_, lbs) -> List.map (fun lb -> lb.mllb_name) lbs
  | MLM_Exn (s, _) -> [s]
  | MLM_Top _
  | MLM_Loc _ -> []


let extract_one
  (g:env)
  (mname:string)
  (gamma:list UEnv.mlbinding)
  (decls:S.mlmodulebody) : string & env =
  // let (deps, gamma, decls)  : (list string & list UEnv.mlbinding & S.mlmodule) =
  //   match load_value_from_file file with
  //   | Some r -> r
  //   | None -> failwith "Could not load file" in

  // print2 "Loaded file %s with deps: %s\n" file (String.concat "; " deps);  
  let items, env = List.fold_left (fun (items, g) d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    // print1 "Decl deps: %s\n"
    //   (String.concat "\n" (reachable_defs_mlmodule1 d |> elems));
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

let file_to_module_name (f:string) : string =
  let suffix = ".ast" in
  let s = Filepath.basename f in
  let s = String.substring s 0 (String.length s - String.length suffix) in
  replace_chars s '_' "."

let read_all_ast_files (files:list string) : dict =
  let d = SMap.create 100 in
  files |> List.iter (fun f ->
    let contents  : (list string & list UEnv.mlbinding & S.mlmodulebody) =
      match load_value_from_file f with
      | Some r -> r
      | None -> failwith (format1 "Could not load file %s" f) in
    SMap.add d (file_to_module_name f) contents);
  d

let build_decls_dict (d:dict) : SMap.t S.mlmodule1 =
  let dd = SMap.create 100 in
  SMap.iter d (fun module_nm (_, _, decls) ->
    List.iter (fun (decl:S.mlmodule1) ->
      List.iter (fun decl_nm ->
        SMap.add dd (module_nm ^ "." ^ decl_nm) decl
      ) (mlmodule1_name decl)
    ) decls
  );
  dd

let rec collect_reachable_defs_aux
  (dd:SMap.t S.mlmodule1)
  (worklist:reachable_defs)
  (reachable_defs:reachable_defs) =

  if is_empty worklist
  then reachable_defs
  else let hd::_ = elems worklist in
       let worklist = remove hd worklist in
      //  print1 "Adding %s to reachable_defs\n" hd;
       let reachable_defs = add hd reachable_defs in
       let worklist =
         let hd_decl = SMap.try_find dd hd in
         match hd_decl with
         | None -> worklist
         | Some hd_decl ->
           let hd_reachable_defs = reachable_defs_mlmodule1 hd_decl in
           hd_reachable_defs |> elems |> List.fold_left (fun worklist def ->
             if mem def reachable_defs ||
                mem def worklist
             then worklist
             else add def worklist
           ) worklist in
       collect_reachable_defs_aux dd worklist reachable_defs

let collect_reachable_defs (d:dict) (root_module:string) : reachable_defs =
  let dd = build_decls_dict d in
  let root_decls = SMap.try_find d root_module |> must |> (fun (_, _, decls) -> decls) in
  let worklist = List.fold_left (fun worklist decl ->
    addn
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

let extract (files:list string) (odir:string) (libs:string) : unit =
  let d = read_all_ast_files files in
  //
  // reversed order in which decls should be emitted,
  //   i.e., main function first
  //
  let all_modules = topsort_all d [] in
  // print1 "all_modules: %s\n" (String.concat " " all_modules);
  let root_module = file_to_module_name (let root_file::_ = files in root_file) in
  // print1 "root_module: %s\n" root_module;
  let reachable_defs = collect_reachable_defs d root_module in
  let external_libs = FStarC.Util.split libs "," |> List.map trim_string in
  let g = empty_env external_libs d all_modules reachable_defs in
  let _, all_rust_files = List.fold_left (fun (g, all_rust_files) f ->
    // print1 "Extracting file: %s\n" f;
    let (_, bs, ds) = SMap.try_find d f |> must in
    let s, g = extract_one g f bs ds in
    let rust_fname = concat_dir_filename odir (rust_file_name f) in
    let rust_f = open_file_for_writing rust_fname in
    append_to_file rust_f header;
    append_to_file rust_f s;
    close_out_channel rust_f;
    g, rust_fname::all_rust_files
  ) (g, []) all_modules in
  
  print1 "\n\nExtracted: %s\n\n" (String.concat " " all_rust_files)
