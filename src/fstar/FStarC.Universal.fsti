(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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

//Top-level invocations into the universal type-checker FStarC.TypeChecker
module FStarC.Universal

open FStarC.Ident
open FStarC.CheckedFiles
module DsEnv   = FStarC.Syntax.DsEnv
module TcEnv   = FStarC.TypeChecker.Env
module Syntax  = FStarC.Syntax.Syntax
module Dep     = FStarC.Parser.Dep
module ParseIt = FStarC.Parser.ParseIt

type uenv = FStarC.Extraction.ML.UEnv.uenv

(* Takes a module an returns whether it is an interface or not,
and an lid for its name. *)
val module_or_interface_name : Syntax.modul -> bool & lid

(* Uses the dsenv inside the TcEnv.env to run the computation. *)
val with_dsenv_of_tcenv : TcEnv.env -> DsEnv.withenv 'a -> 'a & TcEnv.env

val core_check: TcEnv.core_check_t

type lang_decls_t = list FStarC.Parser.AST.decl

(* Interactive mode: checking a fragment of code. *)
val tc_one_fragment :
    is_interface:bool ->
    option Syntax.modul ->
    TcEnv.env_t ->
    either (FStarC.Parser.ParseIt.input_frag & lang_decls_t) FStarC.Parser.AST.decl ->
    option Syntax.modul & TcEnv.env & lang_decls_t

(* Load an interface file into the dsenv. sed in interactive mode when fly_deps is off *)
val load_interface_decls :
    TcEnv.env ->
    string ->
    TcEnv.env_t

(* Loads one file as a dependence. Used in interactive mode when fly_deps is off *)
val load_file :
    TcEnv.env_t ->
    iface_fn:option string ->
    filename:string ->
    TcEnv.env_t


(* This is used by interactive mode (PushHelper). 
    - initializes the desugaring environment for interleaving, if needed
    - parses the input fragment into a decl
    - interleaves the decl with decls from the interface
    - scans them one by one, loads dependences, and checks them
*)
val load_fly_deps_and_tc_one_fragment :
    filename:string ->
    is_interface:bool ->
    option Syntax.modul ->
    TcEnv.env_t ->
    either (FStarC.Parser.ParseIt.input_frag & lang_decls_t) FStarC.Parser.AST.decl ->
    option Syntax.modul &
    TcEnv.env &
    lang_decls_t &
    list string //filenames that were loaded

(* Initialize a clean environment, built from a dependency graph. The
graph is used to populate the internal dsenv of the tcenv. *)
val init_env : Dep.deps -> TcEnv.env

(* [needs_interleaving s1 s2] is when s1 and s2 are (resp.) the filenames
for the interface and implementation of a (single) module. *)
val needs_interleaving :
    string ->
    string ->
    bool

(* Batch mode: check multiple files. *)
val batch_mode_tc :
    fly_deps:bool ->
    list string ->
    FStarC.Parser.Dep.deps ->
    list tc_result & uenv & (uenv -> uenv)
