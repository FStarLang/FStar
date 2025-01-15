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

open FStar open FStarC
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

(* Initialize a clean environment, built from a dependency graph. The
graph is used to populate the internal dsenv of the tcenv. *)
val init_env : Dep.deps -> TcEnv.env

val core_check: TcEnv.core_check_t

type lang_decls_t = list FStarC.Parser.AST.decl

(* Interactive mode: checking a fragment of code. *)
val tc_one_fragment :
    option Syntax.modul ->
    TcEnv.env_t ->
    either (FStarC.Parser.ParseIt.input_frag & lang_decls_t) FStarC.Parser.AST.decl ->
    option Syntax.modul & TcEnv.env & lang_decls_t

(* Load an interface file into the dsenv. *)
val load_interface_decls :
    TcEnv.env ->
    string ->
    TcEnv.env_t

(* Batch mode: check one file. *)
val tc_one_file :
    uenv ->
    option string ->
    string ->
    FStarC.Parser.Dep.parsing_data ->
    tc_result & option FStarC.Extraction.ML.Syntax.mllib & uenv

(* A thin wrapper for tc_one_file, called by the interactive mode.
Basically discards any information about extraction. *)
val tc_one_file_for_ide :
    TcEnv.env_t ->
    option string ->
    string ->
    FStarC.Parser.Dep.parsing_data ->
    tc_result & TcEnv.env_t

(* [needs_interleaving s1 s2] is when s1 and s2 are (resp.) the filenames
for the interface and implementation of a (single) module. *)
val needs_interleaving :
    string ->
    string ->
    bool

(* Batch mode: check multiple files. *)
val batch_mode_tc :
    list string ->
    FStarC.Parser.Dep.deps ->
    list tc_result & uenv & (uenv -> uenv)
