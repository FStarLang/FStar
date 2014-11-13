(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"

// (c) Microsoft Corporation. All rights reserved
module Microsoft.FStar.Options
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Getopt

type debug_level_t = 
    | Low
    | Medium
    | High
    | Extreme
    | Other of string

let show_signatures = Util.mk_ref []
let norm_then_print = Util.mk_ref true
let z3_exe = Util.mk_ref (Platform.exe "z3")
let silent=Util.mk_ref false
let debug=Util.mk_ref []
let debug_level = Util.mk_ref Low 
let dlevel = function 
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let debug_level_geq l1 l2 = match l1 with 
    | Other _ 
    | Low -> l1 = l2
    | Medium -> (l2 = Low || l2 = Medium)
    | High -> (l2 = Low || l2 = Medium || l2 = High)
    | Extreme -> (l2 = Low || l2 = Medium || l2 = High || l2 = Extreme)
    
let log_types = Util.mk_ref false
let print_effect_args=Util.mk_ref false
let print_real_names = Util.mk_ref false
let dump_module : ref<option<string>> = Util.mk_ref None
let should_dump l = match !dump_module with 
    | None -> false
    | Some m -> m=l
let logQueries = Util.mk_ref false
let z3exe = Util.mk_ref true
let outputDir = Util.mk_ref (Some ".")
let fstar_home_opt = Util.mk_ref None
let _fstar_home = Util.mk_ref ""
let prims_ref = Util.mk_ref None
let z3timeout = Util.mk_ref 5
let pretype = Util.mk_ref true
let codegen = Util.mk_ref None
let admit_fsi = Util.mk_ref []
let trace_error = Util.mk_ref false
let verify = Util.mk_ref false
let full_context_dependency = Util.mk_ref false
let print_implicits = Util.mk_ref false
let hide_uvar_nums = Util.mk_ref false
let hide_genident_nums = Util.mk_ref false
let serialize_mods = Util.mk_ref false
let initial_fuel = Util.mk_ref 2
let max_fuel = Util.mk_ref 8

let set_fstar_home () = 
  let fh = match !fstar_home_opt with 
    | None ->
      let x = Util.expand_environment_variable "FSTAR_HOME" in
      _fstar_home := x;
      fstar_home_opt := Some x;
      x
    | Some x -> _fstar_home := x; x in
  fh
let get_fstar_home () = match !fstar_home_opt with 
    | None -> ignore <| set_fstar_home(); !_fstar_home
    | Some x -> x

let prims () = match !prims_ref with 
  | None -> (get_fstar_home()) ^ "/lib/prims.fst" 
  | Some x -> x

let prependOutputDir fname = match !outputDir with
  | None -> fname
  | Some x -> x ^ "/" ^ fname

let cache_dir = "cache" 

let display_usage specs =
  Util.print_string "fstar [option] infile...";
  List.iter
    (fun (_, flag, p, doc) ->
       match p with
         | ZeroArgs ig ->
             if doc = "" then Util.print_string (Util.format1 "  --%s\n" flag)
             else Util.print_string (Util.format2 "  --%s  %s\n" flag doc)
         | OneArg (_, argname) ->
             if doc = "" then Util.print_string (Util.format2 "  --%s %s\n" flag argname)
             else Util.print_string (Util.format3 "  --%s %s  %s\n" flag argname doc))
    specs

let specs () : list<Getopt.opt> = 
  let specs =   
    [( noshort, "trace_error", ZeroArgs (fun () -> trace_error := true), "Don't print an error message; show an exception trace instead");
     ( noshort, "codegen", OneArg ((fun s -> codegen := Some s), "OCaml|F#|JS"), "Generate code for execution");
     ( noshort, "pretype", ZeroArgs (fun () -> pretype := true), "Run the pre-type checker");
     ( noshort, "fstar_home", OneArg ((fun x -> fstar_home_opt := Some x), "dir"), "Set the FSTAR_HOME variable to dir");
     ( noshort, "silent", ZeroArgs (fun () -> silent := true), "");
     ( noshort, "prims", OneArg ((fun x -> prims_ref := Some x), "file"), "");
     ( noshort, "prn", ZeroArgs (fun () -> print_real_names := true), "Print real names---you may want to use this in conjunction with logQueries");
     ( noshort, "debug", OneArg ((fun x -> debug := x::!debug), "module name"), "Print LOTS of debugging information while checking module [arg]");
     ( noshort, "debug_level", OneArg ((fun x -> debug_level := dlevel x), "Low|Medium|High|Extreme"), "Control the verbosity of debugging info");
     ( noshort, "log_types", ZeroArgs (fun () -> log_types := true), "Print types computed for data/val/let-bindings");
     ( noshort, "print_effect_args", ZeroArgs (fun () -> print_effect_args := true), "Print inferred predicate transformers for all computation types");
     ( noshort, "dump_module", OneArg ((fun x -> dump_module := Some x), "module name"), "");
     ( noshort, "z3timeout", OneArg ((fun s -> z3timeout := int_of_string s), "t"), "Set the Z3 per-query (soft) timeout to t seconds (default 5)");
     ( noshort, "logQueries", ZeroArgs (fun () -> logQueries := true), "Log the Z3 queries in queries.smt2");
     ( noshort, "admit_fsi", OneArg ((fun x -> admit_fsi := x::!admit_fsi), "module name"), "Treat .fsi as a .fst");
     ( noshort, "odir", OneArg ((fun x -> outputDir := Some x), "dir"), "Place output in directory dir");
     ( noshort, "verify", ZeroArgs (fun () -> verify := true), "Call the SMT solver to discharge verifications conditions");
     ( noshort, "z3exe", OneArg ((fun x -> z3_exe := x), "path"), "Path to the Z3 SMT solver");
     ( noshort, "print_before_norm", ZeroArgs(fun () -> norm_then_print := false), "Do not normalize types before printing (for debugging)");
     ( noshort, "show_signatures", OneArg((fun x -> show_signatures := x::!show_signatures), "module name"), "Show the checked signatures for all top-level symbols in the module");
     ( noshort, "full_context_dependency", ZeroArgs(fun () -> full_context_dependency := true), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference)");
     ( noshort, "print_implicits", ZeroArgs(fun () -> print_implicits := true), "Print implicit arguments");
     ( noshort, "hide_uvar_nums", ZeroArgs(fun () -> hide_uvar_nums := true), "Don't print unification variable numbers");
     ( noshort, "hide_genident_nums", ZeroArgs(fun () -> hide_genident_nums := true), "Don't print generated identifier numbers");
     ( noshort, "serialize_mods", ZeroArgs (fun () -> serialize_mods := true), "Serialize compiled modules");
     ( noshort, "initial_fuel", OneArg((fun x -> initial_fuel := int_of_string x), "non-negative integer"), "Number of unrolling of recursive functions to try initially (default 2)");
     ( noshort, "max_fuel", OneArg((fun x -> max_fuel := int_of_string x), "non-negative integer"), "Number of unrolling of recursive functions to try at most (default 8)");
    ] in 
     ( 'h', "help", ZeroArgs (fun x -> display_usage specs; exit 0), "Display this information")::specs
