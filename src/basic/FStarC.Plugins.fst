(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Plugins

open FStarC
open FStarC
open FStarC.Effect
open FStarC.Plugins.Base

module BU = FStarC.Util
module E   = FStarC.Errors
open FStarC.Class.Show

let loaded : ref (list string) = mk_ref []
let loaded_plugin_lib : ref bool = mk_ref false

let pout  s   = if Debug.any () then Format.print_string s
let pout1 s x = if Debug.any () then Format.print1 s x
let perr  s   = if Debug.any () then Format.print_error s
let perr1 s x = if Debug.any () then Format.print1_error s x

let do_dynlink (fname:string) : unit =
  try
    dynlink_loadfile fname
  with DynlinkError e ->
    E.log_issue0 E.Error_PluginDynlink [
      E.text (Format.fmt1 "Failed to load plugin file %s" fname);
      Pprint.prefix 2 1 (E.text "Reason:") (E.text e);
      E.text (Format.fmt1 "Remove the `--load` option or use `--warn_error -%s` to ignore and continue."
                (show (E.errno E.Error_PluginDynlink)))
    ];
    (* If we weren't ignoring this error, just stop now *)
    E.stop_if_err ()

let dynlink (fname:string) : unit =
  if List.mem fname !loaded then (
    pout1 "Plugin %s already loaded, skipping\n" fname
  ) else (
    pout ("Attempting to load " ^ fname ^ "\n");
    do_dynlink fname;
    loaded := fname :: !loaded;
    pout1 "Loaded %s\n" fname;
    ()
  )

let load_plugin tac =
  if not (!loaded_plugin_lib) then (
    pout "Loading fstar.pluginlib before first plugin\n";
    do_dynlink (Filepath.normalize_file_path <| BU.get_exec_dir () ^ "/../lib/fstar/pluginlib/fstar_pluginlib.cmxs");
    pout "Loaded fstar.pluginlib OK\n";
    loaded_plugin_lib := true
  );
  dynlink tac

let load_plugins tacs =
  List.iter load_plugin tacs

let load_plugins_dir dir =
  (* Dynlink all .cmxs files in the given directory *)
  (* fixme: confusion between FStarC.String and FStar.String *)
  Filepath.readdir dir
  |> List.filter (fun s -> String.length s >= 5 && FStar.String.sub s (String.length s - 5) 5 = ".cmxs")
  |> List.map (fun s -> dir ^ "/" ^ s)
  |> load_plugins

let compile_modules dir ms =
   let compile m =
     let packages = [ "fstar.pluginlib" ] in
     let pkg pname = "-package " ^ pname in
     let args = ["ocamlopt"; "-shared"] (* FIXME shell injection *)
                @ ["-I"; dir]
                @ ["-w"; "-8-11-20-21-26-28" ]
                @ (List.map pkg packages)
                @ ["-o"; m ^ ".cmxs"; m ^ ".ml"] in
     (* Note: not useful when in an OPAM setting *)
     let old_ocamlpath =
       match BU.expand_environment_variable "OCAMLPATH" with
       | Some s -> s
       | None -> ""
     in
     let env_setter = Format.fmt3 "env OCAMLPATH=\"%s%s%s\""
       (Find.locate_ocaml ())
       Platform.ocamlpath_sep
      //  Options.fstar_bin_directory // needed?
      //  ocamlpath_sep
       old_ocamlpath
     in
     let cmd = String.concat " " (env_setter :: "ocamlfind" :: args) in
     let rc = BU.system_run cmd in
     if rc <> 0
     then E.raise_error0 E.Fatal_FailToCompileNativeTactic [
            E.text "Failed to compile native tactic.";
            E.text (Format.fmt2 "Command\n`%s`\nreturned with exit code %s"
                                  cmd (show rc))
          ]
     else ()
   in
   try
     ms
      |> List.map (fun m -> dir ^ "/" ^ m)
      |> List.iter compile
   with e ->
     perr (Format.fmt1 "Failed to load native tactic: %s\n" (Util.print_exn e));
     raise e

(* Tries to load a plugin named like the extension. Returns true
if it could find a plugin with the proper name. This will fail hard
if loading the plugin fails. *)
let autoload_plugin (ext:string) : bool =
  if Options.Ext.enabled "noautoload" then false else (
  if Debug.any () then
    Format.print1 "Trying to find a plugin for extension %s\n" ext;
  match Find.find_file (ext ^ ".cmxs") with
  | Some fn ->
    if List.mem fn !loaded then false
    else (
    if Debug.any () then
      Format.print1 "Autoloading plugin %s ...\n" fn;
    load_plugin fn;
    true
    )
  | None ->
    false
)
