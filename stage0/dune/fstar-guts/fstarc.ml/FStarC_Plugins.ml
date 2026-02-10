open Prims
let loaded : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let loaded_plugin_lib : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
let pout (s : Prims.string) : unit=
  let uu___ = FStarC_Debug.any () in
  if uu___ then FStarC_Format.print_string s else ()
let pout1 (s : Prims.string) (x : Prims.string) : unit=
  let uu___ = FStarC_Debug.any () in
  if uu___ then FStarC_Format.print1 s x else ()
let perr (s : Prims.string) : unit=
  let uu___ = FStarC_Debug.any () in
  if uu___ then FStarC_Format.print_error s else ()
let perr1 (s : Prims.string) (x : Prims.string) : unit=
  let uu___ = FStarC_Debug.any () in
  if uu___ then FStarC_Format.print1_error s x else ()
let do_dynlink (fname : Prims.string) : unit=
  try
    (fun uu___ ->
       match () with | () -> FStarC_Plugins_Base.dynlink_loadfile fname) ()
  with
  | FStarC_Plugins_Base.DynlinkError e ->
      ((let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Format.fmt1 "Failed to load plugin file %s" fname in
            FStarC_Errors_Msg.text uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 = FStarC_Errors_Msg.text "Reason:" in
              let uu___7 = FStarC_Errors_Msg.text e in
              FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___6
                uu___7 in
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      FStarC_Errors.errno
                        FStarC_Errors_Codes.Error_PluginDynlink in
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      uu___10 in
                  FStarC_Format.fmt1
                    "Remove the `--load` option or use `--warn_error -%s` to ignore and continue."
                    uu___9 in
                FStarC_Errors_Msg.text uu___8 in
              [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        FStarC_Errors.log_issue0 FStarC_Errors_Codes.Error_PluginDynlink ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___2));
       FStarC_Errors.stop_if_err ())
let dynlink (fname : Prims.string) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang loaded in FStarC_List.mem fname uu___1 in
  if uu___
  then pout1 "Plugin %s already loaded, skipping\n" fname
  else
    (pout (Prims.strcat "Attempting to load " (Prims.strcat fname "\n"));
     do_dynlink fname;
     (let uu___5 =
        let uu___6 = FStarC_Effect.op_Bang loaded in fname :: uu___6 in
      FStarC_Effect.op_Colon_Equals loaded uu___5);
     pout1 "Loaded %s\n" fname)
let load_plugin (tac : Prims.string) : unit=
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang loaded_plugin_lib in
     Prims.op_Negation uu___2 in
   if uu___1
   then
     (pout "Loading fstar.pluginlib before first plugin\n";
      (let uu___4 =
         let uu___5 =
           let uu___6 = FStarC_Util.get_exec_dir () in
           Prims.strcat uu___6 "/../lib/fstar/pluginlib/fstar_pluginlib.cmxs" in
         FStarC_Filepath.normalize_file_path uu___5 in
       do_dynlink uu___4);
      pout "Loaded fstar.pluginlib OK\n";
      FStarC_Effect.op_Colon_Equals loaded_plugin_lib true)
   else ());
  dynlink tac
let load_plugins (tacs : Prims.string Prims.list) : unit=
  FStarC_List.iter load_plugin tacs
let load_plugins_dir (dir : Prims.string) : unit=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Filepath.readdir dir in
      FStarC_List.filter
        (fun s ->
           ((FStarC_String.length s) >= (Prims.of_int (5))) &&
             ((FStar_String.sub s
                 ((FStarC_String.length s) - (Prims.of_int (5)))
                 (Prims.of_int (5)))
                = ".cmxs")) uu___2 in
    FStarC_List.map (fun s -> Prims.strcat dir (Prims.strcat "/" s)) uu___1 in
  load_plugins uu___
let compile_modules (dir : Prims.string) (ms : Prims.string Prims.list) :
  unit=
  let compile m =
    let packages = ["fstar.pluginlib"] in
    let pkg pname = Prims.strcat "-package " pname in
    let args =
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_List.map pkg packages in
            FStar_List_Tot_Base.append uu___3
              ["-o"; Prims.strcat m ".cmxs"; Prims.strcat m ".ml"] in
          FStar_List_Tot_Base.append ["-w"; "-8-11-20-21-26-28"] uu___2 in
        FStar_List_Tot_Base.append ["-I"; dir] uu___1 in
      FStar_List_Tot_Base.append ["ocamlopt"; "-shared"] uu___ in
    let old_ocamlpath =
      let uu___ = FStarC_Util.expand_environment_variable "OCAMLPATH" in
      match uu___ with
      | FStar_Pervasives_Native.Some s -> s
      | FStar_Pervasives_Native.None -> "" in
    let env_setter =
      let uu___ = FStarC_Find.locate_ocaml () in
      FStarC_Format.fmt3 "env OCAMLPATH=\"%s%s%s\"" uu___
        FStarC_Platform.ocamlpath_sep old_ocamlpath in
    let cmd = FStarC_String.concat " " (env_setter :: "ocamlfind" :: args) in
    let rc = FStarC_Util.system_run cmd in
    if rc <> Prims.int_zero
    then
      let uu___ =
        let uu___1 =
          FStarC_Errors_Msg.text "Failed to compile native tactic." in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int rc in
              FStarC_Format.fmt2 "Command\n`%s`\nreturned with exit code %s"
                cmd uu___5 in
            FStarC_Errors_Msg.text uu___4 in
          [uu___3] in
        uu___1 :: uu___2 in
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___)
    else () in
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 =
             FStarC_List.map (fun m -> Prims.strcat dir (Prims.strcat "/" m))
               ms in
           FStarC_List.iter compile uu___1) ()
  with
  | uu___ ->
      ((let uu___2 =
          let uu___3 = FStarC_Util.print_exn uu___ in
          FStarC_Format.fmt1 "Failed to load native tactic: %s\n" uu___3 in
        perr uu___2);
       FStarC_Effect.raise uu___)
let autoload_plugin (ext : Prims.string) : Prims.bool=
  let uu___ = FStarC_Options_Ext.enabled "noautoload" in
  if uu___
  then false
  else
    ((let uu___3 = FStarC_Debug.any () in
      if uu___3
      then
        FStarC_Format.print1 "Trying to find a plugin for extension %s\n" ext
      else ());
     (let uu___3 = FStarC_Find.find_file (Prims.strcat ext ".cmxs") in
      match uu___3 with
      | FStar_Pervasives_Native.Some fn ->
          let uu___4 =
            let uu___5 = FStarC_Effect.op_Bang loaded in
            FStarC_List.mem fn uu___5 in
          if uu___4
          then false
          else
            ((let uu___7 = FStarC_Debug.any () in
              if uu___7
              then FStarC_Format.print1 "Autoloading plugin %s ...\n" fn
              else ());
             load_plugin fn;
             true)
      | FStar_Pervasives_Native.None -> false))
