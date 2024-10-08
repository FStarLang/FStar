open Prims
let (loaded : Prims.string Prims.list FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref []
let (pout : Prims.string -> unit) =
  fun s ->
    let uu___ = FStar_Compiler_Debug.any () in
    if uu___ then FStar_Compiler_Util.print_string s else ()
let (pout1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu___ = FStar_Compiler_Debug.any () in
      if uu___ then FStar_Compiler_Util.print1 s x else ()
let (perr : Prims.string -> unit) =
  fun s ->
    let uu___ = FStar_Compiler_Debug.any () in
    if uu___ then FStar_Compiler_Util.print_error s else ()
let (perr1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu___ = FStar_Compiler_Debug.any () in
      if uu___ then FStar_Compiler_Util.print1_error s x else ()
let (dynlink : Prims.string -> unit) =
  fun fname ->
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang loaded in
      FStar_Compiler_List.mem fname uu___1 in
    if uu___
    then pout1 "Plugin %s already loaded, skipping\n" fname
    else
      (pout (Prims.strcat "Attempting to load " (Prims.strcat fname "\n"));
       (try
          (fun uu___4 ->
             match () with
             | () -> FStar_Compiler_Plugins_Base.dynlink_loadfile fname) ()
        with
        | FStar_Compiler_Plugins_Base.DynlinkError e ->
            ((let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_Compiler_Util.format1
                      "Failed to load plugin file %s" fname in
                  FStar_Errors_Msg.text uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 = FStar_Errors_Msg.text "Reason:" in
                    let uu___11 = FStar_Errors_Msg.text e in
                    FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___10 uu___11 in
                  let uu___10 =
                    let uu___11 =
                      let uu___12 =
                        let uu___13 =
                          let uu___14 =
                            FStar_Errors.errno
                              FStar_Errors_Codes.Error_PluginDynlink in
                          FStar_Class_Show.show
                            (FStar_Class_Show.printableshow
                               FStar_Class_Printable.printable_int) uu___14 in
                        FStar_Compiler_Util.format1
                          "Remove the `--load` option or use `--warn_error -%s` to ignore and continue."
                          uu___13 in
                      FStar_Errors_Msg.text uu___12 in
                    [uu___11] in
                  uu___9 :: uu___10 in
                uu___7 :: uu___8 in
              FStar_Errors.log_issue0 FStar_Errors_Codes.Error_PluginDynlink
                () (Obj.magic FStar_Errors_Msg.is_error_message_list_doc)
                (Obj.magic uu___6));
             FStar_Errors.stop_if_err ()));
       (let uu___5 =
          let uu___6 = FStar_Compiler_Effect.op_Bang loaded in fname ::
            uu___6 in
        FStar_Compiler_Effect.op_Colon_Equals loaded uu___5);
       pout1 "Loaded %s\n" fname)
let (load_plugin : Prims.string -> unit) = fun tac -> dynlink tac
let (load_plugins : Prims.string Prims.list -> unit) =
  fun tacs -> FStar_Compiler_List.iter load_plugin tacs
let (load_plugins_dir : Prims.string -> unit) =
  fun dir ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Compiler_Util.readdir dir in
        FStar_Compiler_List.filter
          (fun s ->
             ((FStar_Compiler_String.length s) >= (Prims.of_int (5))) &&
               ((FStar_String.sub s
                   ((FStar_Compiler_String.length s) - (Prims.of_int (5)))
                   (Prims.of_int (5)))
                  = ".cmxs")) uu___2 in
      FStar_Compiler_List.map
        (fun s -> Prims.strcat dir (Prims.strcat "/" s)) uu___1 in
    load_plugins uu___
let (compile_modules : Prims.string -> Prims.string Prims.list -> unit) =
  fun dir ->
    fun ms ->
      let compile m =
        let packages = ["fstar.lib"] in
        let pkg pname = Prims.strcat "-package " pname in
        let args =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Compiler_List.map pkg packages in
                FStar_List_Tot_Base.append uu___3
                  ["-o"; Prims.strcat m ".cmxs"; Prims.strcat m ".ml"] in
              FStar_List_Tot_Base.append ["-w"; "-8-11-20-21-26-28"] uu___2 in
            FStar_List_Tot_Base.append ["-I"; dir] uu___1 in
          FStar_List_Tot_Base.append ["ocamlopt"; "-shared"] uu___ in
        let ocamlpath_sep =
          match FStar_Platform.system with
          | FStar_Platform.Windows -> ";"
          | FStar_Platform.Posix -> ":" in
        let old_ocamlpath =
          let uu___ =
            FStar_Compiler_Util.expand_environment_variable "OCAMLPATH" in
          match uu___ with
          | FStar_Pervasives_Native.Some s -> s
          | FStar_Pervasives_Native.None -> "" in
        let env_setter =
          FStar_Compiler_Util.format5 "env OCAMLPATH=\"%s/../lib/%s%s/%s%s\""
            FStar_Options.fstar_bin_directory ocamlpath_sep
            FStar_Options.fstar_bin_directory ocamlpath_sep old_ocamlpath in
        let cmd =
          FStar_Compiler_String.concat " " (env_setter :: "ocamlfind" ::
            args) in
        let rc = FStar_Compiler_Util.system_run cmd in
        if rc <> Prims.int_zero
        then
          let uu___ =
            let uu___1 =
              FStar_Errors_Msg.text "Failed to compile native tactic." in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStar_Class_Show.show
                      (FStar_Class_Show.printableshow
                         FStar_Class_Printable.printable_int) rc in
                  FStar_Compiler_Util.format2
                    "Command\n`%s`\nreturned with exit code %s" cmd uu___5 in
                FStar_Errors_Msg.text uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Errors.raise_error0
            FStar_Errors_Codes.Fatal_FailToCompileNativeTactic ()
            (Obj.magic FStar_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___)
        else () in
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 =
                 FStar_Compiler_List.map
                   (fun m -> Prims.strcat dir (Prims.strcat "/" m)) ms in
               FStar_Compiler_List.iter compile uu___1) ()
      with
      | uu___ ->
          ((let uu___2 =
              let uu___3 = FStar_Compiler_Util.print_exn uu___ in
              FStar_Compiler_Util.format1
                "Failed to load native tactic: %s\n" uu___3 in
            perr uu___2);
           FStar_Compiler_Effect.raise uu___)
let (autoload_plugin : Prims.string -> Prims.bool) =
  fun ext ->
    let uu___ =
      let uu___1 = FStar_Options_Ext.get "noautoload" in uu___1 <> "" in
    if uu___
    then false
    else
      ((let uu___3 = FStar_Compiler_Debug.any () in
        if uu___3
        then
          FStar_Compiler_Util.print1
            "Trying to find a plugin for extension %s\n" ext
        else ());
       (let uu___3 = FStar_Options.find_file (Prims.strcat ext ".cmxs") in
        match uu___3 with
        | FStar_Pervasives_Native.Some fn ->
            let uu___4 =
              let uu___5 = FStar_Compiler_Effect.op_Bang loaded in
              FStar_Compiler_List.mem fn uu___5 in
            if uu___4
            then false
            else
              ((let uu___7 = FStar_Compiler_Debug.any () in
                if uu___7
                then
                  FStar_Compiler_Util.print1 "Autoloading plugin %s ...\n" fn
                else ());
               load_plugin fn;
               true)
        | FStar_Pervasives_Native.None -> false))