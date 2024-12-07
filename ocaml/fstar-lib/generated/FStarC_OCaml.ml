open Prims
let (shellescape : Prims.string -> Prims.string) =
  fun s ->
    let uu___ =
      let uu___1 = FStarC_Compiler_String.list_of_string s in
      FStarC_Compiler_List.map
        (fun uu___2 ->
           match uu___2 with
           | 39 -> "'\"'\"'"
           | c -> FStarC_Compiler_String.make Prims.int_one c) uu___1 in
    FStarC_Compiler_String.concat "" uu___
let (new_ocamlpath : unit -> Prims.string) =
  fun uu___ ->
    let ocamldir = FStarC_Find.locate_ocaml () in
    let sep =
      match FStarC_Platform.system with
      | FStarC_Platform.Windows -> ";"
      | FStarC_Platform.Posix -> ":" in
    let old_ocamlpath =
      let uu___1 =
        FStarC_Compiler_Util.expand_environment_variable "OCAMLPATH" in
      FStarC_Compiler_Util.dflt "" uu___1 in
    let new_ocamlpath1 =
      Prims.strcat ocamldir (Prims.strcat sep old_ocamlpath) in
    new_ocamlpath1
let exec_in_ocamlenv : 'a . Prims.string -> Prims.string Prims.list -> 'a =
  fun cmd ->
    fun args ->
      let new_ocamlpath1 = new_ocamlpath () in
      FStarC_Compiler_Util.putenv "OCAMLPATH" new_ocamlpath1;
      (let pid = FStarC_Compiler_Util.create_process cmd (cmd :: args) in
       let rc = FStarC_Compiler_Util.waitpid pid in
       match rc with
       | FStar_Pervasives.Inl rc1 -> FStarC_Compiler_Effect.exit rc1
       | FStar_Pervasives.Inr uu___1 ->
           FStarC_Compiler_Effect.exit Prims.int_one)
let (app_lib : Prims.string) = "fstar.lib"
let (plugin_lib : Prims.string) = "fstar.lib"
let (wstr : Prims.string) = "-8"
let (common_args : Prims.string Prims.list) = ["-w"; wstr; "-thread"]
let exec_ocamlc : 'a . Prims.string Prims.list -> 'a =
  fun args ->
    exec_in_ocamlenv "ocamlfind"
      (FStar_List_Tot_Base.op_At ("c" :: common_args) ("-linkpkg" ::
         "-package" :: app_lib :: args))
let exec_ocamlopt : 'a . Prims.string Prims.list -> 'a =
  fun args ->
    exec_in_ocamlenv "ocamlfind"
      (FStar_List_Tot_Base.op_At ("opt" :: common_args) ("-linkpkg" ::
         "-package" :: app_lib :: args))
let exec_ocamlopt_plugin : 'a . Prims.string Prims.list -> 'a =
  fun args ->
    exec_in_ocamlenv "ocamlfind"
      (FStar_List_Tot_Base.op_At ("opt" :: common_args) ("-shared" ::
         "-package" :: plugin_lib :: args))