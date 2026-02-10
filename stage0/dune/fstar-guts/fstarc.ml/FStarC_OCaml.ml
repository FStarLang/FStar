open Prims
let shellescape (s : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_String.list_of_string s in
    FStarC_List.map
      (fun uu___2 ->
         match uu___2 with
         | 39 -> "'\"'\"'"
         | c -> FStarC_String.make Prims.int_one c) uu___1 in
  FStarC_String.concat "" uu___
let new_ocamlpath (uu___ : unit) : Prims.string=
  let ocamldir = FStarC_Find.locate_ocaml () in
  let old_ocamlpath =
    let uu___1 = FStarC_Util.expand_environment_variable "OCAMLPATH" in
    FStarC_Option.dflt "" uu___1 in
  let new_ocamlpath1 =
    Prims.strcat ocamldir
      (Prims.strcat FStarC_Platform.ocamlpath_sep old_ocamlpath) in
  new_ocamlpath1
let exec_in_ocamlenv (cmd : Prims.string) (args : Prims.string Prims.list) :
  'a=
  let new_ocamlpath1 = new_ocamlpath () in
  FStarC_Util.putenv "OCAMLPATH" new_ocamlpath1;
  (let pid = FStarC_Util.create_process cmd (cmd :: args) in
   let rc = FStarC_Util.waitpid pid in
   match rc with
   | FStar_Pervasives.Inl rc1 -> FStarC_Effect.exit rc1
   | FStar_Pervasives.Inr uu___1 -> FStarC_Effect.exit Prims.int_one)
let app_lib : Prims.string= "fstar.lib"
let plugin_lib : Prims.string= "fstar.pluginlib"
let wstr : Prims.string= "-8"
let common_args : Prims.string Prims.list= ["-w"; wstr; "-thread"]
let exec_ocamlc (args : Prims.string Prims.list) : 'a=
  exec_in_ocamlenv "ocamlfind"
    (FStar_List_Tot_Base.op_At ("c" :: common_args) ("-linkpkg" :: "-package"
       :: app_lib :: args))
let exec_ocamlopt (args : Prims.string Prims.list) : 'a=
  exec_in_ocamlenv "ocamlfind"
    (FStar_List_Tot_Base.op_At ("opt" :: common_args) ("-linkpkg" ::
       "-package" :: app_lib :: args))
let exec_ocamlopt_plugin (args : Prims.string Prims.list) : 'a=
  exec_in_ocamlenv "ocamlfind"
    (FStar_List_Tot_Base.op_At ("opt" :: common_args) ("-shared" ::
       "-package" :: plugin_lib :: args))
