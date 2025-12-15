open Prims
let z3url : Prims.string= "https://github.com/Z3Prover/z3/releases"
let packaged_z3_versions : Prims.string Prims.list=
  ["4.8.5"; "4.13.3"; "4.15.3"]
let z3_install_suggestion (v : Prims.string) :
  FStar_Pprint.document Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStarC_Format.fmt1 "Please download version %s of Z3 from" v in
        FStarC_Errors_Msg.text uu___3 in
      FStar_Pprint.prefix (Prims.of_int (4)) Prims.int_one uu___2
        (FStar_Pprint.url z3url) in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          FStarC_Errors_Msg.text "and install it into your $PATH as" in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 = FStarC_Platform.exe (Prims.strcat "z3-" v) in
              FStar_Pprint.doc_of_string uu___8 in
            FStar_Pprint.squotes uu___7 in
          FStar_Pprint.op_Hat_Hat uu___6 FStar_Pprint.dot in
        FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
      FStar_Pprint.group uu___3 in
    FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
  let uu___1 =
    let uu___2 =
      if FStarC_List.mem v packaged_z3_versions
      then
        let uu___3 =
          FStarC_Format.fmt1
            "Version %s of Z3 should be included in binary packages of F*. If you are using a binary package and are seeing\n              this error, please file a bug report."
            v in
        FStarC_Errors_Msg.text uu___3
      else FStar_Pprint.empty in
    [uu___2] in
  uu___ :: uu___1
let z3_inpath (path : Prims.string) : Prims.bool=
  try
    (fun uu___ ->
       match () with
       | () ->
           let s =
             FStarC_Util.run_process "z3_pathtest" path ["-version"]
               FStar_Pervasives_Native.None in
           s <> "") ()
  with | uu___ -> false
let do_locate_z3 (v : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let guard b =
    if b
    then FStar_Pervasives_Native.Some ()
    else FStar_Pervasives_Native.None in
  let op_Less_Bar_Greater o1 o2 uu___ =
    let uu___1 = o1 () in
    match uu___1 with
    | FStar_Pervasives_Native.Some v1 -> FStar_Pervasives_Native.Some v1
    | FStar_Pervasives_Native.None -> o2 () in
  let path =
    let in_lib uu___ =
      (fun uu___ ->
         let uu___1 = FStarC_Find.lib_root () in
         Obj.magic
           (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option ()
              () (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun root ->
                    let root = Obj.magic root in
                    let path1 =
                      FStarC_Platform.exe
                        (Prims.strcat root
                           (Prims.strcat "/z3-" (Prims.strcat v "/bin/z3"))) in
                    let path2 = FStarC_Filepath.normalize_file_path path1 in
                    let uu___2 = guard (FStarC_Filepath.file_exists path2) in
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang
                         FStarC_Class_Monad.monad_option () () uu___2
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___3 = Obj.magic uu___3 in
                               Obj.magic (FStar_Pervasives_Native.Some path2))
                              uu___3))) uu___2))) uu___ in
    let from_path uu___1 uu___ =
      (fun cmd uu___ ->
         let cmd1 = FStarC_Platform.exe cmd in
         let uu___1 = let uu___2 = z3_inpath cmd1 in guard uu___2 in
         Obj.magic
           (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option ()
              () uu___1
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Pervasives_Native.Some cmd1)) uu___2)))
        uu___1 uu___ in
    op_Less_Bar_Greater
      (op_Less_Bar_Greater
         (op_Less_Bar_Greater (op_Less_Bar_Greater FStarC_Options.smt in_lib)
            (from_path (Prims.strcat "z3-" v))) (from_path "z3"))
      (fun uu___ -> FStar_Pervasives_Native.None) () in
  (let uu___1 = FStarC_Debug.any () in
   if uu___1
   then
     let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_string v in
     let uu___3 =
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_option FStarC_Class_Show.showable_string)
         path in
     FStarC_Format.print2 "do_locate_z3(%s) = %s\n" uu___2 uu___3
   else ());
  path
let locate_z3 : Prims.string -> Prims.string FStar_Pervasives_Native.option=
  let cache = FStarC_SMap.create (Prims.of_int (5)) in
  fun v ->
    let find_or k f =
      let uu___ = FStarC_SMap.try_find cache k in
      match uu___ with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let v1 = f k in (FStarC_SMap.add cache k v1; v1) in
    find_or v do_locate_z3
