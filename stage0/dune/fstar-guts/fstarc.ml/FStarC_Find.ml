open Prims
let (fstar_bin_directory : Prims.string) = FStarC_Util.get_exec_dir ()
let (read_fstar_include :
  Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun fn ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let s = FStarC_Util.file_get_contents fn in
             let subdirs =
               let uu___1 =
                 FStarC_List.map FStarC_Util.trim_string
                   (FStarC_String.split [13; 10] s) in
               FStarC_List.filter
                 (fun s1 ->
                    (s1 <> "") &&
                      (let uu___2 =
                         let uu___3 = FStarC_String.get s1 Prims.int_zero in
                         uu___3 = 35 in
                       Prims.op_Negation uu___2)) uu___1 in
             FStar_Pervasives_Native.Some subdirs) ()
    with
    | uu___ ->
        (failwith (Prims.strcat "Could not read " fn);
         FStar_Pervasives_Native.None)
let rec (expand_include_d : Prims.string -> Prims.string Prims.list) =
  fun dirname ->
    let dot_inc_path = Prims.strcat dirname "/fstar.include" in
    if FStarC_Util.file_exists dot_inc_path
    then
      let subdirs =
        let uu___ = read_fstar_include dot_inc_path in
        FStar_Pervasives_Native.__proj__Some__item__v uu___ in
      let uu___ =
        FStarC_List.collect
          (fun subd ->
             expand_include_d (Prims.strcat dirname (Prims.strcat "/" subd)))
          subdirs in
      dirname :: uu___
    else [dirname]
let (expand_include_ds : Prims.string Prims.list -> Prims.string Prims.list)
  = fun dirnames -> FStarC_List.collect expand_include_d dirnames
let (lib_root : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ ->
    let uu___1 = FStarC_Options.no_default_includes () in
    if uu___1
    then FStar_Pervasives_Native.None
    else
      (let uu___3 = FStarC_Util.expand_environment_variable "FSTAR_LIB" in
       match uu___3 with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some
             (Prims.strcat fstar_bin_directory "/../lib/fstar"))
let (fstarc_paths : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let uu___1 = FStarC_Options.with_fstarc () in
    if uu___1
    then
      expand_include_d
        (Prims.strcat fstar_bin_directory "/../lib/fstar/fstarc")
    else []
let (lib_paths : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 = lib_root () in FStarC_Common.option_to_list uu___3 in
      expand_include_ds uu___2 in
    let uu___2 = fstarc_paths () in FStarC_List.op_At uu___1 uu___2
let (include_path : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let cache_dir =
      let uu___1 = FStarC_Options.cache_dir () in
      match uu___1 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some c -> [c] in
    let include_paths =
      let uu___1 = FStarC_Options.include_ () in expand_include_ds uu___1 in
    let uu___1 =
      let uu___2 = lib_paths () in
      let uu___3 =
        let uu___4 = expand_include_d "." in
        FStarC_List.op_At include_paths uu___4 in
      FStarC_List.op_At uu___2 uu___3 in
    FStarC_List.op_At cache_dir uu___1
let (do_find :
  Prims.string Prims.list ->
    Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun paths ->
    fun filename ->
      let uu___ = FStarC_Util.is_path_absolute filename in
      if uu___
      then
        (if FStarC_Util.file_exists filename
         then FStar_Pervasives_Native.Some filename
         else FStar_Pervasives_Native.None)
      else
        (try
           (fun uu___2 ->
              match () with
              | () ->
                  FStarC_Util.find_map (FStarC_List.rev paths)
                    (fun p ->
                       let path =
                         if p = "."
                         then filename
                         else FStarC_Util.join_paths p filename in
                       if FStarC_Util.file_exists path
                       then FStar_Pervasives_Native.Some path
                       else FStar_Pervasives_Native.None)) ()
         with | uu___2 -> FStar_Pervasives_Native.None)
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let cache = FStarC_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu___ = FStarC_Util.smap_try_find cache filename in
    match uu___ with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let result = let uu___1 = include_path () in do_find uu___1 filename in
        (if FStar_Pervasives_Native.uu___is_Some result
         then FStarC_Util.smap_add cache filename result
         else ();
         result)
let (find_file_odir :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  let cache = FStarC_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu___ = FStarC_Util.smap_try_find cache filename in
    match uu___ with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let odir =
          let uu___1 = FStarC_Options.output_dir () in
          match uu___1 with
          | FStar_Pervasives_Native.Some d -> [d]
          | FStar_Pervasives_Native.None -> [] in
        let result =
          let uu___1 =
            let uu___2 = include_path () in FStarC_List.op_At uu___2 odir in
          do_find uu___1 filename in
        (if FStar_Pervasives_Native.uu___is_Some result
         then FStarC_Util.smap_add cache filename result
         else ();
         result)
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname ->
    let uu___ = FStarC_Options.output_dir () in
    match uu___ with
    | FStar_Pervasives_Native.None -> fname
    | FStar_Pervasives_Native.Some x -> FStarC_Util.join_paths x fname
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath ->
    let uu___ = FStarC_Options.cache_dir () in
    match uu___ with
    | FStar_Pervasives_Native.None -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu___1 = FStarC_Util.basename fpath in
        FStarC_Util.join_paths x uu___1
let (locate : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 = FStarC_Util.get_exec_dir () in
    FStarC_Util.normalize_file_path uu___1
let (locate_lib : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ ->
    let uu___1 = lib_root () in
    FStarC_Util.map_opt uu___1 FStarC_Util.normalize_file_path
let (locate_ocaml : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Util.get_exec_dir () in
      Prims.strcat uu___2 "/../lib" in
    FStarC_Util.normalize_file_path uu___1
let (z3url : Prims.string) = "https://github.com/Z3Prover/z3/releases"
let (packaged_z3_versions : Prims.string Prims.list) = ["4.8.5"; "4.13.3"]
let (z3_install_suggestion :
  Prims.string -> FStarC_Pprint.document Prims.list) =
  fun v ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Util.format1 "Please download version %s of Z3 from" v in
          FStarC_Errors_Msg.text uu___3 in
        let uu___3 = FStarC_Pprint.url z3url in
        FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one uu___2 uu___3 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Errors_Msg.text "and install it into your $PATH as" in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStarC_Platform.exe (Prims.strcat "z3-" v) in
                FStarC_Pprint.doc_of_string uu___8 in
              FStarC_Pprint.squotes uu___7 in
            FStarC_Pprint.op_Hat_Hat uu___6 FStarC_Pprint.dot in
          FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
        FStarC_Pprint.group uu___3 in
      FStarC_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
    let uu___1 =
      let uu___2 =
        if FStarC_List.mem v packaged_z3_versions
        then
          let uu___3 =
            FStarC_Util.format1
              "Version %s of Z3 should be included in binary packages of F*. If you are using a binary package and are seeing\n              this error, please file a bug report."
              v in
          FStarC_Errors_Msg.text uu___3
        else FStarC_Pprint.empty in
      [uu___2] in
    uu___ :: uu___1
let (z3_inpath : Prims.string -> Prims.bool) =
  fun path ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let s =
               FStarC_Util.run_process "z3_pathtest" path ["-version"]
                 FStar_Pervasives_Native.None in
             s <> "") ()
    with | uu___ -> false
let (do_locate_z3 :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun v ->
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
           let uu___1 = lib_root () in
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___1)
                (fun uu___2 ->
                   (fun root ->
                      let root = Obj.magic root in
                      let path1 =
                        FStarC_Platform.exe
                          (Prims.strcat root
                             (Prims.strcat "/z3-" (Prims.strcat v "/bin/z3"))) in
                      let path2 = FStarC_Util.normalize_file_path path1 in
                      let uu___2 = guard (FStarC_Util.file_exists path2) in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () () uu___2
                           (fun uu___3 ->
                              (fun uu___3 ->
                                 let uu___3 = Obj.magic uu___3 in
                                 Obj.magic
                                   (FStar_Pervasives_Native.Some path2))
                                uu___3))) uu___2))) uu___ in
      let from_path uu___1 uu___ =
        (fun cmd ->
           fun uu___ ->
             let cmd1 = FStarC_Platform.exe cmd in
             let uu___1 = let uu___2 = z3_inpath cmd1 in guard uu___2 in
             Obj.magic
               (FStarC_Class_Monad.op_let_Bang
                  FStarC_Class_Monad.monad_option () () uu___1
                  (fun uu___2 ->
                     (fun uu___2 ->
                        let uu___2 = Obj.magic uu___2 in
                        Obj.magic (FStar_Pervasives_Native.Some cmd1)) uu___2)))
          uu___1 uu___ in
      op_Less_Bar_Greater
        (op_Less_Bar_Greater
           (op_Less_Bar_Greater
              (op_Less_Bar_Greater FStarC_Options.smt in_lib)
              (from_path (Prims.strcat "z3-" v))) (from_path "z3"))
        (fun uu___ -> FStar_Pervasives_Native.None) () in
    (let uu___1 = FStarC_Debug.any () in
     if uu___1
     then
       let uu___2 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_string v in
       let uu___3 =
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_option FStarC_Class_Show.showable_string)
           path in
       FStarC_Util.print2 "do_locate_z3(%s) = %s\n" uu___2 uu___3
     else ());
    path
let (locate_z3 : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun v ->
    let cache = FStarC_Util.smap_create (Prims.of_int (5)) in
    let find_or k f =
      let uu___ = FStarC_Util.smap_try_find cache k in
      match uu___ with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let v1 = f k in (FStarC_Util.smap_add cache k v1; v1) in
    find_or v do_locate_z3