open Prims
let (fstar_bin_directory : Prims.string) =
  FStarC_Compiler_Util.get_exec_dir ()
let (read_fstar_include :
  Prims.string -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun fn ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let s = FStarC_Compiler_Util.file_get_contents fn in
             let subdirs =
               FStarC_Compiler_List.filter
                 (fun s1 ->
                    (s1 <> "") &&
                      (let uu___1 =
                         let uu___2 =
                           FStarC_Compiler_String.get s1 Prims.int_zero in
                         uu___2 = 35 in
                       Prims.op_Negation uu___1))
                 (FStarC_Compiler_String.split [10] s) in
             FStar_Pervasives_Native.Some subdirs) ()
    with
    | uu___ ->
        (failwith (Prims.strcat "Could not read " fn);
         FStar_Pervasives_Native.None)
let rec (expand_include_d : Prims.string -> Prims.string Prims.list) =
  fun dirname ->
    let dot_inc_path = Prims.strcat dirname "/fstar.include" in
    if FStarC_Compiler_Util.file_exists dot_inc_path
    then
      let subdirs =
        let uu___ = read_fstar_include dot_inc_path in
        FStar_Pervasives_Native.__proj__Some__item__v uu___ in
      let uu___ =
        FStarC_Compiler_List.collect
          (fun subd ->
             expand_include_d (Prims.strcat dirname (Prims.strcat "/" subd)))
          subdirs in
      dirname :: uu___
    else [dirname]
let (expand_include_ds : Prims.string Prims.list -> Prims.string Prims.list)
  = fun dirnames -> FStarC_Compiler_List.collect expand_include_d dirnames
let (lib_root : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ ->
    let uu___1 = FStarC_Options.no_default_includes () in
    if uu___1
    then FStar_Pervasives_Native.None
    else
      (let uu___3 =
         FStarC_Compiler_Util.expand_environment_variable "FSTAR_LIB" in
       match uu___3 with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None ->
           if
             FStarC_Compiler_Util.file_exists
               (Prims.strcat fstar_bin_directory "/../ulib")
           then
             FStar_Pervasives_Native.Some
               (Prims.strcat fstar_bin_directory "/../ulib")
           else
             if
               FStarC_Compiler_Util.file_exists
                 (Prims.strcat fstar_bin_directory "/../lib/fstar")
             then
               FStar_Pervasives_Native.Some
                 (Prims.strcat fstar_bin_directory "/../lib/fstar")
             else FStar_Pervasives_Native.None)
let (lib_paths : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = lib_root () in FStarC_Common.option_to_list uu___2 in
    expand_include_ds uu___1
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
        FStarC_Compiler_List.op_At include_paths uu___4 in
      FStarC_Compiler_List.op_At uu___2 uu___3 in
    FStarC_Compiler_List.op_At cache_dir uu___1
let (do_find :
  Prims.string Prims.list ->
    Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun paths ->
    fun filename ->
      let uu___ = FStarC_Compiler_Util.is_path_absolute filename in
      if uu___
      then
        (if FStarC_Compiler_Util.file_exists filename
         then FStar_Pervasives_Native.Some filename
         else FStar_Pervasives_Native.None)
      else
        (try
           (fun uu___2 ->
              match () with
              | () ->
                  FStarC_Compiler_Util.find_map
                    (FStarC_Compiler_List.rev paths)
                    (fun p ->
                       let path =
                         if p = "."
                         then filename
                         else FStarC_Compiler_Util.join_paths p filename in
                       if FStarC_Compiler_Util.file_exists path
                       then FStar_Pervasives_Native.Some path
                       else FStar_Pervasives_Native.None)) ()
         with | uu___2 -> FStar_Pervasives_Native.None)
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let cache = FStarC_Compiler_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu___ = FStarC_Compiler_Util.smap_try_find cache filename in
    match uu___ with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let result = let uu___1 = include_path () in do_find uu___1 filename in
        (if FStar_Pervasives_Native.uu___is_Some result
         then FStarC_Compiler_Util.smap_add cache filename result
         else ();
         result)
let (find_file_odir :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  let cache = FStarC_Compiler_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu___ = FStarC_Compiler_Util.smap_try_find cache filename in
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
            let uu___2 = include_path () in
            FStarC_Compiler_List.op_At uu___2 odir in
          do_find uu___1 filename in
        (if FStar_Pervasives_Native.uu___is_Some result
         then FStarC_Compiler_Util.smap_add cache filename result
         else ();
         result)
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname ->
    let uu___ = FStarC_Options.output_dir () in
    match uu___ with
    | FStar_Pervasives_Native.None -> fname
    | FStar_Pervasives_Native.Some x ->
        FStarC_Compiler_Util.join_paths x fname
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath ->
    let uu___ = FStarC_Options.cache_dir () in
    match uu___ with
    | FStar_Pervasives_Native.None -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu___1 = FStarC_Compiler_Util.basename fpath in
        FStarC_Compiler_Util.join_paths x uu___1
let (locate : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Util.get_exec_dir () in
    FStarC_Compiler_Util.normalize_file_path uu___1
let (locate_lib : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ ->
    let uu___1 = lib_root () in
    FStarC_Compiler_Util.map_opt uu___1
      FStarC_Compiler_Util.normalize_file_path
let (locate_ocaml : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Compiler_Util.get_exec_dir () in
      Prims.strcat uu___2 "/../lib" in
    FStarC_Compiler_Util.normalize_file_path uu___1