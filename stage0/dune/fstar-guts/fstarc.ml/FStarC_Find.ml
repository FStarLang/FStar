open Prims
let cached_fun (cache : 'a FStarC_SMap.t) (f : Prims.string -> 'a)
  (s : Prims.string) : 'a=
  let uu___ = FStarC_SMap.try_find cache s in
  match uu___ with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None ->
      let v = f s in (FStarC_SMap.add cache s v; v)
let _full_include :
  Prims.string Prims.list FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let find_file_cache :
  Prims.string FStar_Pervasives_Native.option FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (100))
let clear (uu___ : unit) : unit=
  FStarC_SMap.clear find_file_cache;
  FStarC_Effect.op_Colon_Equals _full_include FStar_Pervasives_Native.None
let _include : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let _cache_dir :
  Prims.string FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let _odir : Prims.string FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let _no_default_includes : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
let _with_fstarc : Prims.bool FStarC_Effect.ref= FStarC_Effect.mk_ref false
let get_include_path (uu___ : unit) : Prims.string Prims.list=
  FStarC_Effect.op_Bang _include
let set_include_path (path : Prims.string Prims.list) : unit=
  clear (); FStarC_Effect.op_Colon_Equals _include path
let get_cache_dir (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  FStarC_Effect.op_Bang _cache_dir
let set_cache_dir (path : Prims.string) : unit=
  clear ();
  FStarC_Effect.op_Colon_Equals _cache_dir
    (FStar_Pervasives_Native.Some path)
let get_odir (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  FStarC_Effect.op_Bang _odir
let set_odir (path : Prims.string) : unit=
  clear ();
  FStarC_Effect.op_Colon_Equals _odir (FStar_Pervasives_Native.Some path)
let get_no_default_includes (uu___ : unit) : Prims.bool=
  FStarC_Effect.op_Bang _no_default_includes
let set_no_default_includes (b : Prims.bool) : unit=
  clear (); FStarC_Effect.op_Colon_Equals _no_default_includes b
let get_with_fstarc (uu___ : unit) : Prims.bool=
  FStarC_Effect.op_Bang _with_fstarc
let set_with_fstarc (b : Prims.bool) : unit=
  clear (); FStarC_Effect.op_Colon_Equals _with_fstarc b
let fstar_bin_directory : Prims.string= FStarC_Util.get_exec_dir ()
let read_fstar_include (fn : Prims.string) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
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
let rec expand_include_d (dirname : Prims.string) : Prims.string Prims.list=
  let dot_inc_path = Prims.strcat dirname "/fstar.include" in
  if FStarC_Filepath.file_exists dot_inc_path
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
let expand_include_ds (dirnames : Prims.string Prims.list) :
  Prims.string Prims.list= FStarC_List.collect expand_include_d dirnames
let lib_root (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  let uu___1 = FStarC_Effect.op_Bang _no_default_includes in
  if uu___1
  then FStar_Pervasives_Native.None
  else
    (let uu___3 = FStarC_Util.expand_environment_variable "FSTAR_LIB" in
     match uu___3 with
     | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
     | FStar_Pervasives_Native.None ->
         let uu___4 =
           FStarC_Filepath.canonicalize
             (Prims.strcat fstar_bin_directory "/../lib/fstar") in
         FStar_Pervasives_Native.Some uu___4)
let fstarc_paths (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Effect.op_Bang _with_fstarc in
  if uu___1
  then
    let uu___2 =
      FStarC_Filepath.canonicalize
        (Prims.strcat fstar_bin_directory "/../lib/fstar/fstarc") in
    expand_include_d uu___2
  else []
let lib_paths (uu___ : unit) : Prims.string Prims.list=
  let uu___1 =
    let uu___2 =
      let uu___3 = lib_root () in FStarC_Common.option_to_list uu___3 in
    expand_include_ds uu___2 in
  let uu___2 = fstarc_paths () in FStar_List_Tot_Base.op_At uu___1 uu___2
let full_include_path (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Effect.op_Bang _full_include in
  match uu___1 with
  | FStar_Pervasives_Native.Some paths -> paths
  | FStar_Pervasives_Native.None ->
      let res =
        let cache_dir =
          let uu___2 = FStarC_Effect.op_Bang _cache_dir in
          match uu___2 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some c -> [c] in
        let include_paths =
          let uu___2 = FStarC_Effect.op_Bang _include in
          expand_include_ds uu___2 in
        let uu___2 =
          let uu___3 = lib_paths () in
          let uu___4 =
            let uu___5 = expand_include_d "." in
            FStar_List_Tot_Base.op_At include_paths uu___5 in
          FStar_List_Tot_Base.op_At uu___3 uu___4 in
        FStar_List_Tot_Base.op_At cache_dir uu___2 in
      (FStarC_Effect.op_Colon_Equals _full_include
         (FStar_Pervasives_Native.Some res);
       res)
let do_find (paths : Prims.string Prims.list) (filename : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = FStarC_Filepath.is_path_absolute filename in
  if uu___
  then
    (if FStarC_Filepath.file_exists filename
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
                     else FStarC_Filepath.join_paths p filename in
                   if FStarC_Filepath.file_exists path
                   then FStar_Pervasives_Native.Some path
                   else FStar_Pervasives_Native.None)) ()
     with | uu___2 -> FStar_Pervasives_Native.None)
let find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option=
  cached_fun find_file_cache
    (fun s -> let uu___ = full_include_path () in do_find uu___ s)
let find_file_odir (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let odir =
    let uu___ = FStarC_Effect.op_Bang _odir in
    match uu___ with
    | FStar_Pervasives_Native.Some d -> [d]
    | FStar_Pervasives_Native.None -> [] in
  let uu___ =
    let uu___1 = full_include_path () in
    FStar_List_Tot_Base.op_At uu___1 odir in
  do_find uu___ s
let prepend_output_dir (fname : Prims.string) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang _odir in
  match uu___ with
  | FStar_Pervasives_Native.None -> fname
  | FStar_Pervasives_Native.Some x -> FStarC_Filepath.join_paths x fname
let prepend_cache_dir (fpath : Prims.string) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang _cache_dir in
  match uu___ with
  | FStar_Pervasives_Native.None -> fpath
  | FStar_Pervasives_Native.Some x ->
      let uu___1 = FStarC_Filepath.basename fpath in
      FStarC_Filepath.join_paths x uu___1
let locate (uu___ : unit) : Prims.string=
  let uu___1 = FStarC_Util.get_exec_dir () in
  FStarC_Filepath.normalize_file_path uu___1
let locate_lib (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  let uu___1 = lib_root () in
  FStarC_Option.map FStarC_Filepath.normalize_file_path uu___1
let locate_ocaml (uu___ : unit) : Prims.string=
  let uu___1 =
    let uu___2 = FStarC_Util.get_exec_dir () in Prims.strcat uu___2 "/../lib" in
  FStarC_Filepath.normalize_file_path uu___1
let refind_file (f : Prims.string) : Prims.string=
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 =
             let uu___2 = FStarC_Filepath.basename f in find_file uu___2 in
           (match uu___1 with
            | FStar_Pervasives_Native.None -> f
            | FStar_Pervasives_Native.Some abs -> abs)) ()
  with | uu___ -> f
