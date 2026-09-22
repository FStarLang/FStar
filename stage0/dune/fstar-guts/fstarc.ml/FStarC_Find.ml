open Prims
type module_include_path_kind =
  | Flat 
  | Recursive 
let uu___is_Flat (projectee : module_include_path_kind) : Prims.bool=
  match projectee with | Flat -> true | uu___ -> false
let uu___is_Recursive (projectee : module_include_path_kind) : Prims.bool=
  match projectee with | Recursive -> true | uu___ -> false
type module_include_path =
  {
  dir: Prims.string ;
  kind: module_include_path_kind }
let __proj__Mkmodule_include_path__item__dir
  (projectee : module_include_path) : Prims.string=
  match projectee with | { dir; kind;_} -> dir
let __proj__Mkmodule_include_path__item__kind
  (projectee : module_include_path) : module_include_path_kind=
  match projectee with | { dir; kind;_} -> kind
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
let _module_include_paths_normalized :
  module_include_path Prims.list FStar_Pervasives_Native.option
    FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let find_file_cache :
  Prims.string FStar_Pervasives_Native.option FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 100)
let _epoch : Prims.int FStarC_Effect.ref= FStarC_Effect.mk_ref Prims.int_zero
let clear (uu___ : unit) : unit=
  FStarC_SMap.clear find_file_cache;
  FStarC_Effect.op_Colon_Equals _full_include FStar_Pervasives_Native.None;
  FStarC_Effect.op_Colon_Equals _module_include_paths_normalized
    FStar_Pervasives_Native.None;
  (let uu___5 =
     let uu___6 = FStarC_Effect.op_Bang _epoch in uu___6 + Prims.int_one in
   FStarC_Effect.op_Colon_Equals _epoch uu___5)
let _include : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let _file_list : Prims.string Prims.list FStarC_Effect.ref=
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
let set_file_list (files : Prims.string Prims.list) : unit=
  clear (); FStarC_Effect.op_Colon_Equals _file_list files
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
let lib_root (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  let uu___1 = FStarC_Effect.op_Bang _no_default_includes in
  if uu___1
  then FStar_Pervasives_Native.None
  else
    (let uu___2 = FStarC_Util.expand_environment_variable "FSTAR_LIB" in
     match uu___2 with
     | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
     | FStar_Pervasives_Native.None ->
         FStar_Pervasives_Native.Some
           (FStarC_Filepath.canonicalize
              (Prims.strcat fstar_bin_directory "/../lib/fstar")))
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
                  if s1 <> ""
                  then
                    let uu___2 =
                      let uu___3 = FStarC_String.get s1 Prims.int_zero in
                      uu___3 = 35 in
                    Prims.not uu___2
                  else false) uu___1 in
           FStar_Pervasives_Native.Some subdirs) ()
  with
  | uu___ ->
      (FStarC_Effect.failwith (Prims.strcat "Could not read " fn);
       FStar_Pervasives_Native.None)
let has_fstar_include (dirname : Prims.string) : Prims.bool=
  FStarC_Filepath.file_exists (Prims.strcat dirname "/fstar.include")
let rec expand_module_include_path (root_kind : module_include_path_kind)
  (dirname : Prims.string) : module_include_path Prims.list=
  let uu___ = has_fstar_include dirname in
  if uu___
  then
    let dot_inc_path = Prims.strcat dirname "/fstar.include" in
    let subdirs =
      let uu___1 = read_fstar_include dot_inc_path in
      match uu___1 with | FStar_Pervasives_Native.Some v -> v in
    let go subd =
      expand_module_include_path Recursive
        (Prims.strcat dirname (Prims.strcat "/" subd)) in
    let uu___1 = FStarC_List.collect go subdirs in
    { dir = dirname; kind = Flat } :: uu___1
  else [{ dir = dirname; kind = root_kind }]
let expand_module_include_paths (root_kind : module_include_path_kind)
  (dirnames : Prims.string Prims.list) : module_include_path Prims.list=
  FStarC_List.collect (expand_module_include_path root_kind) dirnames
let include_dirs (paths : module_include_path Prims.list) :
  Prims.string Prims.list= FStarC_List.map (fun path -> path.dir) paths
let expand_include_d (dirname : Prims.string) : Prims.string Prims.list=
  let uu___ = expand_module_include_path Flat dirname in include_dirs uu___
let fstarc_roots (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Effect.op_Bang _with_fstarc in
  if uu___1
  then
    [FStarC_Filepath.canonicalize
       (Prims.strcat fstar_bin_directory "/../lib/fstar/fstarc")]
  else []
let lib_roots (uu___ : unit) : Prims.string Prims.list=
  let uu___1 =
    let uu___2 = lib_root () in FStarC_Common.option_to_list uu___2 in
  let uu___2 = fstarc_roots () in FStar_List_Tot_Base.op_At uu___1 uu___2
let lib_paths (uu___ : unit) : module_include_path Prims.list=
  let uu___1 = lib_roots () in expand_module_include_paths Flat uu___1
let rec path_is_at_or_below (root : Prims.string) (path : Prims.string) :
  Prims.bool=
  if root = path
  then true
  else
    (let parent = FStarC_Filepath.dirname path in
     if parent <> path then path_is_at_or_below root parent else false)
let module_include_covers_path (inc : module_include_path)
  (path : Prims.string) : Prims.bool=
  let incnorm = FStarC_Filepath.normalize_file_path inc.dir in
  let pathnorm = FStarC_Filepath.normalize_file_path path in
  match inc.kind with
  | Flat -> incnorm = pathnorm
  | Recursive -> path_is_at_or_below incnorm pathnorm
let command_line_include_roots (uu___ : unit) : Prims.string Prims.list=
  let files = FStarC_Effect.op_Bang _file_list in
  let explicit_includes =
    let uu___1 = FStarC_Effect.op_Bang _include in
    expand_module_include_paths Recursive uu___1 in
  let file_roots =
    FStarC_List.collect
      (fun file ->
         let root =
           FStarC_Filepath.normalize_file_path (FStarC_Filepath.dirname file) in
         let is_dir = FStarC_Filepath.is_directory file in
         if is_dir then [] else [root]) files in
  FStarC_List.filter
    (fun root ->
       let uu___1 =
         FStarC_List.existsb (fun inc -> module_include_covers_path inc root)
           explicit_includes in
       Prims.not uu___1) file_roots
let command_line_include_paths (uu___ : unit) :
  module_include_path Prims.list=
  let uu___1 = command_line_include_roots () in
  expand_module_include_paths Flat uu___1
let module_include_paths (uu___ : unit) : module_include_path Prims.list=
  let cache_dir =
    let uu___1 = FStarC_Effect.op_Bang _cache_dir in
    match uu___1 with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some dir -> [{ dir; kind = Flat }] in
  let uu___1 =
    let uu___2 = lib_paths () in
    let uu___3 =
      let uu___4 =
        let uu___5 = FStarC_Effect.op_Bang _include in
        expand_module_include_paths Recursive uu___5 in
      let uu___5 =
        let uu___6 = command_line_include_paths () in
        let uu___7 = expand_module_include_path Flat "." in
        FStar_List_Tot_Base.op_At uu___6 uu___7 in
      FStar_List_Tot_Base.op_At uu___4 uu___5 in
    FStar_List_Tot_Base.op_At uu___2 uu___3 in
  FStar_List_Tot_Base.op_At cache_dir uu___1
let epoch (uu___ : unit) : Prims.int= FStarC_Effect.op_Bang _epoch
let full_include_path (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Effect.op_Bang _full_include in
  match uu___1 with
  | FStar_Pervasives_Native.Some paths -> paths
  | FStar_Pervasives_Native.None ->
      let res = let uu___2 = module_include_paths () in include_dirs uu___2 in
      (FStarC_Effect.op_Colon_Equals _full_include
         (FStar_Pervasives_Native.Some res);
       res)
let module_include_paths_normalized (uu___ : unit) :
  module_include_path Prims.list=
  let uu___1 = FStarC_Effect.op_Bang _module_include_paths_normalized in
  match uu___1 with
  | FStar_Pervasives_Native.Some paths -> paths
  | FStar_Pervasives_Native.None ->
      let paths =
        let uu___2 = module_include_paths () in
        FStarC_List.map
          (fun path ->
             let uu___3 = FStarC_Filepath.normalize_file_path path.dir in
             { dir = uu___3; kind = (path.kind) }) uu___2 in
      (FStarC_Effect.op_Colon_Equals _module_include_paths_normalized
         (FStar_Pervasives_Native.Some paths);
       paths)
let do_find (paths : Prims.string Prims.list) (filename : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if FStarC_Filepath.is_path_absolute filename
  then
    (if FStarC_Filepath.file_exists filename
     then FStar_Pervasives_Native.Some filename
     else FStar_Pervasives_Native.None)
  else
    (try
       (fun uu___ ->
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
     with | uu___ -> FStar_Pervasives_Native.None)
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
let prepend_cache_dir (fpath : Prims.string) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang _cache_dir in
  match uu___ with
  | FStar_Pervasives_Native.None -> fpath
  | FStar_Pervasives_Native.Some x ->
      FStarC_Filepath.join_paths x (FStarC_Filepath.basename fpath)
let prepend_output_dir (fname : Prims.string) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang _odir in
  match uu___ with
  | FStar_Pervasives_Native.None -> fname
  | FStar_Pervasives_Native.Some x -> FStarC_Filepath.join_paths x fname
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
           let uu___1 = find_file (FStarC_Filepath.basename f) in
           (match uu___1 with
            | FStar_Pervasives_Native.None -> f
            | FStar_Pervasives_Native.Some abs -> abs)) ()
  with | uu___ -> f
