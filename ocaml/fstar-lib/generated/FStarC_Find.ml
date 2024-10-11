open Prims
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStarC_Compiler_Util.smap_create (Prims.of_int (100)) in
  fun filename ->
    let uu___ = FStarC_Compiler_Util.smap_try_find file_map filename in
    match uu___ with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let result =
          try
            (fun uu___1 ->
               match () with
               | () ->
                   let uu___2 =
                     FStarC_Compiler_Util.is_path_absolute filename in
                   if uu___2
                   then
                     (if FStarC_Compiler_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu___4 =
                        let uu___5 = FStarC_Options.include_path () in
                        FStar_List_Tot_Base.rev uu___5 in
                      FStarC_Compiler_Util.find_map uu___4
                        (fun p ->
                           let path =
                             if p = "."
                             then filename
                             else FStarC_Compiler_Util.join_paths p filename in
                           if FStarC_Compiler_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___1 -> FStar_Pervasives_Native.None in
        (if FStar_Pervasives_Native.uu___is_Some result
         then FStarC_Compiler_Util.smap_add file_map filename result
         else ();
         result)