open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "10") 
type tc_result =
  {
  checked_module: FStar_Syntax_Syntax.modul ;
  mii: FStar_Syntax_DsEnv.module_inclusion_info ;
  smt_decls:
    (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
      Prims.list)
    ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let (__proj__Mktc_result__item__checked_module :
  tc_result -> FStar_Syntax_Syntax.modul) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        checked_module
  
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} -> mii
  
let (__proj__Mktc_result__item__smt_decls :
  tc_result ->
    (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
      Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        smt_decls
  
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        tc_time
  
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        extraction_time
  
type checked_file_entry =
  (Prims.int * (Prims.string * Prims.string) Prims.list * Prims.string *
    FStar_Parser_Dep.parsing_data * tc_result)
type tc_result_t =
  | Unknown of ((Prims.string * Prims.string) Prims.list * tc_result) 
  | Invalid of Prims.string 
  | Valid of (Prims.string * tc_result) 
let (uu___is_Unknown : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown _0 -> true | uu____66357 -> false
  
let (__proj__Unknown__item___0 :
  tc_result_t -> ((Prims.string * Prims.string) Prims.list * tc_result)) =
  fun projectee  -> match projectee with | Unknown _0 -> _0 
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Invalid _0 -> true | uu____66413 -> false
  
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee  -> match projectee with | Invalid _0 -> _0 
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Valid _0 -> true | uu____66440 -> false
  
let (__proj__Valid__item___0 : tc_result_t -> (Prims.string * tc_result)) =
  fun projectee  -> match projectee with | Valid _0 -> _0 
type cache_t =
  (tc_result_t * (Prims.string,FStar_Parser_Dep.parsing_data)
    FStar_Util.either)
let (mcache : cache_t FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let (hash_dependences :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      (Prims.string,(Prims.string * Prims.string) Prims.list)
        FStar_Util.either)
  =
  fun deps  ->
    fun fn  ->
      let fn1 =
        let uu____66518 = FStar_Options.find_file fn  in
        match uu____66518 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____66526 -> fn  in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1  in
      let source_hash = FStar_Util.digest_of_file fn1  in
      let has_interface =
        let uu____66536 = FStar_Parser_Dep.interface_of deps module_name  in
        FStar_Option.isSome uu____66536  in
      let interface_hash =
        let uu____66550 =
          (FStar_Parser_Dep.is_implementation fn1) && has_interface  in
        if uu____66550
        then
          let uu____66561 =
            let uu____66568 =
              let uu____66570 =
                let uu____66572 =
                  FStar_Parser_Dep.interface_of deps module_name  in
                FStar_Option.get uu____66572  in
              FStar_Util.digest_of_file uu____66570  in
            ("interface", uu____66568)  in
          [uu____66561]
        else []  in
      let binary_deps =
        let uu____66604 = FStar_Parser_Dep.deps_of deps fn1  in
        FStar_All.pipe_right uu____66604
          (FStar_List.filter
             (fun fn2  ->
                let uu____66619 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu____66622 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     uu____66622 = module_name)
                   in
                Prims.op_Negation uu____66619))
         in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11  ->
             fun fn2  ->
               let uu____66638 = FStar_Parser_Dep.lowercase_module_name fn11
                  in
               let uu____66640 = FStar_Parser_Dep.lowercase_module_name fn2
                  in
               FStar_String.compare uu____66638 uu____66640) binary_deps
         in
      let rec hash_deps out uu___650_66676 =
        match uu___650_66676 with
        | [] ->
            FStar_Util.Inr
              (FStar_List.append (("source", source_hash) :: interface_hash)
                 out)
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2  in
            let digest =
              let uu____66742 = FStar_Util.smap_try_find mcache cache_fn  in
              match uu____66742 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn
                     in
                  ((let uu____66755 = FStar_Options.debug_any ()  in
                    if uu____66755 then FStar_Util.print1 "%s\\m" msg else ());
                   FStar_Util.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg,uu____66764) ->
                  FStar_Util.Inl msg
              | FStar_Pervasives_Native.Some
                  (Valid (dig,uu____66779),uu____66780) -> FStar_Util.Inr dig
              | FStar_Pervasives_Native.Some
                  (Unknown uu____66795,uu____66796) ->
                  let uu____66819 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name
                     in
                  failwith uu____66819
               in
            (match digest with
             | FStar_Util.Inl msg -> FStar_Util.Inl msg
             | FStar_Util.Inr dig ->
                 let uu____66858 =
                   let uu____66867 =
                     let uu____66874 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     (uu____66874, dig)  in
                   uu____66867 :: out  in
                 hash_deps uu____66858 deps1)
         in
      hash_deps [] binary_deps1
  
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn  ->
    fun checked_fn  ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache)  in
      let uu____66911 = FStar_All.pipe_right elt FStar_Util.is_some  in
      if uu____66911
      then FStar_All.pipe_right elt FStar_Util.must
      else
        (let add_and_return elt1 =
           FStar_Util.smap_add mcache checked_fn elt1; elt1  in
         if Prims.op_Negation (FStar_Util.file_exists checked_fn)
         then
           let msg =
             FStar_Util.format1 "checked file %s does not exist" checked_fn
              in
           add_and_return ((Invalid msg), (FStar_Util.Inl msg))
         else
           (let uu____66940 = FStar_Util.load_value_from_file checked_fn  in
            match uu____66940 with
            | FStar_Pervasives_Native.None  ->
                let msg =
                  FStar_Util.format1 "checked file %s is corrupt" checked_fn
                   in
                add_and_return ((Invalid msg), (FStar_Util.Inl msg))
            | FStar_Pervasives_Native.Some
                (vnum,deps_dig,dig,parsing_data,tc_result) ->
                if vnum <> cache_version_number
                then
                  let msg =
                    FStar_Util.format1
                      "checked file %s has incorrect version" checked_fn
                     in
                  add_and_return ((Invalid msg), (FStar_Util.Inl msg))
                else
                  (let current_dig = FStar_Util.digest_of_file fn  in
                   if dig <> current_dig
                   then
                     ((let uu____67075 = FStar_Options.debug_any ()  in
                       if uu____67075
                       then
                         FStar_Util.print4
                           "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n"
                           checked_fn fn current_dig dig
                       else ());
                      (let msg =
                         FStar_Util.format2
                           "checked file %s is stale (digest mismatch for %s)"
                           checked_fn fn
                          in
                       add_and_return ((Invalid msg), (FStar_Util.Inl msg))))
                   else
                     add_and_return
                       ((Unknown (deps_dig, tc_result)),
                         (FStar_Util.Inr parsing_data)))))
  
let (load_checked_file_with_tc_result :
  FStar_Parser_Dep.deps -> Prims.string -> Prims.string -> cache_t) =
  fun deps  ->
    fun fn  ->
      fun checked_fn  ->
        let elt = load_checked_file fn checked_fn  in
        match elt with
        | (Invalid uu____67127,uu____67128) -> elt
        | (Valid uu____67140,uu____67141) -> elt
        | (Unknown (deps_dig,tc_result),parsing_data) ->
            let uu____67186 = hash_dependences deps fn  in
            (match uu____67186 with
             | FStar_Util.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data)  in
                 (FStar_Util.smap_add mcache checked_fn elt1; elt1)
             | FStar_Util.Inr deps_dig' ->
                 if deps_dig = deps_dig'
                 then
                   let elt1 =
                     let uu____67264 =
                       let uu____67265 =
                         let uu____67271 =
                           FStar_Util.digest_of_file checked_fn  in
                         (uu____67271, tc_result)  in
                       Valid uu____67265  in
                     (uu____67264, parsing_data)  in
                   (FStar_Util.smap_add mcache checked_fn elt1;
                    (let validate_iface_cache uu____67285 =
                       let iface1 =
                         let uu____67290 =
                           FStar_All.pipe_right fn
                             FStar_Parser_Dep.lowercase_module_name
                            in
                         FStar_All.pipe_right uu____67290
                           (FStar_Parser_Dep.interface_of deps)
                          in
                       match iface1 with
                       | FStar_Pervasives_Native.None  -> ()
                       | FStar_Pervasives_Native.Some iface2 ->
                           (try
                              (fun uu___778_67309  ->
                                 match () with
                                 | () ->
                                     let iface_checked_fn =
                                       FStar_All.pipe_right iface2
                                         FStar_Parser_Dep.cache_file_name
                                        in
                                     let uu____67314 =
                                       FStar_Util.smap_try_find mcache
                                         iface_checked_fn
                                        in
                                     (match uu____67314 with
                                      | FStar_Pervasives_Native.Some
                                          (Unknown
                                           (uu____67317,tc_result1),parsing_data1)
                                          ->
                                          let uu____67346 =
                                            let uu____67347 =
                                              let uu____67348 =
                                                let uu____67354 =
                                                  FStar_Util.digest_of_file
                                                    iface_checked_fn
                                                   in
                                                (uu____67354, tc_result1)  in
                                              Valid uu____67348  in
                                            (uu____67347, parsing_data1)  in
                                          FStar_Util.smap_add mcache
                                            iface_checked_fn uu____67346
                                      | uu____67362 -> ())) ()
                            with | uu___777_67366 -> ())
                        in
                     validate_iface_cache (); elt1))
                 else
                   ((let uu____67371 = FStar_Options.debug_any ()  in
                     if uu____67371
                     then
                       ((let uu____67375 =
                           FStar_Util.string_of_int
                             (FStar_List.length deps_dig')
                            in
                         let uu____67383 =
                           FStar_Parser_Dep.print_digest deps_dig'  in
                         let uu____67385 =
                           FStar_Util.string_of_int
                             (FStar_List.length deps_dig)
                            in
                         let uu____67393 =
                           FStar_Parser_Dep.print_digest deps_dig  in
                         FStar_Util.print4
                           "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                           uu____67375 uu____67383 uu____67385 uu____67393);
                        if
                          (FStar_List.length deps_dig) =
                            (FStar_List.length deps_dig')
                        then
                          FStar_List.iter2
                            (fun uu____67429  ->
                               fun uu____67430  ->
                                 match (uu____67429, uu____67430) with
                                 | ((x,y),(x',y')) ->
                                     if (x <> x') || (y <> y')
                                     then
                                       let uu____67482 =
                                         FStar_Parser_Dep.print_digest
                                           [(x, y)]
                                          in
                                       let uu____67498 =
                                         FStar_Parser_Dep.print_digest
                                           [(x', y')]
                                          in
                                       FStar_Util.print2
                                         "Differ at: Expected %s\n Got %s\n"
                                         uu____67482 uu____67498
                                     else ()) deps_dig deps_dig'
                        else ())
                     else ());
                    (let msg =
                       FStar_Util.format1
                         "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)"
                         checked_fn
                        in
                     let elt1 = ((Invalid msg), (FStar_Util.Inl msg))  in
                     FStar_Util.smap_add mcache checked_fn elt1; elt1)))
  
let (load_parsing_data_from_cache :
  Prims.string ->
    FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
  =
  fun file_name  ->
    let cache_file =
      try
        (fun uu___810_67560  ->
           match () with
           | () ->
               let uu____67564 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____67564
                 (fun _67571  -> FStar_Pervasives_Native.Some _67571)) ()
      with | uu___809_67573 -> FStar_Pervasives_Native.None  in
    match cache_file with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some cache_file1 ->
        let uu____67584 = load_checked_file file_name cache_file1  in
        (match uu____67584 with
         | (uu____67587,FStar_Util.Inl msg) -> FStar_Pervasives_Native.None
         | (uu____67596,FStar_Util.Inr data) ->
             FStar_Pervasives_Native.Some data)
  
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false  in
  fun env  ->
    fun fn  ->
      let load_it uu____67632 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 msg cache_file1 =
          let suppress_warning =
            (FStar_Options.should_verify_file fn) ||
              (FStar_ST.op_Bang already_failed)
             in
          if Prims.op_Negation suppress_warning
          then
            (FStar_ST.op_Colon_Equals already_failed true;
             (let uu____67697 =
                let uu____67698 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____67701 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____67698 uu____67701  in
              let uu____67704 =
                let uu____67710 =
                  FStar_Util.format3
                    "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                    cache_file1 msg fn
                   in
                (FStar_Errors.Warning_CachedFile, uu____67710)  in
              FStar_Errors.log_issue uu____67697 uu____67704))
          else ()  in
        let uu____67716 =
          let uu____67717 =
            let uu____67727 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            load_checked_file_with_tc_result uu____67727 fn cache_file  in
          FStar_All.pipe_right uu____67717 FStar_Pervasives_Native.fst  in
        match uu____67716 with
        | Invalid msg -> (fail1 msg cache_file; FStar_Pervasives_Native.None)
        | Valid (uu____67747,tc_result) ->
            ((let uu____67752 = FStar_Options.debug_any ()  in
              if uu____67752
              then
                FStar_Util.print1
                  "Successfully loaded module from checked file %s\n"
                  cache_file
              else ());
             FStar_Pervasives_Native.Some tc_result)
        | uu____67758 ->
            failwith
              "load_checked_file_tc_result must have an Invalid or Valid entry"
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____67778 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____67778
             msg)
  
let (store_value_to_cache : Prims.string -> checked_file_entry -> unit) =
  fun cache_file  ->
    fun data  -> FStar_Util.save_value_to_file cache_file data
  
let (store_module_to_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env  ->
    fun fn  ->
      fun parsing_data  ->
        fun tc_result  ->
          let uu____67817 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____67820 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____67820)
             in
          if uu____67817
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____67839 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              hash_dependences uu____67839 fn  in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result1 =
                  let uu___864_67859 = tc_result  in
                  {
                    checked_module = (uu___864_67859.checked_module);
                    mii = (uu___864_67859.mii);
                    smt_decls = (uu___864_67859.smt_decls);
                    tc_time = (Prims.parse_int "0");
                    extraction_time = (Prims.parse_int "0")
                  }  in
                let uu____67862 =
                  let uu____67863 = FStar_Util.digest_of_file fn  in
                  (cache_version_number, hashes, uu____67863, parsing_data,
                    tc_result1)
                   in
                store_value_to_cache cache_file uu____67862
            | FStar_Util.Inl msg ->
                let uu____67886 =
                  let uu____67887 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____67890 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____67887 uu____67890  in
                let uu____67893 =
                  let uu____67899 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____67899)  in
                FStar_Errors.log_issue uu____67886 uu____67893
          else ()
  