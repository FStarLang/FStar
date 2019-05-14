open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "11") 
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
  | Unknown 
  | Invalid of Prims.string 
  | Valid of Prims.string 
let (uu___is_Unknown : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____534 -> false
  
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Invalid _0 -> true | uu____547 -> false
  
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee  -> match projectee with | Invalid _0 -> _0 
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Valid _0 -> true | uu____570 -> false
  
let (__proj__Valid__item___0 : tc_result_t -> Prims.string) =
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
        let uu____636 = FStar_Options.find_file fn  in
        match uu____636 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____644 -> fn  in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1  in
      let source_hash = FStar_Util.digest_of_file fn1  in
      let has_interface =
        let uu____654 = FStar_Parser_Dep.interface_of deps module_name  in
        FStar_Option.isSome uu____654  in
      let interface_hash =
        let uu____668 =
          (FStar_Parser_Dep.is_implementation fn1) && has_interface  in
        if uu____668
        then
          let uu____679 =
            let uu____686 =
              let uu____688 =
                let uu____690 =
                  FStar_Parser_Dep.interface_of deps module_name  in
                FStar_Option.get uu____690  in
              FStar_Util.digest_of_file uu____688  in
            ("interface", uu____686)  in
          [uu____679]
        else []  in
      let binary_deps =
        let uu____722 = FStar_Parser_Dep.deps_of deps fn1  in
        FStar_All.pipe_right uu____722
          (FStar_List.filter
             (fun fn2  ->
                let uu____737 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu____740 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     uu____740 = module_name)
                   in
                Prims.op_Negation uu____737))
         in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11  ->
             fun fn2  ->
               let uu____756 = FStar_Parser_Dep.lowercase_module_name fn11
                  in
               let uu____758 = FStar_Parser_Dep.lowercase_module_name fn2  in
               FStar_String.compare uu____756 uu____758) binary_deps
         in
      let rec hash_deps out uu___0_794 =
        match uu___0_794 with
        | [] ->
            FStar_Util.Inr
              (FStar_List.append (("source", source_hash) :: interface_hash)
                 out)
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2  in
            let digest =
              let uu____860 = FStar_Util.smap_try_find mcache cache_fn  in
              match uu____860 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn
                     in
                  ((let uu____873 = FStar_Options.debug_any ()  in
                    if uu____873 then FStar_Util.print1 "%s\\m" msg else ());
                   FStar_Util.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg,uu____882) ->
                  FStar_Util.Inl msg
              | FStar_Pervasives_Native.Some (Valid dig,uu____897) ->
                  FStar_Util.Inr dig
              | FStar_Pervasives_Native.Some (Unknown ,uu____911) ->
                  let uu____922 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name
                     in
                  failwith uu____922
               in
            (match digest with
             | FStar_Util.Inl msg -> FStar_Util.Inl msg
             | FStar_Util.Inr dig ->
                 let uu____961 =
                   let uu____970 =
                     let uu____977 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     (uu____977, dig)  in
                   uu____970 :: out  in
                 hash_deps uu____961 deps1)
         in
      hash_deps [] binary_deps1
  
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn  ->
    fun checked_fn  ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache)  in
      let uu____1014 = FStar_All.pipe_right elt FStar_Util.is_some  in
      if uu____1014
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
           (let entry = FStar_Util.load_value_from_file checked_fn  in
            match entry with
            | FStar_Pervasives_Native.None  ->
                let msg =
                  FStar_Util.format1 "checked file %s is corrupt" checked_fn
                   in
                add_and_return ((Invalid msg), (FStar_Util.Inl msg))
            | FStar_Pervasives_Native.Some
                (vnum,uu____1056,dig,parsing_data,uu____1059) ->
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
                     ((let uu____1124 = FStar_Options.debug_any ()  in
                       if uu____1124
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
                     add_and_return (Unknown, (FStar_Util.Inr parsing_data)))))
  
let (load_checked_file_with_tc_result :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      Prims.string -> (Prims.string,tc_result) FStar_Util.either)
  =
  fun deps  ->
    fun fn  ->
      fun checked_fn  ->
        let load_tc_result fn1 =
          let entry = FStar_Util.load_value_from_file checked_fn  in
          match entry with
          | FStar_Pervasives_Native.Some
              (uu____1289,deps_dig,uu____1291,uu____1292,tc_result) ->
              (deps_dig, tc_result)
          | uu____1361 ->
              failwith
                "Impossible! if first phase of loading was unknown, it should have succeeded"
           in
        let elt = load_checked_file fn checked_fn  in
        match elt with
        | (Invalid msg,uu____1410) -> FStar_Util.Inl msg
        | (Valid uu____1436,uu____1437) ->
            let uu____1449 =
              let uu____1476 = FStar_All.pipe_right checked_fn load_tc_result
                 in
              FStar_All.pipe_right uu____1476 FStar_Pervasives_Native.snd  in
            FStar_All.pipe_right uu____1449
              (fun _1632  -> FStar_Util.Inr _1632)
        | (Unknown ,parsing_data) ->
            let uu____1644 = hash_dependences deps fn  in
            (match uu____1644 with
             | FStar_Util.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data)  in
                 (FStar_Util.smap_add mcache checked_fn elt1;
                  FStar_Util.Inl msg)
             | FStar_Util.Inr deps_dig' ->
                 let uu____1735 =
                   FStar_All.pipe_right checked_fn load_tc_result  in
                 (match uu____1735 with
                  | (deps_dig,tc_result) ->
                      if deps_dig = deps_dig'
                      then
                        let elt1 =
                          let uu____1886 =
                            let uu____1887 =
                              FStar_Util.digest_of_file checked_fn  in
                            Valid uu____1887  in
                          (uu____1886, parsing_data)  in
                        (FStar_Util.smap_add mcache checked_fn elt1;
                         (let validate_iface_cache uu____1900 =
                            let iface1 =
                              let uu____1905 =
                                FStar_All.pipe_right fn
                                  FStar_Parser_Dep.lowercase_module_name
                                 in
                              FStar_All.pipe_right uu____1905
                                (FStar_Parser_Dep.interface_of deps)
                               in
                            match iface1 with
                            | FStar_Pervasives_Native.None  -> ()
                            | FStar_Pervasives_Native.Some iface2 ->
                                (try
                                   (fun uu___136_1922  ->
                                      match () with
                                      | () ->
                                          let iface_checked_fn =
                                            FStar_All.pipe_right iface2
                                              FStar_Parser_Dep.cache_file_name
                                             in
                                          let uu____1927 =
                                            FStar_Util.smap_try_find mcache
                                              iface_checked_fn
                                             in
                                          (match uu____1927 with
                                           | FStar_Pervasives_Native.Some
                                               (Unknown ,parsing_data1) ->
                                               let uu____1941 =
                                                 let uu____1942 =
                                                   let uu____1943 =
                                                     FStar_Util.digest_of_file
                                                       iface_checked_fn
                                                      in
                                                   Valid uu____1943  in
                                                 (uu____1942, parsing_data1)
                                                  in
                                               FStar_Util.smap_add mcache
                                                 iface_checked_fn uu____1941
                                           | uu____1950 -> ())) ()
                                 with | uu___135_1954 -> ())
                             in
                          validate_iface_cache (); FStar_Util.Inr tc_result))
                      else
                        ((let uu____1973 = FStar_Options.debug_any ()  in
                          if uu____1973
                          then
                            ((let uu____1977 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig')
                                 in
                              let uu____1985 =
                                FStar_Parser_Dep.print_digest deps_dig'  in
                              let uu____1987 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig)
                                 in
                              let uu____1995 =
                                FStar_Parser_Dep.print_digest deps_dig  in
                              FStar_Util.print4
                                "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                                uu____1977 uu____1985 uu____1987 uu____1995);
                             if
                               (FStar_List.length deps_dig) =
                                 (FStar_List.length deps_dig')
                             then
                               FStar_List.iter2
                                 (fun uu____2031  ->
                                    fun uu____2032  ->
                                      match (uu____2031, uu____2032) with
                                      | ((x,y),(x',y')) ->
                                          if (x <> x') || (y <> y')
                                          then
                                            let uu____2084 =
                                              FStar_Parser_Dep.print_digest
                                                [(x, y)]
                                               in
                                            let uu____2100 =
                                              FStar_Parser_Dep.print_digest
                                                [(x', y')]
                                               in
                                            FStar_Util.print2
                                              "Differ at: Expected %s\n Got %s\n"
                                              uu____2084 uu____2100
                                          else ()) deps_dig deps_dig'
                             else ())
                          else ());
                         (let msg =
                            FStar_Util.format1
                              "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)"
                              checked_fn
                             in
                          let elt1 = ((Invalid msg), (FStar_Util.Inl msg))
                             in
                          FStar_Util.smap_add mcache checked_fn elt1;
                          FStar_Util.Inl msg))))
  
let (load_parsing_data_from_cache :
  Prims.string ->
    FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
  =
  fun file_name  ->
    let cache_file =
      try
        (fun uu___165_2176  ->
           match () with
           | () ->
               let uu____2180 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____2180
                 (fun _2187  -> FStar_Pervasives_Native.Some _2187)) ()
      with | uu___164_2189 -> FStar_Pervasives_Native.None  in
    match cache_file with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some cache_file1 ->
        let uu____2200 = load_checked_file file_name cache_file1  in
        (match uu____2200 with
         | (uu____2203,FStar_Util.Inl msg) -> FStar_Pervasives_Native.None
         | (uu____2212,FStar_Util.Inr data) ->
             FStar_Pervasives_Native.Some data)
  
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false  in
  fun env  ->
    fun fn  ->
      let load_it uu____2392 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 msg cache_file1 =
          let suppress_warning =
            (FStar_Options.should_verify_file fn) ||
              (FStar_ST.op_Bang already_failed)
             in
          if Prims.op_Negation suppress_warning
          then
            (FStar_ST.op_Colon_Equals already_failed true;
             (let uu____2457 =
                let uu____2458 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____2461 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____2458 uu____2461  in
              let uu____2464 =
                let uu____2470 =
                  FStar_Util.format3
                    "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                    cache_file1 msg fn
                   in
                (FStar_Errors.Warning_CachedFile, uu____2470)  in
              FStar_Errors.log_issue uu____2457 uu____2464))
          else ()  in
        let uu____2476 =
          let uu____2495 =
            FStar_TypeChecker_Env.dep_graph
              env.FStar_Extraction_ML_UEnv.env_tcenv
             in
          load_checked_file_with_tc_result uu____2495 fn cache_file  in
        match uu____2476 with
        | FStar_Util.Inl msg ->
            (fail1 msg cache_file; FStar_Pervasives_Native.None)
        | FStar_Util.Inr tc_result ->
            ((let uu____2570 = FStar_Options.debug_any ()  in
              if uu____2570
              then
                FStar_Util.print1
                  "Successfully loaded module from checked file %s\n"
                  cache_file
              else ());
             FStar_Pervasives_Native.Some tc_result)
        | uu____2589 ->
            failwith
              "load_checked_file_tc_result must have an Invalid or Valid entry"
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____2679 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____2679 msg)
  
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
          let uu____2862 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____2865 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____2865)
             in
          if uu____2862
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____2884 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              hash_dependences uu____2884 fn  in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result1 =
                  let uu___217_2930 = tc_result  in
                  {
                    checked_module = (uu___217_2930.checked_module);
                    mii = (uu___217_2930.mii);
                    smt_decls = (uu___217_2930.smt_decls);
                    tc_time = (Prims.parse_int "0");
                    extraction_time = (Prims.parse_int "0")
                  }  in
                let uu____2959 =
                  let uu____2960 = FStar_Util.digest_of_file fn  in
                  (cache_version_number, hashes, uu____2960, parsing_data,
                    tc_result1)
                   in
                store_value_to_cache cache_file uu____2959
            | FStar_Util.Inl msg ->
                let uu____2996 =
                  let uu____2997 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____3000 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____2997 uu____3000  in
                let uu____3003 =
                  let uu____3009 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____3009)  in
                FStar_Errors.log_issue uu____2996 uu____3003
          else ()
  