open Prims
let (cache_version_number : Prims.int) = (Prims.of_int (15)) 
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
  
type checked_file_entry_stage1 =
  {
  version: Prims.int ;
  digest: Prims.string ;
  parsing_data: FStar_Parser_Dep.parsing_data }
let (__proj__Mkchecked_file_entry_stage1__item__version :
  checked_file_entry_stage1 -> Prims.int) =
  fun projectee  ->
    match projectee with | { version; digest; parsing_data;_} -> version
  
let (__proj__Mkchecked_file_entry_stage1__item__digest :
  checked_file_entry_stage1 -> Prims.string) =
  fun projectee  ->
    match projectee with | { version; digest; parsing_data;_} -> digest
  
let (__proj__Mkchecked_file_entry_stage1__item__parsing_data :
  checked_file_entry_stage1 -> FStar_Parser_Dep.parsing_data) =
  fun projectee  ->
    match projectee with | { version; digest; parsing_data;_} -> parsing_data
  
type checked_file_entry_stage2 =
  {
  deps_dig: (Prims.string * Prims.string) Prims.list ;
  tc_res: tc_result }
let (__proj__Mkchecked_file_entry_stage2__item__deps_dig :
  checked_file_entry_stage2 -> (Prims.string * Prims.string) Prims.list) =
  fun projectee  -> match projectee with | { deps_dig; tc_res;_} -> deps_dig 
let (__proj__Mkchecked_file_entry_stage2__item__tc_res :
  checked_file_entry_stage2 -> tc_result) =
  fun projectee  -> match projectee with | { deps_dig; tc_res;_} -> tc_res 
type tc_result_t =
  | Unknown 
  | Invalid of Prims.string 
  | Valid of Prims.string 
let (uu___is_Unknown : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____297 -> false
  
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Invalid _0 -> true | uu____310 -> false
  
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee  -> match projectee with | Invalid _0 -> _0 
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Valid _0 -> true | uu____333 -> false
  
let (__proj__Valid__item___0 : tc_result_t -> Prims.string) =
  fun projectee  -> match projectee with | Valid _0 -> _0 
type cache_t =
  (tc_result_t * (Prims.string,FStar_Parser_Dep.parsing_data)
    FStar_Util.either)
let (mcache : cache_t FStar_Util.smap) =
  FStar_Util.smap_create (Prims.of_int (50)) 
let (hash_dependences :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      (Prims.string,(Prims.string * Prims.string) Prims.list)
        FStar_Util.either)
  =
  fun deps  ->
    fun fn  ->
      let fn1 =
        let uu____399 = FStar_Options.find_file fn  in
        match uu____399 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____407 -> fn  in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1  in
      let source_hash = FStar_Util.digest_of_file fn1  in
      let has_interface =
        let uu____417 = FStar_Parser_Dep.interface_of deps module_name  in
        FStar_Option.isSome uu____417  in
      let interface_hash =
        let uu____431 =
          (FStar_Parser_Dep.is_implementation fn1) && has_interface  in
        if uu____431
        then
          let uu____442 =
            let uu____449 =
              let uu____451 =
                let uu____453 =
                  FStar_Parser_Dep.interface_of deps module_name  in
                FStar_Option.get uu____453  in
              FStar_Util.digest_of_file uu____451  in
            ("interface", uu____449)  in
          [uu____442]
        else []  in
      let binary_deps =
        let uu____485 = FStar_Parser_Dep.deps_of deps fn1  in
        FStar_All.pipe_right uu____485
          (FStar_List.filter
             (fun fn2  ->
                let uu____500 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu____503 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     uu____503 = module_name)
                   in
                Prims.op_Negation uu____500))
         in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11  ->
             fun fn2  ->
               let uu____519 = FStar_Parser_Dep.lowercase_module_name fn11
                  in
               let uu____521 = FStar_Parser_Dep.lowercase_module_name fn2  in
               FStar_String.compare uu____519 uu____521) binary_deps
         in
      let rec hash_deps out uu___0_557 =
        match uu___0_557 with
        | [] ->
            FStar_Util.Inr
              (FStar_List.append (("source", source_hash) :: interface_hash)
                 out)
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2  in
            let digest =
              let uu____623 = FStar_Util.smap_try_find mcache cache_fn  in
              match uu____623 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn
                     in
                  ((let uu____636 = FStar_Options.debug_any ()  in
                    if uu____636 then FStar_Util.print1 "%s\\m" msg else ());
                   FStar_Util.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg,uu____645) ->
                  FStar_Util.Inl msg
              | FStar_Pervasives_Native.Some (Valid dig,uu____660) ->
                  FStar_Util.Inr dig
              | FStar_Pervasives_Native.Some (Unknown ,uu____674) ->
                  let uu____685 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name
                     in
                  failwith uu____685
               in
            (match digest with
             | FStar_Util.Inl msg -> FStar_Util.Inl msg
             | FStar_Util.Inr dig ->
                 let uu____724 =
                   let uu____733 =
                     let uu____740 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     (uu____740, dig)  in
                   uu____733 :: out  in
                 hash_deps uu____724 deps1)
         in
      hash_deps [] binary_deps1
  
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn  ->
    fun checked_fn  ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache)  in
      let uu____777 = FStar_All.pipe_right elt FStar_Util.is_some  in
      if uu____777
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
            | FStar_Pervasives_Native.Some x ->
                if x.version <> cache_version_number
                then
                  let msg =
                    FStar_Util.format1
                      "checked file %s has incorrect version" checked_fn
                     in
                  add_and_return ((Invalid msg), (FStar_Util.Inl msg))
                else
                  (let current_digest = FStar_Util.digest_of_file fn  in
                   if x.digest <> current_digest
                   then
                     ((let uu____837 = FStar_Options.debug_any ()  in
                       if uu____837
                       then
                         FStar_Util.print4
                           "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n"
                           checked_fn fn current_digest x.digest
                       else ());
                      (let msg =
                         FStar_Util.format2
                           "checked file %s is stale (digest mismatch for %s)"
                           checked_fn fn
                          in
                       add_and_return ((Invalid msg), (FStar_Util.Inl msg))))
                   else
                     add_and_return
                       (Unknown, (FStar_Util.Inr (x.parsing_data))))))
  
let (load_checked_file_with_tc_result :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      Prims.string -> (Prims.string,tc_result) FStar_Util.either)
  =
  fun deps  ->
    fun fn  ->
      fun checked_fn  ->
        let load_tc_result fn1 =
          let entry = FStar_Util.load_2values_from_file checked_fn  in
          match entry with
          | FStar_Pervasives_Native.Some (uu____941,s2) ->
              ((s2.deps_dig), (s2.tc_res))
          | uu____955 ->
              failwith
                "Impossible! if first phase of loading was unknown, it should have succeeded"
           in
        let elt = load_checked_file fn checked_fn  in
        match elt with
        | (Invalid msg,uu____982) -> FStar_Util.Inl msg
        | (Valid uu____995,uu____996) ->
            let uu____1008 =
              let uu____1009 = FStar_All.pipe_right checked_fn load_tc_result
                 in
              FStar_All.pipe_right uu____1009 FStar_Pervasives_Native.snd  in
            FStar_All.pipe_right uu____1008
              (fun _1061  -> FStar_Util.Inr _1061)
        | (Unknown ,parsing_data) ->
            let uu____1073 = hash_dependences deps fn  in
            (match uu____1073 with
             | FStar_Util.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data)  in
                 (FStar_Util.smap_add mcache checked_fn elt1;
                  FStar_Util.Inl msg)
             | FStar_Util.Inr deps_dig' ->
                 let uu____1138 =
                   FStar_All.pipe_right checked_fn load_tc_result  in
                 (match uu____1138 with
                  | (deps_dig,tc_result) ->
                      if deps_dig = deps_dig'
                      then
                        let elt1 =
                          let uu____1211 =
                            let uu____1212 =
                              FStar_Util.digest_of_file checked_fn  in
                            Valid uu____1212  in
                          (uu____1211, parsing_data)  in
                        (FStar_Util.smap_add mcache checked_fn elt1;
                         (let validate_iface_cache uu____1225 =
                            let iface1 =
                              let uu____1230 =
                                FStar_All.pipe_right fn
                                  FStar_Parser_Dep.lowercase_module_name
                                 in
                              FStar_All.pipe_right uu____1230
                                (FStar_Parser_Dep.interface_of deps)
                               in
                            match iface1 with
                            | FStar_Pervasives_Native.None  -> ()
                            | FStar_Pervasives_Native.Some iface2 ->
                                (try
                                   (fun uu___143_1247  ->
                                      match () with
                                      | () ->
                                          let iface_checked_fn =
                                            FStar_All.pipe_right iface2
                                              FStar_Parser_Dep.cache_file_name
                                             in
                                          let uu____1252 =
                                            FStar_Util.smap_try_find mcache
                                              iface_checked_fn
                                             in
                                          (match uu____1252 with
                                           | FStar_Pervasives_Native.Some
                                               (Unknown ,parsing_data1) ->
                                               let uu____1266 =
                                                 let uu____1267 =
                                                   let uu____1268 =
                                                     FStar_Util.digest_of_file
                                                       iface_checked_fn
                                                      in
                                                   Valid uu____1268  in
                                                 (uu____1267, parsing_data1)
                                                  in
                                               FStar_Util.smap_add mcache
                                                 iface_checked_fn uu____1266
                                           | uu____1275 -> ())) ()
                                 with | uu___142_1279 -> ())
                             in
                          validate_iface_cache (); FStar_Util.Inr tc_result))
                      else
                        ((let uu____1285 = FStar_Options.debug_any ()  in
                          if uu____1285
                          then
                            ((let uu____1289 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig')
                                 in
                              let uu____1297 =
                                FStar_Parser_Dep.print_digest deps_dig'  in
                              let uu____1299 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig)
                                 in
                              let uu____1307 =
                                FStar_Parser_Dep.print_digest deps_dig  in
                              FStar_Util.print4
                                "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                                uu____1289 uu____1297 uu____1299 uu____1307);
                             if
                               (FStar_List.length deps_dig) =
                                 (FStar_List.length deps_dig')
                             then
                               FStar_List.iter2
                                 (fun uu____1343  ->
                                    fun uu____1344  ->
                                      match (uu____1343, uu____1344) with
                                      | ((x,y),(x',y')) ->
                                          if (x <> x') || (y <> y')
                                          then
                                            let uu____1396 =
                                              FStar_Parser_Dep.print_digest
                                                [(x, y)]
                                               in
                                            let uu____1412 =
                                              FStar_Parser_Dep.print_digest
                                                [(x', y')]
                                               in
                                            FStar_Util.print2
                                              "Differ at: Expected %s\n Got %s\n"
                                              uu____1396 uu____1412
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
        (fun uu___172_1475  ->
           match () with
           | () ->
               let uu____1479 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____1479
                 (fun _1486  -> FStar_Pervasives_Native.Some _1486)) ()
      with | uu___171_1488 -> FStar_Pervasives_Native.None  in
    match cache_file with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some cache_file1 ->
        let uu____1499 = load_checked_file file_name cache_file1  in
        (match uu____1499 with
         | (uu____1502,FStar_Util.Inl msg) -> FStar_Pervasives_Native.None
         | (uu____1511,FStar_Util.Inr data) ->
             FStar_Pervasives_Native.Some data)
  
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false  in
  fun env  ->
    fun fn  ->
      let load_it uu____1547 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 msg cache_file1 =
          let suppress_warning =
            (FStar_Options.should_verify_file fn) ||
              (FStar_ST.op_Bang already_failed)
             in
          if Prims.op_Negation suppress_warning
          then
            (FStar_ST.op_Colon_Equals already_failed true;
             (let uu____1612 =
                let uu____1613 =
                  FStar_Range.mk_pos Prims.int_zero Prims.int_zero  in
                let uu____1616 =
                  FStar_Range.mk_pos Prims.int_zero Prims.int_zero  in
                FStar_Range.mk_range fn uu____1613 uu____1616  in
              let uu____1619 =
                let uu____1625 =
                  FStar_Util.format3
                    "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                    cache_file1 msg fn
                   in
                (FStar_Errors.Warning_CachedFile, uu____1625)  in
              FStar_Errors.log_issue uu____1612 uu____1619))
          else ()  in
        let uu____1631 =
          let uu____1637 =
            FStar_TypeChecker_Env.dep_graph
              env.FStar_Extraction_ML_UEnv.env_tcenv
             in
          load_checked_file_with_tc_result uu____1637 fn cache_file  in
        match uu____1631 with
        | FStar_Util.Inl msg ->
            (fail1 msg cache_file; FStar_Pervasives_Native.None)
        | FStar_Util.Inr tc_result ->
            ((let uu____1647 = FStar_Options.debug_any ()  in
              if uu____1647
              then
                FStar_Util.print1
                  "Successfully loaded module from checked file %s\n"
                  cache_file
              else ());
             FStar_Pervasives_Native.Some tc_result)
         in
      FStar_Profiling.profile load_it FStar_Pervasives_Native.None
        "FStar.CheckedFiles"
  
let (store_values_to_cache :
  Prims.string ->
    checked_file_entry_stage1 -> checked_file_entry_stage2 -> unit)
  =
  fun cache_file  ->
    fun stage1  ->
      fun stage2  -> FStar_Util.save_2values_to_file cache_file stage1 stage2
  
let (store_module_to_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env  ->
    fun fn  ->
      fun parsing_data  ->
        fun tc_result  ->
          let uu____1698 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____1701 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____1701)
             in
          if uu____1698
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____1720 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              hash_dependences uu____1720 fn  in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result1 =
                  let uu___221_1740 = tc_result  in
                  {
                    checked_module = (uu___221_1740.checked_module);
                    mii = (uu___221_1740.mii);
                    smt_decls = (uu___221_1740.smt_decls);
                    tc_time = Prims.int_zero;
                    extraction_time = Prims.int_zero
                  }  in
                let stage1 =
                  let uu____1744 = FStar_Util.digest_of_file fn  in
                  {
                    version = cache_version_number;
                    digest = uu____1744;
                    parsing_data
                  }  in
                let stage2 = { deps_dig = hashes; tc_res = tc_result1 }  in
                store_values_to_cache cache_file stage1 stage2
            | FStar_Util.Inl msg ->
                let uu____1758 =
                  let uu____1759 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero  in
                  let uu____1762 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero  in
                  FStar_Range.mk_range fn uu____1759 uu____1762  in
                let uu____1765 =
                  let uu____1771 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____1771)  in
                FStar_Errors.log_issue uu____1758 uu____1765
          else ()
  