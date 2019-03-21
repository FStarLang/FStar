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
    match projectee with | Unknown _0 -> true | uu____226 -> false
  
let (__proj__Unknown__item___0 :
  tc_result_t -> ((Prims.string * Prims.string) Prims.list * tc_result)) =
  fun projectee  -> match projectee with | Unknown _0 -> _0 
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Invalid _0 -> true | uu____282 -> false
  
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee  -> match projectee with | Invalid _0 -> _0 
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Valid _0 -> true | uu____309 -> false
  
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
        let uu____387 = FStar_Options.find_file fn  in
        match uu____387 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____395 -> fn  in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1  in
      let source_hash = FStar_Util.digest_of_file fn1  in
      let has_interface =
        let uu____405 = FStar_Parser_Dep.interface_of deps module_name  in
        FStar_Option.isSome uu____405  in
      let interface_hash =
        let uu____419 =
          (FStar_Parser_Dep.is_implementation fn1) && has_interface  in
        if uu____419
        then
          let uu____430 =
            let uu____437 =
              let uu____439 =
                let uu____441 =
                  FStar_Parser_Dep.interface_of deps module_name  in
                FStar_Option.get uu____441  in
              FStar_Util.digest_of_file uu____439  in
            ("interface", uu____437)  in
          [uu____430]
        else []  in
      let binary_deps =
        let uu____473 = FStar_Parser_Dep.deps_of deps fn1  in
        FStar_All.pipe_right uu____473
          (FStar_List.filter
             (fun fn2  ->
                let uu____488 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu____491 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     uu____491 = module_name)
                   in
                Prims.op_Negation uu____488))
         in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11  ->
             fun fn2  ->
               let uu____507 = FStar_Parser_Dep.lowercase_module_name fn11
                  in
               let uu____509 = FStar_Parser_Dep.lowercase_module_name fn2  in
               FStar_String.compare uu____507 uu____509) binary_deps
         in
      let rec hash_deps out uu___0_545 =
        match uu___0_545 with
        | [] ->
            FStar_Util.Inr
              (FStar_List.append (("source", source_hash) :: interface_hash)
                 out)
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2  in
            let digest =
              let uu____611 = FStar_Util.smap_try_find mcache cache_fn  in
              match uu____611 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn
                     in
                  ((let uu____624 = FStar_Options.debug_any ()  in
                    if uu____624 then FStar_Util.print1 "%s\\m" msg else ());
                   FStar_Util.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg,uu____633) ->
                  FStar_Util.Inl msg
              | FStar_Pervasives_Native.Some
                  (Valid (dig,uu____648),uu____649) -> FStar_Util.Inr dig
              | FStar_Pervasives_Native.Some (Unknown uu____664,uu____665) ->
                  let uu____688 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name
                     in
                  failwith uu____688
               in
            (match digest with
             | FStar_Util.Inl msg -> FStar_Util.Inl msg
             | FStar_Util.Inr dig ->
                 let uu____727 =
                   let uu____736 =
                     let uu____743 =
                       FStar_Parser_Dep.lowercase_module_name fn2  in
                     (uu____743, dig)  in
                   uu____736 :: out  in
                 hash_deps uu____727 deps1)
         in
      hash_deps [] binary_deps1
  
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn  ->
    fun checked_fn  ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache)  in
      let uu____780 = FStar_All.pipe_right elt FStar_Util.is_some  in
      if uu____780
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
           (let uu____809 = FStar_Util.load_value_from_file checked_fn  in
            match uu____809 with
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
                     ((let uu____944 = FStar_Options.debug_any ()  in
                       if uu____944
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
        | (Invalid uu____996,uu____997) -> elt
        | (Valid uu____1009,uu____1010) -> elt
        | (Unknown (deps_dig,tc_result),parsing_data) ->
            let uu____1055 = hash_dependences deps fn  in
            (match uu____1055 with
             | FStar_Util.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data)  in
                 (FStar_Util.smap_add mcache checked_fn elt1; elt1)
             | FStar_Util.Inr deps_dig' ->
                 if deps_dig = deps_dig'
                 then
                   let elt1 =
                     let uu____1133 =
                       let uu____1134 =
                         let uu____1140 =
                           FStar_Util.digest_of_file checked_fn  in
                         (uu____1140, tc_result)  in
                       Valid uu____1134  in
                     (uu____1133, parsing_data)  in
                   (FStar_Util.smap_add mcache checked_fn elt1;
                    (let validate_iface_cache uu____1154 =
                       let iface1 =
                         let uu____1159 =
                           FStar_All.pipe_right fn
                             FStar_Parser_Dep.lowercase_module_name
                            in
                         FStar_All.pipe_right uu____1159
                           (FStar_Parser_Dep.interface_of deps)
                          in
                       match iface1 with
                       | FStar_Pervasives_Native.None  -> ()
                       | FStar_Pervasives_Native.Some iface2 ->
                           (try
                              (fun uu___128_1178  ->
                                 match () with
                                 | () ->
                                     let iface_checked_fn =
                                       FStar_All.pipe_right iface2
                                         FStar_Parser_Dep.cache_file_name
                                        in
                                     let uu____1183 =
                                       FStar_Util.smap_try_find mcache
                                         iface_checked_fn
                                        in
                                     (match uu____1183 with
                                      | FStar_Pervasives_Native.Some
                                          (Unknown
                                           (uu____1186,tc_result1),parsing_data1)
                                          ->
                                          let uu____1215 =
                                            let uu____1216 =
                                              let uu____1217 =
                                                let uu____1223 =
                                                  FStar_Util.digest_of_file
                                                    iface_checked_fn
                                                   in
                                                (uu____1223, tc_result1)  in
                                              Valid uu____1217  in
                                            (uu____1216, parsing_data1)  in
                                          FStar_Util.smap_add mcache
                                            iface_checked_fn uu____1215
                                      | uu____1231 -> ())) ()
                            with | uu___127_1235 -> ())
                        in
                     validate_iface_cache (); elt1))
                 else
                   ((let uu____1240 = FStar_Options.debug_any ()  in
                     if uu____1240
                     then
                       ((let uu____1244 =
                           FStar_Util.string_of_int
                             (FStar_List.length deps_dig')
                            in
                         let uu____1252 =
                           FStar_Parser_Dep.print_digest deps_dig'  in
                         let uu____1254 =
                           FStar_Util.string_of_int
                             (FStar_List.length deps_dig)
                            in
                         let uu____1262 =
                           FStar_Parser_Dep.print_digest deps_dig  in
                         FStar_Util.print4
                           "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                           uu____1244 uu____1252 uu____1254 uu____1262);
                        if
                          (FStar_List.length deps_dig) =
                            (FStar_List.length deps_dig')
                        then
                          FStar_List.iter2
                            (fun uu____1298  ->
                               fun uu____1299  ->
                                 match (uu____1298, uu____1299) with
                                 | ((x,y),(x',y')) ->
                                     if (x <> x') || (y <> y')
                                     then
                                       let uu____1351 =
                                         FStar_Parser_Dep.print_digest
                                           [(x, y)]
                                          in
                                       let uu____1367 =
                                         FStar_Parser_Dep.print_digest
                                           [(x', y')]
                                          in
                                       FStar_Util.print2
                                         "Differ at: Expected %s\n Got %s\n"
                                         uu____1351 uu____1367
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
        (fun uu___160_1429  ->
           match () with
           | () ->
               let uu____1433 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____1433
                 (fun _1440  -> FStar_Pervasives_Native.Some _1440)) ()
      with | uu___159_1442 -> FStar_Pervasives_Native.None  in
    match cache_file with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some cache_file1 ->
        let uu____1453 = load_checked_file file_name cache_file1  in
        (match uu____1453 with
         | (uu____1456,FStar_Util.Inl msg) -> FStar_Pervasives_Native.None
         | (uu____1465,FStar_Util.Inr data) ->
             FStar_Pervasives_Native.Some data)
  
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false  in
  fun env  ->
    fun fn  ->
      let load_it uu____1501 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 msg cache_file1 =
          let suppress_warning =
            (FStar_Options.should_verify_file fn) ||
              (FStar_ST.op_Bang already_failed)
             in
          if Prims.op_Negation suppress_warning
          then
            (FStar_ST.op_Colon_Equals already_failed true;
             (let uu____1566 =
                let uu____1567 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____1570 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____1567 uu____1570  in
              let uu____1573 =
                let uu____1579 =
                  FStar_Util.format3
                    "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                    cache_file1 msg fn
                   in
                (FStar_Errors.Warning_CachedFile, uu____1579)  in
              FStar_Errors.log_issue uu____1566 uu____1573))
          else ()  in
        let uu____1585 =
          let uu____1586 =
            let uu____1596 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            load_checked_file_with_tc_result uu____1596 fn cache_file  in
          FStar_All.pipe_right uu____1586 FStar_Pervasives_Native.fst  in
        match uu____1585 with
        | Invalid msg -> (fail1 msg cache_file; FStar_Pervasives_Native.None)
        | Valid (uu____1616,tc_result) ->
            ((let uu____1621 = FStar_Options.debug_any ()  in
              if uu____1621
              then
                FStar_Util.print1
                  "Successfully loaded module from checked file %s\n"
                  cache_file
              else ());
             FStar_Pervasives_Native.Some tc_result)
        | uu____1627 ->
            failwith
              "load_checked_file_tc_result must have an Invalid or Valid entry"
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____1647 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____1647 msg)
  
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
          let uu____1686 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____1689 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____1689)
             in
          if uu____1686
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____1708 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              hash_dependences uu____1708 fn  in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result1 =
                  let uu___214_1728 = tc_result  in
                  {
                    checked_module = (uu___214_1728.checked_module);
                    mii = (uu___214_1728.mii);
                    smt_decls = (uu___214_1728.smt_decls);
                    tc_time = (Prims.parse_int "0");
                    extraction_time = (Prims.parse_int "0")
                  }  in
                let uu____1731 =
                  let uu____1732 = FStar_Util.digest_of_file fn  in
                  (cache_version_number, hashes, uu____1732, parsing_data,
                    tc_result1)
                   in
                store_value_to_cache cache_file uu____1731
            | FStar_Util.Inl msg ->
                let uu____1755 =
                  let uu____1756 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____1759 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____1756 uu____1759  in
                let uu____1762 =
                  let uu____1768 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____1768)  in
                FStar_Errors.log_issue uu____1755 uu____1762
          else ()
  