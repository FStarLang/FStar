open Prims
let (cache_version_number : Prims.int) = (Prims.of_int (28))
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
  fun projectee ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        checked_module
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} -> mii
let (__proj__Mktc_result__item__smt_decls :
  tc_result ->
    (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
      Prims.list))
  =
  fun projectee ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        smt_decls
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        tc_time
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee ->
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
  fun projectee ->
    match projectee with | { version; digest; parsing_data;_} -> version
let (__proj__Mkchecked_file_entry_stage1__item__digest :
  checked_file_entry_stage1 -> Prims.string) =
  fun projectee ->
    match projectee with | { version; digest; parsing_data;_} -> digest
let (__proj__Mkchecked_file_entry_stage1__item__parsing_data :
  checked_file_entry_stage1 -> FStar_Parser_Dep.parsing_data) =
  fun projectee ->
    match projectee with | { version; digest; parsing_data;_} -> parsing_data
type checked_file_entry_stage2 =
  {
  deps_dig: (Prims.string * Prims.string) Prims.list ;
  tc_res: tc_result }
let (__proj__Mkchecked_file_entry_stage2__item__deps_dig :
  checked_file_entry_stage2 -> (Prims.string * Prims.string) Prims.list) =
  fun projectee -> match projectee with | { deps_dig; tc_res;_} -> deps_dig
let (__proj__Mkchecked_file_entry_stage2__item__tc_res :
  checked_file_entry_stage2 -> tc_result) =
  fun projectee -> match projectee with | { deps_dig; tc_res;_} -> tc_res
type tc_result_t =
  | Unknown 
  | Invalid of Prims.string 
  | Valid of Prims.string 
let (uu___is_Unknown : tc_result_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Unknown -> true | uu____241 -> false
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Invalid _0 -> true | uu____248 -> false
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee -> match projectee with | Invalid _0 -> _0
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Valid _0 -> true | uu____261 -> false
let (__proj__Valid__item___0 : tc_result_t -> Prims.string) =
  fun projectee -> match projectee with | Valid _0 -> _0
type cache_t =
  (tc_result_t * (Prims.string, FStar_Parser_Dep.parsing_data)
    FStar_Util.either)
let (mcache : cache_t FStar_Util.smap) =
  FStar_Util.smap_create (Prims.of_int (50))
let (hash_dependences :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      (Prims.string, (Prims.string * Prims.string) Prims.list)
        FStar_Util.either)
  =
  fun deps ->
    fun fn ->
      let fn1 =
        let uu____309 = FStar_Options.find_file fn in
        match uu____309 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | uu____313 -> fn in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1 in
      let source_hash = FStar_Util.digest_of_file fn1 in
      let has_interface =
        let uu____319 = FStar_Parser_Dep.interface_of deps module_name in
        FStar_Option.isSome uu____319 in
      let interface_checked_file_name =
        let uu____325 =
          (FStar_Parser_Dep.is_implementation fn1) && has_interface in
        if uu____325
        then
          let uu____328 =
            let uu____329 =
              let uu____330 =
                FStar_All.pipe_right module_name
                  (FStar_Parser_Dep.interface_of deps) in
              FStar_All.pipe_right uu____330 FStar_Util.must in
            FStar_All.pipe_right uu____329 FStar_Parser_Dep.cache_file_name in
          FStar_All.pipe_right uu____328
            (fun uu____339 -> FStar_Pervasives_Native.Some uu____339)
        else FStar_Pervasives_Native.None in
      let binary_deps =
        let uu____344 = FStar_Parser_Dep.deps_of deps fn1 in
        FStar_All.pipe_right uu____344
          (FStar_List.filter
             (fun fn2 ->
                let uu____354 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu____356 =
                       FStar_Parser_Dep.lowercase_module_name fn2 in
                     uu____356 = module_name) in
                Prims.op_Negation uu____354)) in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11 ->
             fun fn2 ->
               let uu____366 = FStar_Parser_Dep.lowercase_module_name fn11 in
               let uu____367 = FStar_Parser_Dep.lowercase_module_name fn2 in
               FStar_String.compare uu____366 uu____367) binary_deps in
      let maybe_add_iface_hash out =
        match interface_checked_file_name with
        | FStar_Pervasives_Native.None ->
            FStar_Util.Inr (("source", source_hash) :: out)
        | FStar_Pervasives_Native.Some iface ->
            let uu____417 = FStar_Util.smap_try_find mcache iface in
            (match uu____417 with
             | FStar_Pervasives_Native.None ->
                 let msg =
                   FStar_Util.format1
                     "hash_dependences::the interface checked file %s does not exist\n"
                     iface in
                 ((let uu____432 =
                     FStar_Options.debug_at_level_no_module
                       (FStar_Options.Other "CheckedFiles") in
                   if uu____432 then FStar_Util.print1 "%s\n" msg else ());
                  FStar_Util.Inl msg)
             | FStar_Pervasives_Native.Some (Invalid msg, uu____441) ->
                 FStar_Util.Inl msg
             | FStar_Pervasives_Native.Some (Valid h, uu____457) ->
                 FStar_Util.Inr (("source", source_hash) :: ("interface", h)
                   :: out)
             | FStar_Pervasives_Native.Some (Unknown, uu____480) ->
                 let uu____489 =
                   FStar_Util.format1
                     "Impossible: unknown entry in the mcache for interface %s\n"
                     iface in
                 failwith uu____489) in
      let rec hash_deps out uu___0_528 =
        match uu___0_528 with
        | [] -> maybe_add_iface_hash out
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2 in
            let digest =
              let uu____557 = FStar_Util.smap_try_find mcache cache_fn in
              match uu____557 with
              | FStar_Pervasives_Native.None ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn in
                  ((let uu____566 =
                      FStar_Options.debug_at_level_no_module
                        (FStar_Options.Other "CheckedFiles") in
                    if uu____566 then FStar_Util.print1 "%s\n" msg else ());
                   FStar_Util.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg, uu____569) ->
                  FStar_Util.Inl msg
              | FStar_Pervasives_Native.Some (Valid dig, uu____579) ->
                  FStar_Util.Inr dig
              | FStar_Pervasives_Native.Some (Unknown, uu____588) ->
                  let uu____597 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name in
                  failwith uu____597 in
            (match digest with
             | FStar_Util.Inl msg -> FStar_Util.Inl msg
             | FStar_Util.Inr dig ->
                 let uu____620 =
                   let uu____627 =
                     let uu____632 =
                       FStar_Parser_Dep.lowercase_module_name fn2 in
                     (uu____632, dig) in
                   uu____627 :: out in
                 hash_deps uu____620 deps1) in
      hash_deps [] binary_deps1
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn ->
    fun checked_fn ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache) in
      let uu____656 = FStar_All.pipe_right elt FStar_Util.is_some in
      if uu____656
      then FStar_All.pipe_right elt FStar_Util.must
      else
        (let add_and_return elt1 =
           FStar_Util.smap_add mcache checked_fn elt1; elt1 in
         if Prims.op_Negation (FStar_Util.file_exists checked_fn)
         then
           let msg =
             FStar_Util.format1 "checked file %s does not exist" checked_fn in
           add_and_return ((Invalid msg), (FStar_Util.Inl msg))
         else
           (let entry = FStar_Util.load_value_from_file checked_fn in
            match entry with
            | FStar_Pervasives_Native.None ->
                let msg =
                  FStar_Util.format1 "checked file %s is corrupt" checked_fn in
                add_and_return ((Invalid msg), (FStar_Util.Inl msg))
            | FStar_Pervasives_Native.Some x ->
                if x.version <> cache_version_number
                then
                  let msg =
                    FStar_Util.format1
                      "checked file %s has incorrect version" checked_fn in
                  add_and_return ((Invalid msg), (FStar_Util.Inl msg))
                else
                  (let current_digest = FStar_Util.digest_of_file fn in
                   if x.digest <> current_digest
                   then
                     ((let uu____692 =
                         FStar_Options.debug_at_level_no_module
                           (FStar_Options.Other "CheckedFiles") in
                       if uu____692
                       then
                         FStar_Util.print4
                           "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n"
                           checked_fn fn current_digest x.digest
                       else ());
                      (let msg =
                         FStar_Util.format2
                           "checked file %s is stale (digest mismatch for %s)"
                           checked_fn fn in
                       add_and_return ((Invalid msg), (FStar_Util.Inl msg))))
                   else
                     add_and_return
                       (Unknown, (FStar_Util.Inr (x.parsing_data))))))
let (load_checked_file_with_tc_result :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      Prims.string -> (Prims.string, tc_result) FStar_Util.either)
  =
  fun deps ->
    fun fn ->
      fun checked_fn ->
        let load_tc_result fn1 =
          let entry = FStar_Util.load_2values_from_file checked_fn in
          match entry with
          | FStar_Pervasives_Native.Some (uu____770, s2) ->
              ((s2.deps_dig), (s2.tc_res))
          | uu____782 ->
              failwith
                "Impossible! if first phase of loading was unknown, it should have succeeded" in
        let elt = load_checked_file fn checked_fn in
        match elt with
        | (Invalid msg, uu____805) -> FStar_Util.Inl msg
        | (Valid uu____814, uu____815) ->
            let uu____824 =
              let uu____825 = FStar_All.pipe_right checked_fn load_tc_result in
              FStar_All.pipe_right uu____825 FStar_Pervasives_Native.snd in
            FStar_All.pipe_right uu____824
              (fun uu____866 -> FStar_Util.Inr uu____866)
        | (Unknown, parsing_data) ->
            let uu____876 = hash_dependences deps fn in
            (match uu____876 with
             | FStar_Util.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data) in
                 (FStar_Util.smap_add mcache checked_fn elt1;
                  FStar_Util.Inl msg)
             | FStar_Util.Inr deps_dig' ->
                 let uu____925 =
                   FStar_All.pipe_right checked_fn load_tc_result in
                 (match uu____925 with
                  | (deps_dig, tc_result1) ->
                      if deps_dig = deps_dig'
                      then
                        let elt1 =
                          let uu____983 =
                            let uu____984 =
                              FStar_Util.digest_of_file checked_fn in
                            Valid uu____984 in
                          (uu____983, parsing_data) in
                        (FStar_Util.smap_add mcache checked_fn elt1;
                         (let validate_iface_cache uu____995 =
                            let iface =
                              let uu____999 =
                                FStar_All.pipe_right fn
                                  FStar_Parser_Dep.lowercase_module_name in
                              FStar_All.pipe_right uu____999
                                (FStar_Parser_Dep.interface_of deps) in
                            match iface with
                            | FStar_Pervasives_Native.None -> ()
                            | FStar_Pervasives_Native.Some iface1 ->
                                (try
                                   (fun uu___166_1008 ->
                                      match () with
                                      | () ->
                                          let iface_checked_fn =
                                            FStar_All.pipe_right iface1
                                              FStar_Parser_Dep.cache_file_name in
                                          let uu____1010 =
                                            FStar_Util.smap_try_find mcache
                                              iface_checked_fn in
                                          (match uu____1010 with
                                           | FStar_Pervasives_Native.Some
                                               (Unknown, parsing_data1) ->
                                               let uu____1022 =
                                                 let uu____1023 =
                                                   let uu____1024 =
                                                     FStar_Util.digest_of_file
                                                       iface_checked_fn in
                                                   Valid uu____1024 in
                                                 (uu____1023, parsing_data1) in
                                               FStar_Util.smap_add mcache
                                                 iface_checked_fn uu____1022
                                           | uu____1029 -> ())) ()
                                 with | uu___165_1033 -> ()) in
                          validate_iface_cache (); FStar_Util.Inr tc_result1))
                      else
                        ((let uu____1037 =
                            FStar_Options.debug_at_level_no_module
                              (FStar_Options.Other "CheckedFiles") in
                          if uu____1037
                          then
                            ((let uu____1039 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig') in
                              let uu____1044 =
                                FStar_Parser_Dep.print_digest deps_dig' in
                              let uu____1045 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig) in
                              let uu____1050 =
                                FStar_Parser_Dep.print_digest deps_dig in
                              FStar_Util.print4
                                "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                                uu____1039 uu____1044 uu____1045 uu____1050);
                             if
                               (FStar_List.length deps_dig) =
                                 (FStar_List.length deps_dig')
                             then
                               FStar_List.iter2
                                 (fun uu____1075 ->
                                    fun uu____1076 ->
                                      match (uu____1075, uu____1076) with
                                      | ((x, y), (x', y')) ->
                                          if (x <> x') || (y <> y')
                                          then
                                            let uu____1105 =
                                              FStar_Parser_Dep.print_digest
                                                [(x, y)] in
                                            let uu____1114 =
                                              FStar_Parser_Dep.print_digest
                                                [(x', y')] in
                                            FStar_Util.print2
                                              "Differ at: Expected %s\n Got %s\n"
                                              uu____1105 uu____1114
                                          else ()) deps_dig deps_dig'
                             else ())
                          else ());
                         (let msg =
                            FStar_Util.format1
                              "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)"
                              checked_fn in
                          let elt1 = ((Invalid msg), (FStar_Util.Inl msg)) in
                          FStar_Util.smap_add mcache checked_fn elt1;
                          FStar_Util.Inl msg))))
let (load_parsing_data_from_cache :
  Prims.string ->
    FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
  =
  fun file_name ->
    let cache_file =
      try
        (fun uu___195_1155 ->
           match () with
           | () ->
               let uu____1158 = FStar_Parser_Dep.cache_file_name file_name in
               FStar_All.pipe_right uu____1158
                 (fun uu____1161 -> FStar_Pervasives_Native.Some uu____1161))
          ()
      with | uu___194_1163 -> FStar_Pervasives_Native.None in
    match cache_file with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some cache_file1 ->
        let uu____1169 = load_checked_file file_name cache_file1 in
        (match uu____1169 with
         | (uu____1172, FStar_Util.Inl msg) -> FStar_Pervasives_Native.None
         | (uu____1178, FStar_Util.Inr data) ->
             FStar_Pervasives_Native.Some data)
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false in
  fun env ->
    fun fn ->
      let load_it fn1 uu____1211 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn1 in
        let fail msg cache_file1 =
          let suppress_warning =
            (FStar_Options.should_verify_file fn1) ||
              (FStar_ST.op_Bang already_failed) in
          if Prims.op_Negation suppress_warning
          then
            (FStar_ST.op_Colon_Equals already_failed true;
             (let uu____1238 =
                let uu____1239 =
                  FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                let uu____1240 =
                  FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                FStar_Range.mk_range fn1 uu____1239 uu____1240 in
              let uu____1241 =
                let uu____1246 =
                  FStar_Util.format3
                    "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                    cache_file1 msg fn1 in
                (FStar_Errors.Warning_CachedFile, uu____1246) in
              FStar_Errors.log_issue uu____1238 uu____1241))
          else () in
        let uu____1248 =
          let uu____1253 =
            let uu____1254 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.dep_graph uu____1254 in
          load_checked_file_with_tc_result uu____1253 fn1 cache_file in
        match uu____1248 with
        | FStar_Util.Inl msg ->
            (fail msg cache_file; FStar_Pervasives_Native.None)
        | FStar_Util.Inr tc_result1 ->
            ((let uu____1261 =
                FStar_Options.debug_at_level_no_module
                  (FStar_Options.Other "CheckedFiles") in
              if uu____1261
              then
                FStar_Util.print1
                  "Successfully loaded module from checked file %s\n"
                  cache_file
              else ());
             FStar_Pervasives_Native.Some tc_result1) in
      let load_with_profiling fn1 =
        FStar_Profiling.profile (load_it fn1) FStar_Pervasives_Native.None
          "FStar.CheckedFiles" in
      let i_fn_opt =
        let uu____1276 =
          let uu____1277 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
          FStar_TypeChecker_Env.dep_graph uu____1277 in
        let uu____1278 = FStar_Parser_Dep.lowercase_module_name fn in
        FStar_Parser_Dep.interface_of uu____1276 uu____1278 in
      let uu____1279 =
        (FStar_Parser_Dep.is_implementation fn) &&
          (FStar_All.pipe_right i_fn_opt FStar_Util.is_some) in
      if uu____1279
      then
        let i_fn = FStar_All.pipe_right i_fn_opt FStar_Util.must in
        let i_tc = load_with_profiling i_fn in
        match i_tc with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some uu____1292 -> load_with_profiling fn
      else load_with_profiling fn
let (store_values_to_cache :
  Prims.string ->
    checked_file_entry_stage1 -> checked_file_entry_stage2 -> unit)
  =
  fun cache_file ->
    fun stage1 ->
      fun stage2 -> FStar_Util.save_2values_to_file cache_file stage1 stage2
let (store_module_to_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env ->
    fun fn ->
      fun parsing_data ->
        fun tc_result1 ->
          let uu____1329 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____1331 = FStar_Options.cache_off () in
               Prims.op_Negation uu____1331) in
          if uu____1329
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn in
            let digest =
              let uu____1344 =
                let uu____1345 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                FStar_TypeChecker_Env.dep_graph uu____1345 in
              hash_dependences uu____1344 fn in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result2 =
                  let uu___254_1360 = tc_result1 in
                  {
                    checked_module = (uu___254_1360.checked_module);
                    mii = (uu___254_1360.mii);
                    smt_decls = (uu___254_1360.smt_decls);
                    tc_time = Prims.int_zero;
                    extraction_time = Prims.int_zero
                  } in
                let stage1 =
                  let uu____1362 = FStar_Util.digest_of_file fn in
                  {
                    version = cache_version_number;
                    digest = uu____1362;
                    parsing_data
                  } in
                let stage2 = { deps_dig = hashes; tc_res = tc_result2 } in
                store_values_to_cache cache_file stage1 stage2
            | FStar_Util.Inl msg ->
                let uu____1371 =
                  let uu____1372 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                  let uu____1373 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                  FStar_Range.mk_range fn uu____1372 uu____1373 in
                let uu____1374 =
                  let uu____1379 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg in
                  (FStar_Errors.Warning_FileNotWritten, uu____1379) in
                FStar_Errors.log_issue uu____1371 uu____1374
          else ()