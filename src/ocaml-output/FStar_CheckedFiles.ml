open Prims
let (cache_version_number : Prims.int) = (Prims.of_int (36))
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
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (uu___is_Invalid : tc_result_t -> Prims.bool) =
  fun projectee -> match projectee with | Invalid _0 -> true | uu___ -> false
let (__proj__Invalid__item___0 : tc_result_t -> Prims.string) =
  fun projectee -> match projectee with | Invalid _0 -> _0
let (uu___is_Valid : tc_result_t -> Prims.bool) =
  fun projectee -> match projectee with | Valid _0 -> true | uu___ -> false
let (__proj__Valid__item___0 : tc_result_t -> Prims.string) =
  fun projectee -> match projectee with | Valid _0 -> _0
type cache_t =
  (tc_result_t * (Prims.string, FStar_Parser_Dep.parsing_data)
    FStar_Pervasives.either)
let (mcache : cache_t FStar_Util.smap) =
  FStar_Util.smap_create (Prims.of_int (50))
let (hash_dependences :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      (Prims.string, (Prims.string * Prims.string) Prims.list)
        FStar_Pervasives.either)
  =
  fun deps ->
    fun fn ->
      let fn1 =
        let uu___ = FStar_Options.find_file fn in
        match uu___ with
        | FStar_Pervasives_Native.Some fn2 -> fn2
        | uu___1 -> fn in
      let module_name = FStar_Parser_Dep.lowercase_module_name fn1 in
      let source_hash = FStar_Util.digest_of_file fn1 in
      let has_interface =
        let uu___ = FStar_Parser_Dep.interface_of deps module_name in
        FStar_Option.isSome uu___ in
      let interface_checked_file_name =
        let uu___ = (FStar_Parser_Dep.is_implementation fn1) && has_interface in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_All.pipe_right module_name
                  (FStar_Parser_Dep.interface_of deps) in
              FStar_All.pipe_right uu___3 FStar_Util.must in
            FStar_All.pipe_right uu___2 FStar_Parser_Dep.cache_file_name in
          FStar_All.pipe_right uu___1
            (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
        else FStar_Pervasives_Native.None in
      let binary_deps =
        let uu___ = FStar_Parser_Dep.deps_of deps fn1 in
        FStar_All.pipe_right uu___
          (FStar_List.filter
             (fun fn2 ->
                let uu___1 =
                  (FStar_Parser_Dep.is_interface fn2) &&
                    (let uu___2 = FStar_Parser_Dep.lowercase_module_name fn2 in
                     uu___2 = module_name) in
                Prims.op_Negation uu___1)) in
      let binary_deps1 =
        FStar_List.sortWith
          (fun fn11 ->
             fun fn2 ->
               let uu___ = FStar_Parser_Dep.lowercase_module_name fn11 in
               let uu___1 = FStar_Parser_Dep.lowercase_module_name fn2 in
               FStar_String.compare uu___ uu___1) binary_deps in
      let maybe_add_iface_hash out =
        match interface_checked_file_name with
        | FStar_Pervasives_Native.None ->
            FStar_Pervasives.Inr (("source", source_hash) :: out)
        | FStar_Pervasives_Native.Some iface ->
            let uu___ = FStar_Util.smap_try_find mcache iface in
            (match uu___ with
             | FStar_Pervasives_Native.None ->
                 let msg =
                   FStar_Util.format1
                     "hash_dependences::the interface checked file %s does not exist\n"
                     iface in
                 ((let uu___2 =
                     FStar_Options.debug_at_level_no_module
                       (FStar_Options.Other "CheckedFiles") in
                   if uu___2 then FStar_Util.print1 "%s\n" msg else ());
                  FStar_Pervasives.Inl msg)
             | FStar_Pervasives_Native.Some (Invalid msg, uu___1) ->
                 FStar_Pervasives.Inl msg
             | FStar_Pervasives_Native.Some (Valid h, uu___1) ->
                 FStar_Pervasives.Inr (("source", source_hash) ::
                   ("interface", h) :: out)
             | FStar_Pervasives_Native.Some (Unknown, uu___1) ->
                 let uu___2 =
                   FStar_Util.format1
                     "Impossible: unknown entry in the mcache for interface %s\n"
                     iface in
                 failwith uu___2) in
      let rec hash_deps out uu___ =
        match uu___ with
        | [] -> maybe_add_iface_hash out
        | fn2::deps1 ->
            let cache_fn = FStar_Parser_Dep.cache_file_name fn2 in
            let digest =
              let uu___1 = FStar_Util.smap_try_find mcache cache_fn in
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  let msg =
                    FStar_Util.format2
                      "For dependency %s, cache file %s is not loaded" fn2
                      cache_fn in
                  ((let uu___3 =
                      FStar_Options.debug_at_level_no_module
                        (FStar_Options.Other "CheckedFiles") in
                    if uu___3 then FStar_Util.print1 "%s\n" msg else ());
                   FStar_Pervasives.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg, uu___2) ->
                  FStar_Pervasives.Inl msg
              | FStar_Pervasives_Native.Some (Valid dig, uu___2) ->
                  FStar_Pervasives.Inr dig
              | FStar_Pervasives_Native.Some (Unknown, uu___2) ->
                  let uu___3 =
                    FStar_Util.format2
                      "Impossible: unknown entry in the cache for dependence %s of module %s"
                      fn2 module_name in
                  failwith uu___3 in
            (match digest with
             | FStar_Pervasives.Inl msg -> FStar_Pervasives.Inl msg
             | FStar_Pervasives.Inr dig ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Parser_Dep.lowercase_module_name fn2 in
                     (uu___3, dig) in
                   uu___2 :: out in
                 hash_deps uu___1 deps1) in
      hash_deps [] binary_deps1
let (load_checked_file : Prims.string -> Prims.string -> cache_t) =
  fun fn ->
    fun checked_fn ->
      let elt =
        FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache) in
      let uu___ = FStar_All.pipe_right elt FStar_Util.is_some in
      if uu___
      then FStar_All.pipe_right elt FStar_Util.must
      else
        (let add_and_return elt1 =
           FStar_Util.smap_add mcache checked_fn elt1; elt1 in
         if Prims.op_Negation (FStar_Util.file_exists checked_fn)
         then
           let msg =
             FStar_Util.format1 "checked file %s does not exist" checked_fn in
           add_and_return ((Invalid msg), (FStar_Pervasives.Inl msg))
         else
           (let entry = FStar_Util.load_value_from_file checked_fn in
            match entry with
            | FStar_Pervasives_Native.None ->
                let msg =
                  FStar_Util.format1 "checked file %s is corrupt" checked_fn in
                add_and_return ((Invalid msg), (FStar_Pervasives.Inl msg))
            | FStar_Pervasives_Native.Some x ->
                if x.version <> cache_version_number
                then
                  let msg =
                    FStar_Util.format1
                      "checked file %s has incorrect version" checked_fn in
                  add_and_return ((Invalid msg), (FStar_Pervasives.Inl msg))
                else
                  (let current_digest = FStar_Util.digest_of_file fn in
                   if x.digest <> current_digest
                   then
                     ((let uu___5 =
                         FStar_Options.debug_at_level_no_module
                           (FStar_Options.Other "CheckedFiles") in
                       if uu___5
                       then
                         FStar_Util.print4
                           "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n"
                           checked_fn fn current_digest x.digest
                       else ());
                      (let msg =
                         FStar_Util.format2
                           "checked file %s is stale (digest mismatch for %s)"
                           checked_fn fn in
                       add_and_return
                         ((Invalid msg), (FStar_Pervasives.Inl msg))))
                   else
                     add_and_return
                       (Unknown, (FStar_Pervasives.Inr (x.parsing_data))))))
let (load_checked_file_with_tc_result :
  FStar_Parser_Dep.deps ->
    Prims.string ->
      Prims.string -> (Prims.string, tc_result) FStar_Pervasives.either)
  =
  fun deps ->
    fun fn ->
      fun checked_fn ->
        let load_tc_result fn1 =
          let entry = FStar_Util.load_2values_from_file checked_fn in
          match entry with
          | FStar_Pervasives_Native.Some (uu___, s2) ->
              ((s2.deps_dig), (s2.tc_res))
          | uu___ ->
              failwith
                "Impossible! if first phase of loading was unknown, it should have succeeded" in
        let elt = load_checked_file fn checked_fn in
        match elt with
        | (Invalid msg, uu___) -> FStar_Pervasives.Inl msg
        | (Valid uu___, uu___1) ->
            let uu___2 =
              let uu___3 = FStar_All.pipe_right checked_fn load_tc_result in
              FStar_All.pipe_right uu___3 FStar_Pervasives_Native.snd in
            FStar_All.pipe_right uu___2
              (fun uu___3 -> FStar_Pervasives.Inr uu___3)
        | (Unknown, parsing_data) ->
            let uu___ = hash_dependences deps fn in
            (match uu___ with
             | FStar_Pervasives.Inl msg ->
                 let elt1 = ((Invalid msg), parsing_data) in
                 (FStar_Util.smap_add mcache checked_fn elt1;
                  FStar_Pervasives.Inl msg)
             | FStar_Pervasives.Inr deps_dig' ->
                 let uu___1 = FStar_All.pipe_right checked_fn load_tc_result in
                 (match uu___1 with
                  | (deps_dig, tc_result1) ->
                      if deps_dig = deps_dig'
                      then
                        let elt1 =
                          let uu___2 =
                            let uu___3 = FStar_Util.digest_of_file checked_fn in
                            Valid uu___3 in
                          (uu___2, parsing_data) in
                        (FStar_Util.smap_add mcache checked_fn elt1;
                         (let validate_iface_cache uu___3 =
                            let iface =
                              let uu___4 =
                                FStar_All.pipe_right fn
                                  FStar_Parser_Dep.lowercase_module_name in
                              FStar_All.pipe_right uu___4
                                (FStar_Parser_Dep.interface_of deps) in
                            match iface with
                            | FStar_Pervasives_Native.None -> ()
                            | FStar_Pervasives_Native.Some iface1 ->
                                (try
                                   (fun uu___4 ->
                                      match () with
                                      | () ->
                                          let iface_checked_fn =
                                            FStar_All.pipe_right iface1
                                              FStar_Parser_Dep.cache_file_name in
                                          let uu___5 =
                                            FStar_Util.smap_try_find mcache
                                              iface_checked_fn in
                                          (match uu___5 with
                                           | FStar_Pervasives_Native.Some
                                               (Unknown, parsing_data1) ->
                                               let uu___6 =
                                                 let uu___7 =
                                                   let uu___8 =
                                                     FStar_Util.digest_of_file
                                                       iface_checked_fn in
                                                   Valid uu___8 in
                                                 (uu___7, parsing_data1) in
                                               FStar_Util.smap_add mcache
                                                 iface_checked_fn uu___6
                                           | uu___6 -> ())) ()
                                 with | uu___4 -> ()) in
                          validate_iface_cache ();
                          FStar_Pervasives.Inr tc_result1))
                      else
                        ((let uu___4 =
                            FStar_Options.debug_at_level_no_module
                              (FStar_Options.Other "CheckedFiles") in
                          if uu___4
                          then
                            ((let uu___6 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig') in
                              let uu___7 =
                                FStar_Parser_Dep.print_digest deps_dig' in
                              let uu___8 =
                                FStar_Util.string_of_int
                                  (FStar_List.length deps_dig) in
                              let uu___9 =
                                FStar_Parser_Dep.print_digest deps_dig in
                              FStar_Util.print4
                                "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                                uu___6 uu___7 uu___8 uu___9);
                             if
                               (FStar_List.length deps_dig) =
                                 (FStar_List.length deps_dig')
                             then
                               FStar_List.iter2
                                 (fun uu___6 ->
                                    fun uu___7 ->
                                      match (uu___6, uu___7) with
                                      | ((x, y), (x', y')) ->
                                          if (x <> x') || (y <> y')
                                          then
                                            let uu___8 =
                                              FStar_Parser_Dep.print_digest
                                                [(x, y)] in
                                            let uu___9 =
                                              FStar_Parser_Dep.print_digest
                                                [(x', y')] in
                                            FStar_Util.print2
                                              "Differ at: Expected %s\n Got %s\n"
                                              uu___8 uu___9
                                          else ()) deps_dig deps_dig'
                             else ())
                          else ());
                         (let msg =
                            FStar_Util.format1
                              "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)"
                              checked_fn in
                          let elt1 =
                            ((Invalid msg), (FStar_Pervasives.Inl msg)) in
                          FStar_Util.smap_add mcache checked_fn elt1;
                          FStar_Pervasives.Inl msg))))
let (load_parsing_data_from_cache :
  Prims.string ->
    FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
  =
  fun file_name ->
    FStar_Errors.with_ctx
      (Prims.op_Hat "While loading parsing data from " file_name)
      (fun uu___ ->
         let cache_file =
           try
             (fun uu___1 ->
                match () with
                | () ->
                    let uu___2 = FStar_Parser_Dep.cache_file_name file_name in
                    FStar_All.pipe_right uu___2
                      (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)) ()
           with | uu___1 -> FStar_Pervasives_Native.None in
         match cache_file with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some cache_file1 ->
             let uu___1 = load_checked_file file_name cache_file1 in
             (match uu___1 with
              | (uu___2, FStar_Pervasives.Inl msg) ->
                  FStar_Pervasives_Native.None
              | (uu___2, FStar_Pervasives.Inr data) ->
                  FStar_Pervasives_Native.Some data))
let (load_module_from_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> tc_result FStar_Pervasives_Native.option)
  =
  let already_failed = FStar_Util.mk_ref false in
  fun env ->
    fun fn ->
      FStar_Errors.with_ctx
        (Prims.op_Hat "While loading module from file " fn)
        (fun uu___ ->
           let load_it fn1 uu___1 =
             let cache_file = FStar_Parser_Dep.cache_file_name fn1 in
             let fail msg cache_file1 =
               let suppress_warning =
                 (FStar_Options.should_verify_file fn1) ||
                   (FStar_ST.op_Bang already_failed) in
               if Prims.op_Negation suppress_warning
               then
                 (FStar_ST.op_Colon_Equals already_failed true;
                  (let uu___3 =
                     let uu___4 =
                       FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                     let uu___5 =
                       FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                     FStar_Range.mk_range fn1 uu___4 uu___5 in
                   let uu___4 =
                     let uu___5 =
                       FStar_Util.format3
                         "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                         cache_file1 msg fn1 in
                     (FStar_Errors.Warning_CachedFile, uu___5) in
                   FStar_Errors.log_issue uu___3 uu___4))
               else () in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                 FStar_TypeChecker_Env.dep_graph uu___4 in
               load_checked_file_with_tc_result uu___3 fn1 cache_file in
             match uu___2 with
             | FStar_Pervasives.Inl msg ->
                 (fail msg cache_file; FStar_Pervasives_Native.None)
             | FStar_Pervasives.Inr tc_result1 ->
                 ((let uu___4 =
                     FStar_Options.debug_at_level_no_module
                       (FStar_Options.Other "CheckedFiles") in
                   if uu___4
                   then
                     FStar_Util.print1
                       "Successfully loaded module from checked file %s\n"
                       cache_file
                   else ());
                  FStar_Pervasives_Native.Some tc_result1) in
           let load_with_profiling fn1 =
             FStar_Profiling.profile (load_it fn1)
               FStar_Pervasives_Native.None "FStar.CheckedFiles" in
           let i_fn_opt =
             let uu___1 =
               let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
               FStar_TypeChecker_Env.dep_graph uu___2 in
             let uu___2 = FStar_Parser_Dep.lowercase_module_name fn in
             FStar_Parser_Dep.interface_of uu___1 uu___2 in
           let uu___1 =
             (FStar_Parser_Dep.is_implementation fn) &&
               (FStar_All.pipe_right i_fn_opt FStar_Util.is_some) in
           if uu___1
           then
             let i_fn = FStar_All.pipe_right i_fn_opt FStar_Util.must in
             let i_tc = load_with_profiling i_fn in
             match i_tc with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some uu___2 -> load_with_profiling fn
           else load_with_profiling fn)
let (store_values_to_cache :
  Prims.string ->
    checked_file_entry_stage1 -> checked_file_entry_stage2 -> unit)
  =
  fun cache_file ->
    fun stage1 ->
      fun stage2 ->
        FStar_Errors.with_ctx
          (Prims.op_Hat "While writing checked file " cache_file)
          (fun uu___ ->
             FStar_Util.save_2values_to_file cache_file stage1 stage2)
let (store_module_to_cache :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env ->
    fun fn ->
      fun parsing_data ->
        fun tc_result1 ->
          let uu___ =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu___1 = FStar_Options.cache_off () in
               Prims.op_Negation uu___1) in
          if uu___
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn in
            let digest =
              let uu___1 =
                let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                FStar_TypeChecker_Env.dep_graph uu___2 in
              hash_dependences uu___1 fn in
            match digest with
            | FStar_Pervasives.Inr hashes ->
                let tc_result2 =
                  let uu___1 = tc_result1 in
                  {
                    checked_module = (uu___1.checked_module);
                    mii = (uu___1.mii);
                    smt_decls = (uu___1.smt_decls);
                    tc_time = Prims.int_zero;
                    extraction_time = Prims.int_zero
                  } in
                let stage1 =
                  let uu___1 = FStar_Util.digest_of_file fn in
                  {
                    version = cache_version_number;
                    digest = uu___1;
                    parsing_data
                  } in
                let stage2 = { deps_dig = hashes; tc_res = tc_result2 } in
                store_values_to_cache cache_file stage1 stage2
            | FStar_Pervasives.Inl msg ->
                let uu___1 =
                  let uu___2 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                  let uu___3 =
                    FStar_Range.mk_pos Prims.int_zero Prims.int_zero in
                  FStar_Range.mk_range fn uu___2 uu___3 in
                let uu___2 =
                  let uu___3 =
                    FStar_Util.format2 "%s was not written since %s"
                      cache_file msg in
                  (FStar_Errors.Warning_FileNotWritten, uu___3) in
                FStar_Errors.log_issue uu___1 uu___2
          else ()