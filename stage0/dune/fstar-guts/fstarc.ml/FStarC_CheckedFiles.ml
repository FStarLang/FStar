open Prims
let dbg : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "CheckedFiles"
let debug (f : unit -> unit) : unit=
  let uu___ = FStarC_Effect.op_Bang dbg in if uu___ then f () else ()
let cache_version_number : Prims.int= (Prims.of_int (76))
type tc_result =
  {
  checked_module: FStarC_Syntax_Syntax.modul ;
  mii: FStarC_Syntax_DsEnv.module_inclusion_info ;
  smt_decls:
    (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.fvar_binding
      Prims.list)
    ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let __proj__Mktc_result__item__checked_module (projectee : tc_result) :
  FStarC_Syntax_Syntax.modul=
  match projectee with
  | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
      checked_module
let __proj__Mktc_result__item__mii (projectee : tc_result) :
  FStarC_Syntax_DsEnv.module_inclusion_info=
  match projectee with
  | { checked_module; mii; smt_decls; tc_time; extraction_time;_} -> mii
let __proj__Mktc_result__item__smt_decls (projectee : tc_result) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.fvar_binding
    Prims.list)=
  match projectee with
  | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
      smt_decls
let __proj__Mktc_result__item__tc_time (projectee : tc_result) : Prims.int=
  match projectee with
  | { checked_module; mii; smt_decls; tc_time; extraction_time;_} -> tc_time
let __proj__Mktc_result__item__extraction_time (projectee : tc_result) :
  Prims.int=
  match projectee with
  | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
      extraction_time
type checked_file_entry_stage1 =
  {
  version: Prims.int ;
  digest: Prims.string ;
  parsing_data: FStarC_Parser_Dep.parsing_data }
let __proj__Mkchecked_file_entry_stage1__item__version
  (projectee : checked_file_entry_stage1) : Prims.int=
  match projectee with | { version; digest; parsing_data;_} -> version
let __proj__Mkchecked_file_entry_stage1__item__digest
  (projectee : checked_file_entry_stage1) : Prims.string=
  match projectee with | { version; digest; parsing_data;_} -> digest
let __proj__Mkchecked_file_entry_stage1__item__parsing_data
  (projectee : checked_file_entry_stage1) : FStarC_Parser_Dep.parsing_data=
  match projectee with | { version; digest; parsing_data;_} -> parsing_data
type checked_file_entry_stage2 =
  {
  deps_dig: (Prims.string * Prims.string) Prims.list ;
  tc_res: tc_result }
let __proj__Mkchecked_file_entry_stage2__item__deps_dig
  (projectee : checked_file_entry_stage2) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { deps_dig; tc_res;_} -> deps_dig
let __proj__Mkchecked_file_entry_stage2__item__tc_res
  (projectee : checked_file_entry_stage2) : tc_result=
  match projectee with | { deps_dig; tc_res;_} -> tc_res
type tc_result_t =
  | Unknown 
  | Invalid of Prims.string 
  | Valid of Prims.string 
let uu___is_Unknown (projectee : tc_result_t) : Prims.bool=
  match projectee with | Unknown -> true | uu___ -> false
let uu___is_Invalid (projectee : tc_result_t) : Prims.bool=
  match projectee with | Invalid _0 -> true | uu___ -> false
let __proj__Invalid__item___0 (projectee : tc_result_t) : Prims.string=
  match projectee with | Invalid _0 -> _0
let uu___is_Valid (projectee : tc_result_t) : Prims.bool=
  match projectee with | Valid _0 -> true | uu___ -> false
let __proj__Valid__item___0 (projectee : tc_result_t) : Prims.string=
  match projectee with | Valid _0 -> _0
let uu___0 : tc_result_t FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Unknown -> "Unknown"
         | Invalid s ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
             Prims.strcat "Invalid " uu___1
         | Valid s ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
             Prims.strcat "Valid " uu___1)
  }
type cache_t =
  (tc_result_t * (Prims.string, FStarC_Parser_Dep.parsing_data)
    FStar_Pervasives.either)
let mcache : cache_t FStarC_SMap.t= FStarC_SMap.create (Prims.of_int (50))
let add_and_return (checked_fn : Prims.string) (elt : cache_t) : cache_t=
  FStarC_SMap.add mcache checked_fn elt; elt
let try_find_in_cache (checked_fn : Prims.string) :
  cache_t FStar_Pervasives_Native.option=
  FStarC_SMap.try_find mcache checked_fn
let dump_cache_keys (tag : Prims.string) : unit=
  let uu___ = FStarC_Effect.op_Bang dbg in
  if uu___
  then
    let uu___1 =
      let uu___2 = FStarC_SMap.keys mcache in
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
        uu___2 in
    FStarC_Format.print2 "(%s) Cache contains %s\n" tag uu___1
  else ()
let load_checked_file (fn : Prims.string) (checked_fn : Prims.string) :
  cache_t=
  debug
    (fun uu___1 ->
       FStarC_Format.print1 "Trying to load checked file result %s\n"
         checked_fn);
  (let elt = try_find_in_cache checked_fn in
   if FStar_Pervasives_Native.uu___is_Some elt
   then FStarC_Option.must elt
   else
     (let add_and_return1 = add_and_return checked_fn in
      if Prims.op_Negation (FStarC_Filepath.file_exists checked_fn)
      then
        let msg =
          FStarC_Format.fmt1 "checked file %s does not exist" checked_fn in
        add_and_return1 ((Invalid msg), (FStar_Pervasives.Inl msg))
      else
        (let entry = FStarC_Util.load_value_from_file checked_fn in
         match entry with
         | FStar_Pervasives_Native.None ->
             let msg =
               FStarC_Format.fmt1 "checked file %s is corrupt" checked_fn in
             add_and_return1 ((Invalid msg), (FStar_Pervasives.Inl msg))
         | FStar_Pervasives_Native.Some x ->
             if x.version <> cache_version_number
             then
               let msg =
                 FStarC_Format.fmt1 "checked file %s has incorrect version"
                   checked_fn in
               add_and_return1 ((Invalid msg), (FStar_Pervasives.Inl msg))
             else
               (let current_digest = FStarC_Util.digest_of_file fn in
                if x.digest <> current_digest
                then
                  (debug
                     (fun uu___5 ->
                        FStarC_Format.print4
                          "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n"
                          checked_fn fn current_digest x.digest);
                   (let msg =
                      FStarC_Format.fmt2
                        "checked file %s is stale (digest mismatch for %s)"
                        checked_fn fn in
                    add_and_return1
                      ((Invalid msg), (FStar_Pervasives.Inl msg))))
                else
                  add_and_return1
                    (Unknown, (FStar_Pervasives.Inr (x.parsing_data)))))))
let hash_dependences (deps : FStarC_Parser_Dep.deps) (fn : Prims.string)
  (deps_of_fn : Prims.string Prims.list) :
  (Prims.string, (Prims.string * Prims.string) Prims.list)
    FStar_Pervasives.either=
  FStarC_Stats.record "hash_dependences"
    (fun uu___ ->
       let fn1 =
         let uu___1 = FStarC_Find.find_file fn in
         match uu___1 with
         | FStar_Pervasives_Native.Some fn2 -> fn2
         | uu___2 -> fn in
       let module_name = FStarC_Parser_Dep.lowercase_module_name fn1 in
       let source_hash = FStarC_Util.digest_of_file fn1 in
       let has_interface =
         let uu___1 = FStarC_Parser_Dep.interface_of deps module_name in
         FStar_Pervasives_Native.uu___is_Some uu___1 in
       let interface_checked_file_name =
         let uu___1 =
           (FStarC_Parser_Dep.is_implementation fn1) && has_interface in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_Parser_Dep.interface_of deps module_name in
               FStarC_Option.must uu___4 in
             FStarC_Parser_Dep.cache_file_name uu___3 in
           FStar_Pervasives_Native.Some uu___2
         else FStar_Pervasives_Native.None in
       let binary_deps =
         FStarC_List.filter
           (fun fn2 ->
              let uu___1 =
                (FStarC_Parser_Dep.is_interface fn2) &&
                  (let uu___2 = FStarC_Parser_Dep.lowercase_module_name fn2 in
                   uu___2 = module_name) in
              Prims.op_Negation uu___1) deps_of_fn in
       let binary_deps1 =
         FStarC_List.sortWith
           (fun fn11 fn2 ->
              let uu___1 = FStarC_Parser_Dep.lowercase_module_name fn11 in
              let uu___2 = FStarC_Parser_Dep.lowercase_module_name fn2 in
              FStarC_String.compare uu___1 uu___2) binary_deps in
       let maybe_add_iface_hash out =
         match interface_checked_file_name with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives.Inr (("source", source_hash) :: out)
         | FStar_Pervasives_Native.Some iface ->
             let uu___1 = try_find_in_cache iface in
             (match uu___1 with
              | FStar_Pervasives_Native.None ->
                  let msg =
                    FStarC_Format.fmt1
                      "hash_dependences::the interface checked file %s does not exist\n"
                      iface in
                  (debug (fun uu___3 -> FStarC_Format.print1 "%s\n" msg);
                   FStar_Pervasives.Inl msg)
              | FStar_Pervasives_Native.Some (Invalid msg, uu___2) ->
                  FStar_Pervasives.Inl msg
              | FStar_Pervasives_Native.Some (Valid h, uu___2) ->
                  FStar_Pervasives.Inr (("source", source_hash) ::
                    ("interface", h) :: out)
              | FStar_Pervasives_Native.Some (Unknown, uu___2) ->
                  let uu___3 =
                    FStarC_Format.fmt1
                      "Impossible: unknown entry in the cache for interface %s\n"
                      iface in
                  failwith uu___3) in
       let rec hash_deps out uu___1 =
         match uu___1 with
         | [] -> maybe_add_iface_hash out
         | fn2::deps1 ->
             let cache_fn = FStarC_Parser_Dep.cache_file_name fn2 in
             let digest =
               let uu___2 = try_find_in_cache cache_fn in
               match uu___2 with
               | FStar_Pervasives_Native.None ->
                   let msg =
                     FStarC_Format.fmt2
                       "For dependency %s, cache file %s is not loaded" fn2
                       cache_fn in
                   (debug (fun uu___4 -> FStarC_Format.print1 "%s\n" msg);
                    FStar_Pervasives.Inl msg)
               | FStar_Pervasives_Native.Some (Invalid msg, uu___3) ->
                   FStar_Pervasives.Inl msg
               | FStar_Pervasives_Native.Some (Valid dig, uu___3) ->
                   FStar_Pervasives.Inr dig
               | FStar_Pervasives_Native.Some (Unknown, uu___3) ->
                   let uu___4 =
                     FStarC_Format.fmt2
                       "Impossible: unknown entry in the cache for dependence %s of module %s"
                       fn2 module_name in
                   failwith uu___4 in
             (match digest with
              | FStar_Pervasives.Inl msg -> FStar_Pervasives.Inl msg
              | FStar_Pervasives.Inr dig ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Parser_Dep.lowercase_module_name fn2 in
                      (uu___4, dig) in
                    uu___3 :: out in
                  hash_deps uu___2 deps1) in
       hash_deps [] binary_deps1)
let load_tc_result (checked_fn : Prims.string) :
  ((Prims.string * Prims.string) Prims.list * tc_result)
    FStar_Pervasives_Native.option=
  let entry = FStarC_Util.load_2values_from_file checked_fn in
  match entry with
  | FStar_Pervasives_Native.Some (uu___, s2) ->
      FStar_Pervasives_Native.Some ((s2.deps_dig), (s2.tc_res))
  | uu___ -> FStar_Pervasives_Native.None
let load_checked_file_with_tc_result (deps : FStarC_Parser_Dep.deps)
  (fn : Prims.string) (checked_fn : Prims.string) :
  (Prims.string, tc_result) FStar_Pervasives.either=
  debug
    (fun uu___1 ->
       FStarC_Format.print1 "Trying to load checked file with tc result %s\n"
         checked_fn);
  (let load_tc_result' fn1 =
     let uu___1 = load_tc_result fn1 in
     match uu___1 with
     | FStar_Pervasives_Native.Some x -> x
     | FStar_Pervasives_Native.None ->
         failwith
           "Impossible! if first phase of loading was unknown, it should have succeeded" in
   let elt = load_checked_file fn checked_fn in
   match elt with
   | (Invalid msg, uu___1) -> FStar_Pervasives.Inl msg
   | (Valid uu___1, uu___2) ->
       let uu___3 =
         let uu___4 = load_tc_result' checked_fn in
         FStar_Pervasives_Native.snd uu___4 in
       FStar_Pervasives.Inr uu___3
   | (Unknown, parsing_data) ->
       let uu___1 =
         let uu___2 = FStarC_Parser_Dep.deps_of deps fn in
         hash_dependences deps fn uu___2 in
       (match uu___1 with
        | FStar_Pervasives.Inl msg ->
            let elt1 = ((Invalid msg), parsing_data) in
            let uu___2 = add_and_return checked_fn elt1 in
            FStar_Pervasives.Inl msg
        | FStar_Pervasives.Inr deps_dig' ->
            let uu___2 = load_tc_result' checked_fn in
            (match uu___2 with
             | (deps_dig, tc_result1) ->
                 if deps_dig = deps_dig'
                 then
                   let elt1 =
                     let uu___3 =
                       let uu___4 = FStarC_Util.digest_of_file checked_fn in
                       Valid uu___4 in
                     (uu___3, parsing_data) in
                   let uu___3 = add_and_return checked_fn elt1 in
                   let validate_iface_cache uu___4 =
                     let iface =
                       let uu___5 =
                         FStarC_Parser_Dep.lowercase_module_name fn in
                       FStarC_Parser_Dep.interface_of deps uu___5 in
                     match iface with
                     | FStar_Pervasives_Native.None -> ()
                     | FStar_Pervasives_Native.Some iface1 ->
                         (try
                            (fun uu___5 ->
                               match () with
                               | () ->
                                   let iface_checked_fn =
                                     FStarC_Parser_Dep.cache_file_name iface1 in
                                   let uu___6 =
                                     try_find_in_cache iface_checked_fn in
                                   (match uu___6 with
                                    | FStar_Pervasives_Native.Some
                                        (Unknown, parsing_data1) ->
                                        let uu___7 =
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStarC_Util.digest_of_file
                                                  iface_checked_fn in
                                              Valid uu___10 in
                                            (uu___9, parsing_data1) in
                                          add_and_return iface_checked_fn
                                            uu___8 in
                                        ()
                                    | uu___7 -> ())) ()
                          with | uu___5 -> ()) in
                   (validate_iface_cache (); FStar_Pervasives.Inr tc_result1)
                 else
                   (debug
                      (fun uu___5 ->
                         (let uu___7 =
                            FStarC_Class_Show.show
                              FStarC_Class_Show.showable_nat
                              (FStarC_List.length deps_dig') in
                          let uu___8 =
                            FStarC_Parser_Dep.print_digest deps_dig' in
                          let uu___9 =
                            FStarC_Class_Show.show
                              FStarC_Class_Show.showable_nat
                              (FStarC_List.length deps_dig) in
                          let uu___10 =
                            FStarC_Parser_Dep.print_digest deps_dig in
                          FStarC_Format.print4
                            "FAILING to load.\nHashes computed (%s):\n%s\n\nHashes read (%s):\n%s\n"
                            uu___7 uu___8 uu___9 uu___10);
                         if
                           (FStarC_List.length deps_dig) =
                             (FStarC_List.length deps_dig')
                         then
                           FStarC_List.iter2
                             (fun uu___7 uu___8 ->
                                match (uu___7, uu___8) with
                                | ((x, y), (x', y')) ->
                                    if (x <> x') || (y <> y')
                                    then
                                      let uu___9 =
                                        FStarC_Parser_Dep.print_digest
                                          [(x, y)] in
                                      let uu___10 =
                                        FStarC_Parser_Dep.print_digest
                                          [(x', y')] in
                                      FStarC_Format.print2
                                        "Differ at: Expected %s\n Got %s\n"
                                        uu___9 uu___10
                                    else ()) deps_dig deps_dig'
                         else ());
                    (let msg =
                       FStarC_Format.fmt1
                         "checked file %s is stale (dependence hash mismatch, use --debug CheckedFiles for more details)"
                         checked_fn in
                     let elt1 = ((Invalid msg), (FStar_Pervasives.Inl msg)) in
                     let uu___5 = add_and_return checked_fn elt1 in
                     FStar_Pervasives.Inl msg)))))
let load_parsing_data_from_cache (file_name : Prims.string) :
  FStarC_Parser_Dep.parsing_data FStar_Pervasives_Native.option=
  FStarC_Errors.with_ctx
    (Prims.strcat "While loading parsing data from " file_name)
    (fun uu___ ->
       let cache_file =
         try
           (fun uu___1 ->
              match () with
              | () ->
                  let uu___2 = FStarC_Parser_Dep.cache_file_name file_name in
                  FStar_Pervasives_Native.Some uu___2) ()
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
let load_module_from_cache_internal :
  Prims.bool ->
    FStarC_Parser_Dep.deps ->
      Prims.string -> tc_result FStar_Pervasives_Native.option=
  let already_failed = FStarC_Effect.mk_ref false in
  fun try_load deps fn ->
    FStarC_Errors.with_ctx
      (Prims.strcat "While loading module from file " fn)
      (fun uu___ ->
         let load_it fn1 uu___1 =
           let cache_file = FStarC_Parser_Dep.cache_file_name fn1 in
           let fail msg cache_file1 =
             let suppress_warning =
               (try_load || (FStarC_Options.should_check_file fn1)) ||
                 (FStarC_Effect.op_Bang already_failed) in
             let uu___2 =
               (Prims.op_Negation suppress_warning) ||
                 (FStarC_Effect.op_Bang dbg) in
             if uu___2
             then
               (FStarC_Effect.op_Colon_Equals already_failed true;
                (let uu___4 =
                   let uu___5 =
                     FStarC_Range_Type.mk_pos Prims.int_zero Prims.int_zero in
                   let uu___6 =
                     FStarC_Range_Type.mk_pos Prims.int_zero Prims.int_zero in
                   FStarC_Range_Type.mk_range fn1 uu___5 uu___6 in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       FStarC_Format.fmt3
                         "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
                         cache_file1 msg fn1 in
                     FStarC_Errors_Msg.text uu___7 in
                   [uu___6] in
                 FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                   uu___4 FStarC_Errors_Codes.Warning_CachedFile ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                   (Obj.magic uu___5)))
             else () in
           let uu___2 = load_checked_file_with_tc_result deps fn1 cache_file in
           match uu___2 with
           | FStar_Pervasives.Inl msg ->
               (fail msg cache_file; FStar_Pervasives_Native.None)
           | FStar_Pervasives.Inr tc_result1 ->
               (debug
                  (fun uu___4 ->
                     FStarC_Format.print1
                       "Successfully loaded module from checked file %s\n"
                       cache_file);
                FStar_Pervasives_Native.Some tc_result1) in
         let load_with_profiling fn1 =
           FStarC_Profiling.profile (load_it fn1)
             FStar_Pervasives_Native.None "FStarC.CheckedFiles" in
         let i_fn_opt =
           let uu___1 = FStarC_Parser_Dep.lowercase_module_name fn in
           FStarC_Parser_Dep.interface_of deps uu___1 in
         let uu___1 =
           (FStarC_Parser_Dep.is_implementation fn) &&
             (FStar_Pervasives_Native.uu___is_Some i_fn_opt) in
         if uu___1
         then
           let i_fn = FStarC_Option.must i_fn_opt in
           let i_tc = load_with_profiling i_fn in
           match i_tc with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some uu___2 -> load_with_profiling fn
         else load_with_profiling fn)
let scan_deps_and_check_cache_validity (fn : Prims.string) :
  (Prims.string Prims.list * FStarC_Parser_Dep.deps)
    FStar_Pervasives_Native.option=
  FStarC_Parser_Dep.with_fly_deps_disabled
    (fun uu___ ->
       let checked_fn = FStarC_Parser_Dep.cache_file_name fn in
       let uu___1 = FStarC_Find.find_file checked_fn in
       match uu___1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some checked_fn1 ->
           let uu___2 =
             FStarC_Parser_Dep.with_fly_deps_disabled
               (fun uu___3 ->
                  FStarC_Dependencies.find_deps_if_needed [fn]
                    load_parsing_data_from_cache) in
           (match uu___2 with
            | (filenames, dep_graph) ->
                let rec try_load_all fns =
                  match fns with
                  | [] -> FStar_Pervasives_Native.Some (filenames, dep_graph)
                  | fn1::rest ->
                      let uu___3 =
                        load_module_from_cache_internal false dep_graph fn1 in
                      (match uu___3 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some tcres ->
                           try_load_all rest) in
                try_load_all filenames))
let load_module_from_cache (env : FStarC_TypeChecker_Env.env)
  (fn : Prims.string) : tc_result FStar_Pervasives_Native.option=
  let uu___ = FStarC_TypeChecker_Env.dep_graph env in
  load_module_from_cache_internal false uu___ fn
let store_values_to_cache (cache_file : Prims.string)
  (stage1 : checked_file_entry_stage1) (stage2 : checked_file_entry_stage2) :
  unit=
  FStarC_Errors.with_ctx
    (Prims.strcat "While writing checked file " cache_file)
    (fun uu___ -> FStarC_Util.save_2values_to_file cache_file stage1 stage2)
let uu___1 : FStarC_Parser_Dep.parsing_data FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = FStarC_Parser_Dep.str_of_parsing_data }
let store_module_to_cache (env : FStarC_TypeChecker_Env.env)
  (fn : Prims.string)
  (parsing_data_and_direct_deps :
    (FStarC_Parser_Dep.parsing_data * Prims.string Prims.list))
  (tc_result1 : tc_result) : unit=
  let uu___ =
    (FStarC_Options.cache_checked_modules ()) &&
      (let uu___2 = FStarC_Options.cache_off () in Prims.op_Negation uu___2) in
  if uu___
  then
    (debug
       (fun uu___3 ->
          let uu___4 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple2 uu___1
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string))
              parsing_data_and_direct_deps in
          FStarC_Format.print2
            "Storing checked file for %s with %s dependences\n" fn uu___4);
     (let uu___4 = FStarC_Parser_Dep.fly_deps_enabled () in
      if uu___4
      then
        let i_fn_opt =
          let uu___5 = FStarC_TypeChecker_Env.dep_graph env in
          let uu___6 = FStarC_Parser_Dep.lowercase_module_name fn in
          FStarC_Parser_Dep.interface_of uu___5 uu___6 in
        match i_fn_opt with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some iface ->
            (debug
               (fun uu___6 ->
                  FStarC_Format.print1
                    "Tryng to load interface %s from cache before storing\n"
                    iface);
             (let uu___6 =
                let uu___7 = FStarC_TypeChecker_Env.dep_graph env in
                load_module_from_cache_internal true uu___7 iface in
              ()))
      else ());
     (let cache_file =
        let uu___4 = FStarC_Options.output_to () in
        match uu___4 with
        | FStar_Pervasives_Native.Some fn1 -> fn1
        | FStar_Pervasives_Native.None ->
            FStarC_Parser_Dep.cache_file_name fn in
      let uu___4 = parsing_data_and_direct_deps in
      match uu___4 with
      | (parsing_data, deps_of_fn) ->
          let digest =
            let uu___5 = FStarC_TypeChecker_Env.dep_graph env in
            hash_dependences uu___5 fn deps_of_fn in
          (match digest with
           | FStar_Pervasives.Inr hashes ->
               let tc_result2 =
                 {
                   checked_module = (tc_result1.checked_module);
                   mii = (tc_result1.mii);
                   smt_decls = (tc_result1.smt_decls);
                   tc_time = Prims.int_zero;
                   extraction_time = Prims.int_zero
                 } in
               let stage1 =
                 let uu___5 = FStarC_Util.digest_of_file fn in
                 {
                   version = cache_version_number;
                   digest = uu___5;
                   parsing_data
                 } in
               let stage2 = { deps_dig = hashes; tc_res = tc_result2 } in
               store_values_to_cache cache_file stage1 stage2
           | FStar_Pervasives.Inl msg ->
               (debug
                  (fun uu___6 ->
                     let uu___7 =
                       FStarC_Class_Show.show
                         (FStarC_Class_Show.show_list
                            FStarC_Class_Show.showable_string) deps_of_fn in
                     FStarC_Format.print2
                       "FAILING to store cache file for %s, with deps %s\n"
                       fn uu___7);
                (let uu___6 =
                   let uu___7 =
                     FStarC_Range_Type.mk_pos Prims.int_zero Prims.int_zero in
                   let uu___8 =
                     FStarC_Range_Type.mk_pos Prims.int_zero Prims.int_zero in
                   FStarC_Range_Type.mk_range fn uu___7 uu___8 in
                 let uu___7 =
                   let uu___8 =
                     let uu___9 =
                       FStarC_Format.fmt1 "Checked file %s was not written."
                         cache_file in
                     FStarC_Errors_Msg.text uu___9 in
                   let uu___9 =
                     let uu___10 =
                       let uu___11 = FStarC_Errors_Msg.text msg in
                       FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                         (FStar_Pprint.doc_of_string "Reason:") uu___11 in
                     [uu___10] in
                   uu___8 :: uu___9 in
                 FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                   uu___6 FStarC_Errors_Codes.Warning_FileNotWritten ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                   (Obj.magic uu___7))))))
  else ()
let unsafe_raw_load_checked_file (checked_fn : Prims.string) :
  (FStarC_Parser_Dep.parsing_data * Prims.string Prims.list * tc_result)
    FStar_Pervasives_Native.option=
  let entry = FStarC_Util.load_2values_from_file checked_fn in
  match entry with
  | FStar_Pervasives_Native.Some (s1, s2) ->
      let uu___ =
        let uu___2 = FStarC_List.map FStar_Pervasives_Native.fst s2.deps_dig in
        ((s1.parsing_data), uu___2, (s2.tc_res)) in
      FStar_Pervasives_Native.Some uu___
  | uu___ -> FStar_Pervasives_Native.None
