open Prims
let (fallback_range :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (error_range_bound :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let with_error_bound :
  'a . FStarC_Compiler_Range_Type.range -> (unit -> 'a) -> 'a =
  fun r ->
    fun f ->
      let old = FStarC_Compiler_Effect.op_Bang error_range_bound in
      FStarC_Compiler_Effect.op_Colon_Equals error_range_bound
        (FStar_Pervasives_Native.Some r);
      (let res = f () in
       FStarC_Compiler_Effect.op_Colon_Equals error_range_bound old; res)
exception Invalid_warn_error_setting of Prims.string 
let (uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Invalid_warn_error_setting uu___ -> true
    | uu___ -> false
let (__proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Invalid_warn_error_setting uu___ -> uu___
let lookup_error :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu * 'uuuuu1 * 'uuuuu2) Prims.list ->
      'uuuuu -> ('uuuuu * 'uuuuu1 * 'uuuuu2)
  =
  fun settings ->
    fun e ->
      let uu___ =
        FStarC_Compiler_Util.try_find
          (fun uu___1 -> match uu___1 with | (v, uu___2, i) -> e = v)
          settings in
      match uu___ with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          failwith "Impossible: unrecognized error"
let lookup_error_range :
  'uuuuu 'uuuuu1 .
    ('uuuuu * 'uuuuu1 * Prims.int) Prims.list ->
      (Prims.int * Prims.int) -> ('uuuuu * 'uuuuu1 * Prims.int) Prims.list
  =
  fun settings ->
    fun uu___ ->
      match uu___ with
      | (l, h) ->
          let uu___1 =
            FStarC_Compiler_List.partition
              (fun uu___2 ->
                 match uu___2 with
                 | (uu___3, uu___4, i) -> (l <= i) && (i <= h)) settings in
          (match uu___1 with | (matches, uu___2) -> matches)
let (error_number : FStarC_Errors_Codes.error_setting -> Prims.int) =
  fun uu___ -> match uu___ with | (uu___1, uu___2, i) -> i
let (errno : FStarC_Errors_Codes.error_code -> Prims.int) =
  fun e ->
    let uu___ = lookup_error FStarC_Errors_Codes.default_settings e in
    error_number uu___
let (warn_on_use_errno : Prims.int) =
  errno FStarC_Errors_Codes.Warning_WarnOnUse
let (defensive_errno : Prims.int) =
  errno FStarC_Errors_Codes.Warning_Defensive
let (call_to_erased_errno : Prims.int) =
  errno FStarC_Errors_Codes.Error_CallToErased
let (update_flags :
  (FStarC_Errors_Codes.error_flag * Prims.string) Prims.list ->
    FStarC_Errors_Codes.error_setting Prims.list)
  =
  fun l ->
    let set_one_flag i flag default_flag =
      match (flag, default_flag) with
      | (FStarC_Errors_Codes.CWarning, FStarC_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1
                "cannot turn error %s into warning" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CError, FStarC_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1
                "cannot turn error %s into warning" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CSilent, FStarC_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1 "cannot silence error %s" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CSilent, FStarC_Errors_Codes.CFatal) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1
                "cannot change the error level of fatal error %s" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CWarning, FStarC_Errors_Codes.CFatal) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1
                "cannot change the error level of fatal error %s" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CError, FStarC_Errors_Codes.CFatal) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_Util.string_of_int i in
              FStarC_Compiler_Util.format1
                "cannot change the error level of fatal error %s" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStarC_Compiler_Effect.raise uu___
      | (FStarC_Errors_Codes.CAlwaysError, FStarC_Errors_Codes.CFatal) ->
          FStarC_Errors_Codes.CFatal
      | uu___ -> flag in
    let set_flag_for_range uu___ =
      match uu___ with
      | (flag, range) ->
          let errs =
            lookup_error_range FStarC_Errors_Codes.default_settings range in
          FStarC_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (v, default_flag, i) ->
                   let uu___2 = set_one_flag i flag default_flag in
                   (v, uu___2, i)) errs in
    let compute_range uu___ =
      match uu___ with
      | (flag, s) ->
          let r = FStarC_Compiler_Util.split s ".." in
          let uu___1 =
            match r with
            | r1::r2::[] ->
                let uu___2 = FStarC_Compiler_Util.int_of_string r1 in
                let uu___3 = FStarC_Compiler_Util.int_of_string r2 in
                (uu___2, uu___3)
            | uu___2 ->
                let uu___3 =
                  let uu___4 =
                    FStarC_Compiler_Util.format1
                      "Malformed warn-error range %s" s in
                  Invalid_warn_error_setting uu___4 in
                FStarC_Compiler_Effect.raise uu___3 in
          (match uu___1 with | (l1, h) -> (flag, (l1, h))) in
    let error_range_settings =
      FStarC_Compiler_List.map compute_range (FStarC_Compiler_List.rev l) in
    let uu___ =
      FStarC_Compiler_List.collect set_flag_for_range error_range_settings in
    FStarC_Compiler_List.op_At uu___ FStarC_Errors_Codes.default_settings
type error =
  (FStarC_Errors_Codes.error_code * FStarC_Errors_Msg.error_message *
    FStarC_Compiler_Range_Type.range * Prims.string Prims.list)
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | ENotImplemented -> true | uu___ -> false
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EInfo -> true | uu___ -> false
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EWarning -> true | uu___ -> false
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EError -> true | uu___ -> false
exception Error of error 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Error uu___ -> true | uu___ -> false
let (__proj__Error__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Error uu___ -> uu___
exception Warning of error 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning uu___ -> true | uu___ -> false
let (__proj__Warning__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Warning uu___ -> uu___
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Stop -> true | uu___ -> false
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Empty_frag -> true | uu___ -> false
let (json_of_issue_level : issue_level -> FStarC_Json.json) =
  fun level ->
    FStarC_Json.JsonStr
      (match level with
       | ENotImplemented -> "NotImplemented"
       | EInfo -> "Info"
       | EWarning -> "Warning"
       | EError -> "Error")
type issue =
  {
  issue_msg: FStarC_Errors_Msg.error_message ;
  issue_level: issue_level ;
  issue_range:
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ;
  issue_number: Prims.int FStar_Pervasives_Native.option ;
  issue_ctx: Prims.string Prims.list }
let (__proj__Mkissue__item__issue_msg :
  issue -> FStarC_Errors_Msg.error_message) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_msg
let (__proj__Mkissue__item__issue_level : issue -> issue_level) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_level1
let (__proj__Mkissue__item__issue_range :
  issue -> FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_range
let (__proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_number
let (__proj__Mkissue__item__issue_ctx : issue -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_ctx
let (json_of_issue : issue -> FStarC_Json.json) =
  fun issue1 ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Errors_Msg.json_of_error_message issue1.issue_msg in
        ("msg", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 = json_of_issue_level issue1.issue_level in
          ("level", uu___4) in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                Obj.magic
                  (FStarC_Class_Monad.op_Less_Dollar_Greater
                     FStarC_Class_Monad.monad_option () ()
                     (fun uu___8 ->
                        (Obj.magic FStarC_Compiler_Range_Type.json_of_range)
                          uu___8) (Obj.magic issue1.issue_range)) in
              FStarC_Compiler_Util.dflt FStarC_Json.JsonNull uu___7 in
            ("range", uu___6) in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  Obj.magic
                    (FStarC_Class_Monad.op_Less_Dollar_Greater
                       FStarC_Class_Monad.monad_option () ()
                       (fun uu___10 ->
                          (fun uu___10 ->
                             let uu___10 = Obj.magic uu___10 in
                             Obj.magic (FStarC_Json.JsonInt uu___10)) uu___10)
                       (Obj.magic issue1.issue_number)) in
                FStarC_Compiler_Util.dflt FStarC_Json.JsonNull uu___9 in
              ("number", uu___8) in
            let uu___8 =
              let uu___9 =
                let uu___10 =
                  let uu___11 =
                    Obj.magic
                      (FStarC_Class_Monad.op_Less_Dollar_Greater
                         FStarC_Class_Monad.monad_list () ()
                         (fun uu___12 ->
                            (fun uu___12 ->
                               let uu___12 = Obj.magic uu___12 in
                               Obj.magic (FStarC_Json.JsonStr uu___12))
                              uu___12) (Obj.magic issue1.issue_ctx)) in
                  FStarC_Json.JsonList uu___11 in
                ("ctx", uu___10) in
              [uu___9] in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___
type error_handler =
  {
  eh_name: Prims.string ;
  eh_add_one: issue -> unit ;
  eh_count_errors: unit -> Prims.int ;
  eh_report: unit -> issue Prims.list ;
  eh_clear: unit -> unit }
let (__proj__Mkerror_handler__item__eh_name : error_handler -> Prims.string)
  =
  fun projectee ->
    match projectee with
    | { eh_name; eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_name
let (__proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> unit) =
  fun projectee ->
    match projectee with
    | { eh_name; eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_add_one
let (__proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> unit -> Prims.int) =
  fun projectee ->
    match projectee with
    | { eh_name; eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_count_errors
let (__proj__Mkerror_handler__item__eh_report :
  error_handler -> unit -> issue Prims.list) =
  fun projectee ->
    match projectee with
    | { eh_name; eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_report
let (__proj__Mkerror_handler__item__eh_clear : error_handler -> unit -> unit)
  =
  fun projectee ->
    match projectee with
    | { eh_name; eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_clear
let (ctx_doc : Prims.string Prims.list -> FStarC_Pprint.document) =
  fun ctx ->
    let uu___ = FStarC_Options.error_contexts () in
    if uu___
    then
      let uu___1 =
        FStarC_Compiler_List.map
          (fun s ->
             let uu___2 =
               let uu___3 = FStarC_Pprint.doc_of_string "> " in
               let uu___4 = FStarC_Pprint.doc_of_string s in
               FStarC_Pprint.op_Hat_Hat uu___3 uu___4 in
             FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___2) ctx in
      FStarC_Pprint.concat uu___1
    else FStarC_Pprint.empty
let (issue_message : issue -> FStarC_Errors_Msg.error_message) =
  fun i ->
    let uu___ = let uu___1 = ctx_doc i.issue_ctx in [uu___1] in
    FStarC_Compiler_List.op_At i.issue_msg uu___
let (string_of_issue_level : issue_level -> Prims.string) =
  fun il ->
    match il with
    | EInfo -> "Info"
    | EWarning -> "Warning"
    | EError -> "Error"
    | ENotImplemented -> "Feature not yet implemented: "
let (issue_level_of_string : Prims.string -> issue_level) =
  fun uu___ ->
    match uu___ with
    | "Info" -> EInfo
    | "Warning" -> EWarning
    | "Error" -> EError
    | uu___1 -> ENotImplemented
let optional_def :
  'a .
    ('a -> FStarC_Pprint.document) ->
      FStarC_Pprint.document ->
        'a FStar_Pervasives_Native.option -> FStarC_Pprint.document
  =
  fun f ->
    fun def ->
      fun o ->
        match o with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None -> def
let (format_issue' : Prims.bool -> issue -> Prims.string) =
  fun print_hdr ->
    fun issue1 ->
      let level_header =
        let uu___ = string_of_issue_level issue1.issue_level in
        FStarC_Pprint.doc_of_string uu___ in
      let num_opt =
        if (issue1.issue_level = EError) || (issue1.issue_level = EWarning)
        then
          let uu___ = FStarC_Pprint.blank Prims.int_one in
          let uu___1 =
            let uu___2 = FStarC_Pprint.doc_of_string "<unknown>" in
            optional_def
              (fun n ->
                 let uu___3 = FStarC_Compiler_Util.string_of_int n in
                 FStarC_Pprint.doc_of_string uu___3) uu___2
              issue1.issue_number in
          FStarC_Pprint.op_Hat_Hat uu___ uu___1
        else FStarC_Pprint.empty in
      let r = issue1.issue_range in
      let atrng =
        match r with
        | FStar_Pervasives_Native.Some r1 when
            r1 <> FStarC_Compiler_Range_Type.dummyRange ->
            let uu___ = FStarC_Pprint.blank Prims.int_one in
            let uu___1 =
              let uu___2 = FStarC_Pprint.doc_of_string "at" in
              let uu___3 =
                let uu___4 = FStarC_Pprint.blank Prims.int_one in
                let uu___5 =
                  let uu___6 =
                    FStarC_Compiler_Range_Ops.string_of_use_range r1 in
                  FStarC_Pprint.doc_of_string uu___6 in
                FStarC_Pprint.op_Hat_Hat uu___4 uu___5 in
              FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
            FStarC_Pprint.op_Hat_Hat uu___ uu___1
        | uu___ -> FStarC_Pprint.empty in
      let hdr =
        if print_hdr
        then
          let uu___ = FStarC_Pprint.doc_of_string "*" in
          let uu___1 =
            let uu___2 = FStarC_Pprint.blank Prims.int_one in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = FStarC_Pprint.doc_of_string ":" in
                    FStarC_Pprint.op_Hat_Hat uu___7 FStarC_Pprint.hardline in
                  FStarC_Pprint.op_Hat_Hat atrng uu___6 in
                FStarC_Pprint.op_Hat_Hat num_opt uu___5 in
              FStarC_Pprint.op_Hat_Hat level_header uu___4 in
            FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStarC_Pprint.op_Hat_Hat uu___ uu___1
        else FStarC_Pprint.empty in
      let seealso =
        match r with
        | FStar_Pervasives_Native.Some r1 when
            (let uu___ = FStarC_Compiler_Range_Type.def_range r1 in
             let uu___1 = FStarC_Compiler_Range_Type.use_range r1 in
             uu___ <> uu___1) &&
              (let uu___ = FStarC_Compiler_Range_Type.def_range r1 in
               let uu___1 =
                 FStarC_Compiler_Range_Type.def_range
                   FStarC_Compiler_Range_Type.dummyRange in
               uu___ <> uu___1)
            ->
            let uu___ = FStarC_Pprint.doc_of_string "See also" in
            let uu___1 =
              let uu___2 = FStarC_Pprint.blank Prims.int_one in
              let uu___3 =
                let uu___4 = FStarC_Compiler_Range_Ops.string_of_range r1 in
                FStarC_Pprint.doc_of_string uu___4 in
              FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
            FStarC_Pprint.op_Hat_Hat uu___ uu___1
        | uu___ -> FStarC_Pprint.empty in
      let ctx =
        match issue1.issue_ctx with
        | h::t when FStarC_Options.error_contexts () ->
            let d1 s =
              let uu___ = FStarC_Pprint.doc_of_string "> " in
              let uu___1 = FStarC_Pprint.doc_of_string s in
              FStarC_Pprint.op_Hat_Hat uu___ uu___1 in
            let uu___ = d1 h in
            FStarC_Compiler_List.fold_left
              (fun l ->
                 fun r1 ->
                   let uu___1 =
                     let uu___2 = d1 r1 in
                     FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___2 in
                   FStarC_Pprint.op_Hat_Hat l uu___1) uu___ t
        | uu___ -> FStarC_Pprint.empty in
      let subdoc = FStarC_Errors_Msg.subdoc' print_hdr in
      let mainmsg =
        let uu___ =
          FStarC_Compiler_List.map
            (fun d -> let uu___1 = FStarC_Pprint.group d in subdoc uu___1)
            issue1.issue_msg in
        FStarC_Pprint.concat uu___ in
      let doc =
        let uu___ =
          let uu___1 =
            let uu___2 = subdoc seealso in
            let uu___3 = subdoc ctx in FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStarC_Pprint.op_Hat_Hat mainmsg uu___1 in
        FStarC_Pprint.op_Hat_Hat hdr uu___ in
      FStarC_Errors_Msg.renderdoc doc
let (format_issue : issue -> Prims.string) =
  fun issue1 -> format_issue' true issue1
let (print_issue_json : issue -> unit) =
  fun issue1 ->
    let uu___ =
      let uu___1 = json_of_issue issue1 in FStarC_Json.string_of_json uu___1 in
    FStarC_Compiler_Util.print1_error "%s\n" uu___
let (print_issue_rendered : issue -> unit) =
  fun issue1 ->
    let printer =
      match issue1.issue_level with
      | EInfo ->
          (fun s ->
             let uu___ = FStarC_Compiler_Util.colorize_cyan s in
             FStarC_Compiler_Util.print_string uu___)
      | EWarning -> FStarC_Compiler_Util.print_warning
      | EError -> FStarC_Compiler_Util.print_error
      | ENotImplemented -> FStarC_Compiler_Util.print_error in
    let uu___ = let uu___1 = format_issue issue1 in Prims.strcat uu___1 "\n" in
    printer uu___
let (print_issue : issue -> unit) =
  fun issue1 ->
    let uu___ = FStarC_Options.message_format () in
    match uu___ with
    | FStarC_Options.Human -> print_issue_rendered issue1
    | FStarC_Options.Json -> print_issue_json issue1
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1 ->
    fun i2 ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          Prims.int_zero
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
          (Prims.of_int (-1))
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
          Prims.int_one
      | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some r2) ->
          FStarC_Compiler_Range_Ops.compare_use_range r1 r2
let (dummy_ide_rng : FStarC_Compiler_Range_Type.rng) =
  let uu___ = FStarC_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  let uu___1 = FStarC_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  FStarC_Compiler_Range_Type.mk_rng "<input>" uu___ uu___1
let (maybe_bound_rng :
  FStarC_Compiler_Range_Type.range -> FStarC_Compiler_Range_Type.range) =
  fun r ->
    let uu___ = FStarC_Compiler_Effect.op_Bang error_range_bound in
    match uu___ with
    | FStar_Pervasives_Native.Some r' ->
        FStarC_Compiler_Range_Ops.bound_range r r'
    | FStar_Pervasives_Native.None -> r
let (fixup_issue_range : issue -> issue) =
  fun i ->
    let rng =
      match i.issue_range with
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Effect.op_Bang fallback_range
      | FStar_Pervasives_Native.Some range ->
          let use_rng = FStarC_Compiler_Range_Type.use_range range in
          let use_rng' =
            if
              (use_rng <> FStarC_Compiler_Range_Type.dummy_rng) &&
                (use_rng <> dummy_ide_rng)
            then use_rng
            else
              (let uu___1 =
                 let uu___2 = FStarC_Compiler_Effect.op_Bang fallback_range in
                 FStar_Pervasives_Native.uu___is_Some uu___2 in
               if uu___1
               then
                 let uu___2 =
                   let uu___3 = FStarC_Compiler_Effect.op_Bang fallback_range in
                   FStar_Pervasives_Native.__proj__Some__item__v uu___3 in
                 FStarC_Compiler_Range_Type.use_range uu___2
               else use_rng) in
          let uu___ = FStarC_Compiler_Range_Type.set_use_range range use_rng' in
          FStar_Pervasives_Native.Some uu___ in
    let uu___ = FStarC_Compiler_Util.map_opt rng maybe_bound_rng in
    {
      issue_msg = (i.issue_msg);
      issue_level = (i.issue_level);
      issue_range = uu___;
      issue_number = (i.issue_number);
      issue_ctx = (i.issue_ctx)
    }
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print ->
    let issues = FStarC_Compiler_Util.mk_ref [] in
    let err_count = FStarC_Compiler_Util.mk_ref Prims.int_zero in
    let add_one e =
      if e.issue_level = EError
      then
        (let uu___1 =
           let uu___2 = FStarC_Compiler_Effect.op_Bang err_count in
           Prims.int_one + uu___2 in
         FStarC_Compiler_Effect.op_Colon_Equals err_count uu___1)
      else ();
      (match e.issue_level with
       | EInfo when print -> print_issue e
       | uu___2 when print && (FStarC_Compiler_Debug.any ()) -> print_issue e
       | uu___2 ->
           let uu___3 =
             let uu___4 = FStarC_Compiler_Effect.op_Bang issues in e ::
               uu___4 in
           FStarC_Compiler_Effect.op_Colon_Equals issues uu___3);
      (let uu___3 =
         (FStarC_Options.defensive_abort ()) &&
           (e.issue_number = (FStar_Pervasives_Native.Some defensive_errno)) in
       if uu___3 then failwith "Aborting due to --defensive abort" else ()) in
    let count_errors uu___ = FStarC_Compiler_Effect.op_Bang err_count in
    let report uu___ =
      let unique_issues =
        let uu___1 = FStarC_Compiler_Effect.op_Bang issues in
        FStarC_Compiler_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu___1 in
      let sorted_unique_issues =
        FStarC_Compiler_List.sortWith compare_issues unique_issues in
      if print
      then FStarC_Compiler_List.iter print_issue sorted_unique_issues
      else ();
      sorted_unique_issues in
    let clear uu___ =
      FStarC_Compiler_Effect.op_Colon_Equals issues [];
      FStarC_Compiler_Effect.op_Colon_Equals err_count Prims.int_zero in
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Compiler_Util.string_of_bool print in
        Prims.strcat uu___2 ")" in
      Prims.strcat "default handler (print=" uu___1 in
    {
      eh_name = uu___;
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear
    }
let (default_handler : error_handler) = mk_default_handler true
let (current_handler : error_handler FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref default_handler
let (mk_issue :
  issue_level ->
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
      FStarC_Errors_Msg.error_message ->
        Prims.int FStar_Pervasives_Native.option ->
          Prims.string Prims.list -> issue)
  =
  fun level ->
    fun range ->
      fun msg ->
        fun n ->
          fun ctx ->
            {
              issue_msg = msg;
              issue_level = level;
              issue_range = range;
              issue_number = n;
              issue_ctx = ctx
            }
let (get_err_count : unit -> Prims.int) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_count_errors ()
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h ->
    fun issue1 ->
      let issue2 = fixup_issue_range issue1 in
      h.eh_add_one issue2;
      if issue2.issue_level <> EInfo
      then
        ((let uu___2 =
            let uu___3 =
              FStarC_Compiler_Effect.op_Bang FStarC_Options.abort_counter in
            uu___3 - Prims.int_one in
          FStarC_Compiler_Effect.op_Colon_Equals FStarC_Options.abort_counter
            uu___2);
         (let uu___2 =
            let uu___3 =
              FStarC_Compiler_Effect.op_Bang FStarC_Options.abort_counter in
            uu___3 = Prims.int_zero in
          if uu___2 then failwith "Aborting due to --abort_on" else ()))
      else ()
let (add_one : issue -> unit) =
  fun issue1 ->
    FStarC_Compiler_Util.atomically
      (fun uu___ ->
         let uu___1 = FStarC_Compiler_Effect.op_Bang current_handler in
         wrapped_eh_add_one uu___1 issue1)
let (add_many : issue Prims.list -> unit) =
  fun issues ->
    FStarC_Compiler_Util.atomically
      (fun uu___ ->
         let uu___1 =
           let uu___2 = FStarC_Compiler_Effect.op_Bang current_handler in
           wrapped_eh_add_one uu___2 in
         FStarC_Compiler_List.iter uu___1 issues)
let (add_issues : issue Prims.list -> unit) = fun issues -> add_many issues
let (report_all : unit -> issue Prims.list) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_report ()
let (clear : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_clear ()
let (set_handler : error_handler -> unit) =
  fun handler ->
    let issues = report_all () in
    clear ();
    FStarC_Compiler_Effect.op_Colon_Equals current_handler handler;
    add_many issues
type error_context_t =
  {
  push: Prims.string -> unit ;
  pop: unit -> Prims.string ;
  clear: unit -> unit ;
  get: unit -> Prims.string Prims.list ;
  set: Prims.string Prims.list -> unit }
let (__proj__Mkerror_context_t__item__push :
  error_context_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> push
let (__proj__Mkerror_context_t__item__pop :
  error_context_t -> unit -> Prims.string) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> pop
let (__proj__Mkerror_context_t__item__clear :
  error_context_t -> unit -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> clear1
let (__proj__Mkerror_context_t__item__get :
  error_context_t -> unit -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> get
let (__proj__Mkerror_context_t__item__set :
  error_context_t -> Prims.string Prims.list -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> set
let (error_context : error_context_t) =
  let ctxs = FStarC_Compiler_Util.mk_ref [] in
  let push s =
    let uu___ =
      let uu___1 = FStarC_Compiler_Effect.op_Bang ctxs in s :: uu___1 in
    FStarC_Compiler_Effect.op_Colon_Equals ctxs uu___ in
  let pop s =
    let uu___ = FStarC_Compiler_Effect.op_Bang ctxs in
    match uu___ with
    | h::t -> (FStarC_Compiler_Effect.op_Colon_Equals ctxs t; h)
    | uu___1 -> failwith "cannot pop error prefix..." in
  let clear1 uu___ = FStarC_Compiler_Effect.op_Colon_Equals ctxs [] in
  let get uu___ = FStarC_Compiler_Effect.op_Bang ctxs in
  let set c = FStarC_Compiler_Effect.op_Colon_Equals ctxs c in
  { push; pop; clear = clear1; get; set }
let (get_ctx : unit -> Prims.string Prims.list) =
  fun uu___ -> error_context.get ()
let (maybe_add_backtrace :
  FStarC_Errors_Msg.error_message -> FStarC_Errors_Msg.error_message) =
  fun msg ->
    let uu___ = FStarC_Options.trace_error () in
    if uu___
    then
      let uu___1 =
        let uu___2 = FStarC_Errors_Msg.backtrace_doc () in [uu___2] in
      FStarC_Compiler_List.op_At msg uu___1
    else msg
let (warn_unsafe_options :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
    Prims.string -> unit)
  =
  fun rng_opt ->
    fun msg ->
      let uu___ = FStarC_Options.report_assumes () in
      match uu___ with
      | FStar_Pervasives_Native.Some "warn" ->
          let uu___1 =
            let uu___2 =
              FStarC_Errors_Msg.mkmsg
                (Prims.strcat "Every use of this option triggers a warning: "
                   msg) in
            mk_issue EWarning rng_opt uu___2
              (FStar_Pervasives_Native.Some warn_on_use_errno) [] in
          add_one uu___1
      | FStar_Pervasives_Native.Some "error" ->
          let uu___1 =
            let uu___2 =
              FStarC_Errors_Msg.mkmsg
                (Prims.strcat "Every use of this option triggers an error: "
                   msg) in
            mk_issue EError rng_opt uu___2
              (FStar_Pervasives_Native.Some warn_on_use_errno) [] in
          add_one uu___1
      | uu___1 -> ()
let (set_option_warning_callback_range :
  FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option -> unit) =
  fun ropt ->
    FStarC_Options.set_option_warning_callback (warn_unsafe_options ropt)
let (uu___0 :
  (((Prims.string -> FStarC_Errors_Codes.error_setting Prims.list) -> unit) *
    (unit -> FStarC_Errors_Codes.error_setting Prims.list)))
  =
  let parser_callback =
    FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let error_flags = FStarC_Compiler_Util.smap_create (Prims.of_int (10)) in
  let set_error_flags uu___ =
    let parse s =
      let uu___1 = FStarC_Compiler_Effect.op_Bang parser_callback in
      match uu___1 with
      | FStar_Pervasives_Native.None ->
          failwith "Callback for parsing warn_error strings is not set"
      | FStar_Pervasives_Native.Some f -> f s in
    let we = FStarC_Options.warn_error () in
    try
      (fun uu___1 ->
         match () with
         | () ->
             let r = parse we in
             (FStarC_Compiler_Util.smap_add error_flags we
                (FStar_Pervasives_Native.Some r);
              FStarC_Getopt.Success)) ()
    with
    | Invalid_warn_error_setting msg ->
        (FStarC_Compiler_Util.smap_add error_flags we
           FStar_Pervasives_Native.None;
         FStarC_Getopt.Error
           (Prims.strcat "Invalid --warn_error setting: "
              (Prims.strcat msg "\n"))) in
  let get_error_flags uu___ =
    let we = FStarC_Options.warn_error () in
    let uu___1 = FStarC_Compiler_Util.smap_try_find error_flags we in
    match uu___1 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some w) -> w
    | uu___2 -> FStarC_Errors_Codes.default_settings in
  let set_callbacks f =
    FStarC_Compiler_Effect.op_Colon_Equals parser_callback
      (FStar_Pervasives_Native.Some f);
    FStarC_Options.set_error_flags_callback set_error_flags;
    FStarC_Options.set_option_warning_callback
      (warn_unsafe_options FStar_Pervasives_Native.None) in
  (set_callbacks, get_error_flags)
let (t_set_parse_warn_error :
  (Prims.string -> FStarC_Errors_Codes.error_setting Prims.list) -> unit) =
  match uu___0 with
  | (t_set_parse_warn_error1, error_flags) -> t_set_parse_warn_error1
let (error_flags : unit -> FStarC_Errors_Codes.error_setting Prims.list) =
  match uu___0 with | (t_set_parse_warn_error1, error_flags1) -> error_flags1
let (set_parse_warn_error :
  (Prims.string -> FStarC_Errors_Codes.error_setting Prims.list) -> unit) =
  t_set_parse_warn_error
let (lookup :
  FStarC_Errors_Codes.error_code -> FStarC_Errors_Codes.error_setting) =
  fun err ->
    let flags = error_flags () in
    let uu___ = lookup_error flags err in
    match uu___ with
    | (v, level, i) ->
        let with_level level1 = (v, level1, i) in
        (match v with
         | FStarC_Errors_Codes.Warning_Defensive when
             (FStarC_Options.defensive_error ()) ||
               (FStarC_Options.defensive_abort ())
             -> with_level FStarC_Errors_Codes.CAlwaysError
         | FStarC_Errors_Codes.Warning_WarnOnUse ->
             let level' =
               let uu___1 = FStarC_Options.report_assumes () in
               match uu___1 with
               | FStar_Pervasives_Native.None -> level
               | FStar_Pervasives_Native.Some "warn" ->
                   (match level with
                    | FStarC_Errors_Codes.CSilent ->
                        FStarC_Errors_Codes.CWarning
                    | uu___2 -> level)
               | FStar_Pervasives_Native.Some "error" ->
                   (match level with
                    | FStarC_Errors_Codes.CWarning ->
                        FStarC_Errors_Codes.CError
                    | FStarC_Errors_Codes.CSilent ->
                        FStarC_Errors_Codes.CError
                    | uu___2 -> level)
               | FStar_Pervasives_Native.Some uu___2 -> level in
             with_level level'
         | uu___1 -> with_level level)
let (log_issue_ctx :
  FStarC_Compiler_Range_Type.range ->
    (FStarC_Errors_Codes.error_code * FStarC_Errors_Msg.error_message) ->
      Prims.string Prims.list -> unit)
  =
  fun r ->
    fun uu___ ->
      fun ctx ->
        match uu___ with
        | (e, msg) ->
            let msg1 = maybe_add_backtrace msg in
            let uu___1 = lookup e in
            (match uu___1 with
             | (uu___2, FStarC_Errors_Codes.CAlwaysError, errno1) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg1
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStarC_Errors_Codes.CError, errno1) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg1
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStarC_Errors_Codes.CWarning, errno1) ->
                 add_one
                   (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg1
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStarC_Errors_Codes.CSilent, uu___3) -> ()
             | (uu___2, FStarC_Errors_Codes.CFatal, errno1) ->
                 let i =
                   mk_issue EError (FStar_Pervasives_Native.Some r) msg1
                     (FStar_Pervasives_Native.Some errno1) ctx in
                 let uu___3 = FStarC_Options.ide () in
                 if uu___3
                 then add_one i
                 else
                   (let uu___5 =
                      let uu___6 = format_issue i in
                      Prims.strcat
                        "don't use log_issue to report fatal error, should use raise_error: "
                        uu___6 in
                    failwith uu___5))
let info :
  'posut .
    'posut FStarC_Class_HasRange.hasRange ->
      'posut ->
        unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> unit
  =
  fun uu___ ->
    fun r ->
      fun uu___1 ->
        fun uu___2 ->
          fun msg ->
            let rng = FStarC_Class_HasRange.pos uu___ r in
            let msg1 = FStarC_Errors_Msg.to_doc_list uu___2 msg in
            let msg2 = maybe_add_backtrace msg1 in
            let ctx = get_ctx () in
            add_one
              (mk_issue EInfo (FStar_Pervasives_Native.Some rng) msg2
                 FStar_Pervasives_Native.None ctx)
let diag :
  'posut .
    'posut FStarC_Class_HasRange.hasRange ->
      'posut ->
        unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> unit
  =
  fun uu___ ->
    fun r ->
      fun uu___1 ->
        fun uu___2 ->
          fun msg ->
            let uu___3 = FStarC_Compiler_Debug.any () in
            if uu___3 then info uu___ r () uu___2 msg else ()
let raise_error :
  'a 'posut .
    'posut FStarC_Class_HasRange.hasRange ->
      'posut ->
        FStarC_Errors_Codes.error_code ->
          unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> 'a
  =
  fun uu___ ->
    fun r ->
      fun e ->
        fun uu___1 ->
          fun uu___2 ->
            fun msg ->
              let rng = FStarC_Class_HasRange.pos uu___ r in
              let msg1 = FStarC_Errors_Msg.to_doc_list uu___2 msg in
              let uu___3 =
                let uu___4 =
                  let uu___5 = maybe_add_backtrace msg1 in
                  let uu___6 = error_context.get () in
                  (e, uu___5, rng, uu___6) in
                Error uu___4 in
              FStarC_Compiler_Effect.raise uu___3
let log_issue :
  'posut .
    'posut FStarC_Class_HasRange.hasRange ->
      'posut ->
        FStarC_Errors_Codes.error_code ->
          unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> unit
  =
  fun uu___ ->
    fun r ->
      fun e ->
        fun uu___1 ->
          fun uu___2 ->
            fun msg ->
              let rng = FStarC_Class_HasRange.pos uu___ r in
              let msg1 = FStarC_Errors_Msg.to_doc_list uu___2 msg in
              let ctx = error_context.get () in
              log_issue_ctx rng (e, msg1) ctx
let raise_error0 :
  'a .
    FStarC_Errors_Codes.error_code ->
      unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> 'a
  =
  fun e ->
    fun uu___ ->
      fun uu___1 ->
        fun msg ->
          raise_error FStarC_Class_HasRange.hasRange_range
            FStarC_Compiler_Range_Type.dummyRange e () uu___1 msg
let (log_issue0 :
  FStarC_Errors_Codes.error_code ->
    unit -> Obj.t FStarC_Errors_Msg.is_error_message -> Obj.t -> unit)
  =
  fun e ->
    fun uu___ ->
      fun uu___1 ->
        fun msg ->
          log_issue FStarC_Class_HasRange.hasRange_range
            FStarC_Compiler_Range_Type.dummyRange e () uu___1 msg
let diag0 : 't . 't FStarC_Errors_Msg.is_error_message -> 't -> unit =
  fun uu___ ->
    fun msg ->
      diag FStarC_Class_HasRange.hasRange_range
        FStarC_Compiler_Range_Type.dummyRange () (Obj.magic uu___)
        (Obj.magic msg)
let (add_errors : error Prims.list -> unit) =
  fun errs ->
    FStarC_Compiler_Util.atomically
      (fun uu___ ->
         FStarC_Compiler_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (e, msg, r, ctx) -> log_issue_ctx r (e, msg) ctx) errs)
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun e ->
    match e with
    | Error (e1, msg, r, ctx) ->
        let errno1 = let uu___ = lookup e1 in error_number uu___ in
        FStar_Pervasives_Native.Some
          (mk_issue EError (FStar_Pervasives_Native.Some r) msg
             (FStar_Pervasives_Native.Some errno1) ctx)
    | uu___ -> FStar_Pervasives_Native.None
let (err_exn : Prims.exn -> unit) =
  fun exn ->
    if exn = Stop
    then ()
    else
      (let uu___1 = issue_of_exn exn in
       match uu___1 with
       | FStar_Pervasives_Native.Some issue1 -> add_one issue1
       | FStar_Pervasives_Native.None -> FStarC_Compiler_Effect.raise exn)
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___ ->
    match uu___ with | Error uu___1 -> true | Stop -> true | uu___1 -> false
let (stop_if_err : unit -> unit) =
  fun uu___ ->
    let uu___1 = let uu___2 = get_err_count () in uu___2 > Prims.int_zero in
    if uu___1 then FStarC_Compiler_Effect.raise Stop else ()
let with_ctx : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      error_context.push s;
      (let r =
         let uu___1 = FStarC_Options.trace_error () in
         if uu___1
         then let uu___2 = f () in FStar_Pervasives.Inr uu___2
         else
           (try
              (fun uu___3 ->
                 match () with
                 | () -> let uu___4 = f () in FStar_Pervasives.Inr uu___4) ()
            with
            | FStarC_Compiler_Effect.Failure msg ->
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = error_context.get () in ctx_doc uu___9 in
                        [uu___8] in
                      FStarC_Errors_Msg.rendermsg uu___7 in
                    Prims.strcat msg uu___6 in
                  FStarC_Compiler_Effect.Failure uu___5 in
                FStar_Pervasives.Inl uu___4
            | ex -> FStar_Pervasives.Inl ex) in
       (let uu___2 = error_context.pop () in ());
       (match r with
        | FStar_Pervasives.Inr r1 -> r1
        | FStar_Pervasives.Inl e -> FStarC_Compiler_Effect.raise e))
let with_ctx_if : 'a . Prims.bool -> Prims.string -> (unit -> 'a) -> 'a =
  fun b -> fun s -> fun f -> if b then with_ctx s f else f ()
let catch_errors_aux :
  'a .
    (unit -> 'a) ->
      (issue Prims.list * issue Prims.list * 'a
        FStar_Pervasives_Native.option)
  =
  fun f ->
    let newh = mk_default_handler false in
    let old = FStarC_Compiler_Effect.op_Bang current_handler in
    FStarC_Compiler_Effect.op_Colon_Equals current_handler newh;
    (let finally_restore uu___1 =
       let all_issues = newh.eh_report () in
       FStarC_Compiler_Effect.op_Colon_Equals current_handler old;
       (let uu___3 =
          FStarC_Compiler_List.partition (fun i -> i.issue_level = EError)
            all_issues in
        match uu___3 with | (errs, rest) -> (errs, rest)) in
     let r =
       try
         (fun uu___1 ->
            match () with
            | () -> let uu___2 = f () in FStar_Pervasives_Native.Some uu___2)
           ()
       with
       | uu___1 ->
           if handleable uu___1
           then (err_exn uu___1; FStar_Pervasives_Native.None)
           else
             (let uu___2 = finally_restore () in
              FStarC_Compiler_Effect.raise uu___1) in
     let uu___1 = finally_restore () in
     match uu___1 with | (errs, rest) -> (errs, rest, r))
let no_ctx : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let save = error_context.get () in
    error_context.clear (); (let res = f () in error_context.set save; res)
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f ->
    let uu___ = catch_errors_aux f in
    match uu___ with
    | (errs, rest, r) ->
        ((let uu___2 =
            let uu___3 = FStarC_Compiler_Effect.op_Bang current_handler in
            uu___3.eh_add_one in
          FStarC_Compiler_List.iter uu___2 rest);
         (errs, r))
let catch_errors_and_ignore_rest :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f ->
    let uu___ = catch_errors_aux f in
    match uu___ with
    | (errs, rest, r) ->
        ((let uu___2 =
            let uu___3 = FStarC_Compiler_Effect.op_Bang current_handler in
            uu___3.eh_add_one in
          let uu___3 =
            FStarC_Compiler_List.filter (fun i -> i.issue_level = EInfo) rest in
          FStarC_Compiler_List.iter uu___2 uu___3);
         (errs, r))
let (find_multiset_discrepancy :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1 ->
    fun l2 ->
      let sort = FStarC_Compiler_List.sortWith (fun x -> fun y -> x - y) in
      let rec collect l =
        match l with
        | [] -> []
        | hd::tl ->
            let uu___ = collect tl in
            (match uu___ with
             | [] -> [(hd, Prims.int_one)]
             | (h, n)::t ->
                 if h = hd
                 then (h, (n + Prims.int_one)) :: t
                 else (hd, Prims.int_one) :: (h, n) :: t) in
      let l11 = let uu___ = sort l1 in collect uu___ in
      let l21 = let uu___ = sort l2 in collect uu___ in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], []) -> FStar_Pervasives_Native.None
        | ((e, n)::uu___, []) ->
            FStar_Pervasives_Native.Some (e, n, Prims.int_zero)
        | ([], (e, n)::uu___) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n)
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2 in
      aux l11 l21
let raise_error_doc :
  'a .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Errors_Codes.error_code -> FStarC_Errors_Msg.error_message -> 'a
  =
  fun rng ->
    fun code ->
      fun msg ->
        raise_error FStarC_Class_HasRange.hasRange_range rng code ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic msg)
let (log_issue_doc :
  FStarC_Compiler_Range_Type.range ->
    FStarC_Errors_Codes.error_code -> FStarC_Errors_Msg.error_message -> unit)
  =
  fun rng ->
    fun code ->
      fun msg ->
        log_issue FStarC_Class_HasRange.hasRange_range rng code ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic msg)
let raise_error_text :
  'a .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Errors_Codes.error_code -> Prims.string -> 'a
  =
  fun rng ->
    fun code ->
      fun msg ->
        raise_error FStarC_Class_HasRange.hasRange_range rng code ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic msg)
let (log_issue_text :
  FStarC_Compiler_Range_Type.range ->
    FStarC_Errors_Codes.error_code -> Prims.string -> unit)
  =
  fun rng ->
    fun code ->
      fun msg ->
        log_issue FStarC_Class_HasRange.hasRange_range rng code ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic msg)