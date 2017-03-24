open Prims
exception Err of Prims.string 
let uu___is_Err : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____6 -> true | uu____7 -> false
  
let __proj__Err__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____14 -> uu____14 
exception Error of (Prims.string * FStar_Range.range) 
let uu___is_Error : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____22 -> true | uu____25 -> false
  
let __proj__Error__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Error uu____36 -> uu____36 
exception Warning of (Prims.string * FStar_Range.range) 
let uu___is_Warning : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____46 -> true | uu____49 -> false
  
let __proj__Warning__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Warning uu____60 -> uu____60 
let diag : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____69 = FStar_Options.debug_any ()  in
      if uu____69
      then
        FStar_Util.print_string
          (let _0_131 = FStar_Range.string_of_range r  in
           FStar_Util.format2 "%s : (Diagnostic) %s\n" _0_131 msg)
      else ()
  
let warn : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let _0_132 = FStar_Range.string_of_range r  in
      FStar_Util.print2_error "%s: (Warning) %s\n" _0_132 msg
  
let num_errs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let verification_errs :
  (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit ;
  append_prefix: Prims.string -> Prims.string ;
  clear_prefix: Prims.unit -> Prims.unit }
let message_prefix : error_message_prefix =
  let pfx = FStar_Util.mk_ref None  in
  let set_prefix s = FStar_ST.write pfx (Some s)  in
  let clear_prefix uu____148 = FStar_ST.write pfx None  in
  let append_prefix s =
    let uu____156 = FStar_ST.read pfx  in
    match uu____156 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s)  in
  { set_prefix; append_prefix; clear_prefix } 
let add_errors : (Prims.string * FStar_Range.range) Prims.list -> Prims.unit
  =
  fun errs  ->
    let errs =
      FStar_All.pipe_right errs
        (FStar_List.map
           (fun uu____185  ->
              match uu____185 with
              | (msg,r) ->
                  let _0_133 = message_prefix.append_prefix msg  in
                  (r, _0_133)))
       in
    let n_errs = FStar_List.length errs  in
    FStar_Util.atomically
      (fun uu____196  ->
         (let _0_135 =
            let _0_134 = FStar_ST.read verification_errs  in
            FStar_List.append errs _0_134  in
          FStar_ST.write verification_errs _0_135);
         (let _0_137 =
            let _0_136 = FStar_ST.read num_errs  in _0_136 + n_errs  in
          FStar_ST.write num_errs _0_137))
  
let mk_error : Prims.string -> FStar_Range.range -> Prims.string =
  fun msg  ->
    fun r  ->
      if r.FStar_Range.use_range <> r.FStar_Range.def_range
      then
        let _0_139 = FStar_Range.string_of_use_range r  in
        let _0_138 = FStar_Range.string_of_range r  in
        FStar_Util.format3 "%s: (Error) %s (see %s)\n" _0_139 msg _0_138
      else
        (let _0_140 = FStar_Range.string_of_range r  in
         FStar_Util.format2 "%s: (Error) %s\n" _0_140 msg)
  
let report_all : Prims.unit -> Prims.nat =
  fun uu____226  ->
    let all_errs =
      FStar_Util.atomically
        (fun uu____234  ->
           let x = FStar_ST.read verification_errs  in
           FStar_ST.write verification_errs []; x)
       in
    let all_errs =
      FStar_List.sortWith
        (fun uu____258  ->
           fun uu____259  ->
             match (uu____258, uu____259) with
             | ((r1,uu____269),(r2,uu____271)) ->
                 FStar_Range.compare_use_range r1 r2) all_errs
       in
    FStar_All.pipe_right all_errs
      (FStar_List.iter
         (fun uu____282  ->
            match uu____282 with
            | (r,msg) -> FStar_Util.print_error (mk_error msg r)));
    FStar_List.length all_errs
  
let handle_err : Prims.bool -> Prims.exn -> Prims.unit =
  fun warning  ->
    fun e  ->
      match e with
      | Error (msg,r) ->
          let msg = message_prefix.append_prefix msg  in
          let _0_141 = FStar_Range.string_of_range r  in
          FStar_Util.print3_error "%s : %s %s\n" _0_141
            (if warning then "(Warning)" else "(Error)") msg
      | FStar_Util.NYI msg ->
          let msg = message_prefix.append_prefix msg  in
          FStar_Util.print1_error "Feature not yet implemented: %s" msg
      | Err msg ->
          let msg = message_prefix.append_prefix msg  in
          FStar_Util.print1_error "Error: %s" msg
      | uu____304 -> Prims.raise e
  
let handleable : Prims.exn -> Prims.bool =
  fun uu___52_307  ->
    match uu___52_307 with
    | Error _|FStar_Util.NYI _|Err _ -> true
    | uu____311 -> false
  
let report : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      FStar_Util.incr num_errs;
      (let msg = message_prefix.append_prefix msg  in
       FStar_Util.print_error (mk_error msg r))
  
let get_err_count : Prims.unit -> Prims.int =
  fun uu____325  -> FStar_ST.read num_errs 