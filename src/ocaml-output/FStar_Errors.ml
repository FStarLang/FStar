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
exception Empty_frag 
let uu___is_Empty_frag : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____66 -> false
  
let diag : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____73 = FStar_Options.debug_any ()  in
      if uu____73
      then
        let uu____74 =
          let uu____75 = FStar_Range.string_of_range r  in
          FStar_Util.format2 "%s : (Diagnostic) %s\n" uu____75 msg  in
        FStar_Util.print_string uu____74
      else ()
  
let warn : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____83 = FStar_Range.string_of_range r  in
      FStar_Util.print2_error "%s: (Warning) %s\n" uu____83 msg
  
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
  let clear_prefix uu____155 = FStar_ST.write pfx None  in
  let append_prefix s =
    let uu____163 = FStar_ST.read pfx  in
    match uu____163 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s)  in
  { set_prefix; append_prefix; clear_prefix } 
let add_errors : (Prims.string * FStar_Range.range) Prims.list -> Prims.unit
  =
  fun errs  ->
    let errs1 =
      FStar_All.pipe_right errs
        (FStar_List.map
           (fun uu____192  ->
              match uu____192 with
              | (msg,r) ->
                  let uu____199 = message_prefix.append_prefix msg  in
                  (r, uu____199)))
       in
    let n_errs = FStar_List.length errs1  in
    FStar_Util.atomically
      (fun uu____204  ->
         (let uu____206 =
            let uu____210 = FStar_ST.read verification_errs  in
            FStar_List.append errs1 uu____210  in
          FStar_ST.write verification_errs uu____206);
         (let uu____226 =
            let uu____227 = FStar_ST.read num_errs  in uu____227 + n_errs  in
          FStar_ST.write num_errs uu____226))
  
let mk_error : Prims.string -> FStar_Range.range -> Prims.string =
  fun msg  ->
    fun r  ->
      if r.FStar_Range.use_range <> r.FStar_Range.def_range
      then
        let uu____240 = FStar_Range.string_of_use_range r  in
        let uu____241 = FStar_Range.string_of_range r  in
        FStar_Util.format3 "%s: (Error) %s (see %s)\n" uu____240 msg
          uu____241
      else
        (let uu____243 = FStar_Range.string_of_range r  in
         FStar_Util.format2 "%s: (Error) %s\n" uu____243 msg)
  
let report_all : Prims.unit -> Prims.nat =
  fun uu____247  ->
    let all_errs =
      FStar_Util.atomically
        (fun uu____255  ->
           let x = FStar_ST.read verification_errs  in
           FStar_ST.write verification_errs []; x)
       in
    let all_errs1 =
      FStar_List.sortWith
        (fun uu____279  ->
           fun uu____280  ->
             match (uu____279, uu____280) with
             | ((r1,uu____290),(r2,uu____292)) ->
                 FStar_Range.compare_use_range r1 r2) all_errs
       in
    FStar_All.pipe_right all_errs1
      (FStar_List.iter
         (fun uu____303  ->
            match uu____303 with
            | (r,msg) ->
                let uu____308 = mk_error msg r  in
                FStar_Util.print_error uu____308));
    FStar_List.length all_errs1
  
let handle_err : Prims.bool -> Prims.exn -> Prims.unit =
  fun warning  ->
    fun e  ->
      match e with
      | Error (msg,r) ->
          let msg1 = message_prefix.append_prefix msg  in
          let uu____321 = FStar_Range.string_of_range r  in
          FStar_Util.print3_error "%s : %s %s\n" uu____321
            (if warning then "(Warning)" else "(Error)") msg1
      | FStar_Util.NYI msg ->
          let msg1 = message_prefix.append_prefix msg  in
          FStar_Util.print1_error "Feature not yet implemented: %s" msg1
      | Err msg ->
          let msg1 = message_prefix.append_prefix msg  in
          FStar_Util.print1_error "Error: %s" msg1
      | uu____327 -> Prims.raise e
  
let handleable : Prims.exn -> Prims.bool =
  fun uu___54_330  ->
    match uu___54_330 with
    | Error _|FStar_Util.NYI _|Err _ -> true
    | uu____334 -> false
  
let report : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      FStar_Util.incr num_errs;
      (let msg1 = message_prefix.append_prefix msg  in
       let uu____346 = mk_error msg1 r  in FStar_Util.print_error uu____346)
  
let get_err_count : Prims.unit -> Prims.int =
  fun uu____349  -> FStar_ST.read num_errs 