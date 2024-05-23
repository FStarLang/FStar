open Prims
let (anyref : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref false
let (_debug_all : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref false
let (toggle_list :
  (Prims.string * Prims.bool FStar_Compiler_Effect.ref) Prims.list
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref []
type saved_state =
  {
  toggles: (Prims.string * Prims.bool) Prims.list ;
  any: Prims.bool ;
  all: Prims.bool }
let (__proj__Mksaved_state__item__toggles :
  saved_state -> (Prims.string * Prims.bool) Prims.list) =
  fun projectee -> match projectee with | { toggles; any; all;_} -> toggles
let (__proj__Mksaved_state__item__any : saved_state -> Prims.bool) =
  fun projectee -> match projectee with | { toggles; any; all;_} -> any
let (__proj__Mksaved_state__item__all : saved_state -> Prims.bool) =
  fun projectee -> match projectee with | { toggles; any; all;_} -> all
let (snapshot : unit -> saved_state) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Compiler_Effect.op_Bang toggle_list in
      FStar_Compiler_List.map
        (fun uu___3 ->
           match uu___3 with
           | (k, r) ->
               let uu___4 = FStar_Compiler_Effect.op_Bang r in (k, uu___4))
        uu___2 in
    let uu___2 = FStar_Compiler_Effect.op_Bang anyref in
    let uu___3 = FStar_Compiler_Effect.op_Bang _debug_all in
    { toggles = uu___1; any = uu___2; all = uu___3 }
let (register_toggle : Prims.string -> Prims.bool FStar_Compiler_Effect.ref)
  =
  fun k ->
    let r = FStar_Compiler_Util.mk_ref false in
    (let uu___1 = FStar_Compiler_Effect.op_Bang _debug_all in
     if uu___1 then FStar_Compiler_Effect.op_Colon_Equals r true else ());
    (let uu___2 =
       let uu___3 = FStar_Compiler_Effect.op_Bang toggle_list in (k, r) ::
         uu___3 in
     FStar_Compiler_Effect.op_Colon_Equals toggle_list uu___2);
    r
let (get_toggle : Prims.string -> Prims.bool FStar_Compiler_Effect.ref) =
  fun k ->
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang toggle_list in
      FStar_Compiler_List.tryFind
        (fun uu___2 -> match uu___2 with | (k', uu___3) -> k = k') uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some (uu___1, r) -> r
    | FStar_Pervasives_Native.None -> register_toggle k
let (restore : saved_state -> unit) =
  fun snapshot1 ->
    (let uu___1 = FStar_Compiler_Effect.op_Bang toggle_list in
     FStar_Compiler_List.iter
       (fun uu___2 ->
          match uu___2 with
          | (uu___3, r) -> FStar_Compiler_Effect.op_Colon_Equals r false)
       uu___1);
    FStar_Compiler_List.iter
      (fun uu___2 ->
         match uu___2 with
         | (k, b) ->
             let r = get_toggle k in
             FStar_Compiler_Effect.op_Colon_Equals r b) snapshot1.toggles;
    FStar_Compiler_Effect.op_Colon_Equals anyref snapshot1.any;
    FStar_Compiler_Effect.op_Colon_Equals _debug_all snapshot1.all
let (list_all_toggles : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang toggle_list in
    FStar_Compiler_List.map FStar_Pervasives_Native.fst uu___1
let (any : unit -> Prims.bool) =
  fun uu___ ->
    (FStar_Compiler_Effect.op_Bang anyref) ||
      (FStar_Compiler_Effect.op_Bang _debug_all)
let (enable : unit -> unit) =
  fun uu___ -> FStar_Compiler_Effect.op_Colon_Equals anyref true
let (dbg_level : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (low : unit -> Prims.bool) =
  fun uu___ ->
    (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
     uu___1 >= Prims.int_one) || (FStar_Compiler_Effect.op_Bang _debug_all)
let (medium : unit -> Prims.bool) =
  fun uu___ ->
    (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
     uu___1 >= (Prims.of_int (2))) ||
      (FStar_Compiler_Effect.op_Bang _debug_all)
let (high : unit -> Prims.bool) =
  fun uu___ ->
    (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
     uu___1 >= (Prims.of_int (3))) ||
      (FStar_Compiler_Effect.op_Bang _debug_all)
let (extreme : unit -> Prims.bool) =
  fun uu___ ->
    (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
     uu___1 >= (Prims.of_int (4))) ||
      (FStar_Compiler_Effect.op_Bang _debug_all)
let (set_level_low : unit -> unit) =
  fun uu___ -> FStar_Compiler_Effect.op_Colon_Equals dbg_level Prims.int_one
let (set_level_medium : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals dbg_level (Prims.of_int (2))
let (set_level_high : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals dbg_level (Prims.of_int (3))
let (set_level_extreme : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals dbg_level (Prims.of_int (4))
let (enable_toggles : Prims.string Prims.list -> unit) =
  fun keys ->
    if Prims.uu___is_Cons keys then enable () else ();
    FStar_Compiler_List.iter
      (fun k ->
         if k = "Low"
         then set_level_low ()
         else
           if k = "Medium"
           then set_level_medium ()
           else
             if k = "High"
             then set_level_high ()
             else
               if k = "Extreme"
               then set_level_extreme ()
               else
                 (let t = get_toggle k in
                  FStar_Compiler_Effect.op_Colon_Equals t true)) keys
let (disable_all : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals anyref false;
    FStar_Compiler_Effect.op_Colon_Equals dbg_level Prims.int_zero;
    (let uu___3 = FStar_Compiler_Effect.op_Bang toggle_list in
     FStar_Compiler_List.iter
       (fun uu___4 ->
          match uu___4 with
          | (uu___5, r) -> FStar_Compiler_Effect.op_Colon_Equals r false)
       uu___3)
let (set_debug_all : unit -> unit) =
  fun uu___ -> FStar_Compiler_Effect.op_Colon_Equals _debug_all true