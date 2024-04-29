open Prims
let (toggle_list :
  (Prims.string * Prims.bool FStar_Compiler_Effect.ref) Prims.list
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref []
let (register_toggle : Prims.string -> Prims.bool FStar_Compiler_Effect.ref)
  =
  fun k ->
    let r = FStar_Compiler_Util.mk_ref false in
    (let uu___1 =
       let uu___2 = FStar_Compiler_Effect.op_Bang toggle_list in (k, r) ::
         uu___2 in
     FStar_Compiler_Effect.op_Colon_Equals toggle_list uu___1);
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
let (list_all_toggles : unit -> Prims.string Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang toggle_list in
    FStar_Compiler_List.map FStar_Pervasives_Native.fst uu___1
let (anyref : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref false
let (any : unit -> Prims.bool) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang anyref
let (enable : unit -> unit) =
  fun uu___ -> FStar_Compiler_Effect.op_Colon_Equals anyref true
let (dbg_level : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (low : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
    uu___1 >= Prims.int_one
let (medium : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
    uu___1 >= (Prims.of_int (2))
let (high : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
    uu___1 >= (Prims.of_int (3))
let (extreme : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang dbg_level in
    uu___1 >= (Prims.of_int (4))
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