open Prims
type key = Prims.string
type value = Prims.string
type ext_state =
  | E of Prims.string FStarC_Compiler_Util.psmap 
let (uu___is_E : ext_state -> Prims.bool) = fun projectee -> true
let (__proj__E__item__map :
  ext_state -> Prims.string FStarC_Compiler_Util.psmap) =
  fun projectee -> match projectee with | E map -> map
let (cur_state : ext_state FStarC_Compiler_Effect.ref) =
  let uu___ = let uu___1 = FStarC_Compiler_Util.psmap_empty () in E uu___1 in
  FStarC_Compiler_Util.mk_ref uu___
let (set : key -> value -> unit) =
  fun k ->
    fun v ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Compiler_Effect.op_Bang cur_state in
            __proj__E__item__map uu___3 in
          FStarC_Compiler_Util.psmap_add uu___2 k v in
        E uu___1 in
      FStarC_Compiler_Effect.op_Colon_Equals cur_state uu___
let (get : key -> value) =
  fun k ->
    let r =
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Compiler_Effect.op_Bang cur_state in
          __proj__E__item__map uu___2 in
        FStarC_Compiler_Util.psmap_try_find uu___1 k in
      match uu___ with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some v -> v in
    r
let (is_prefix : Prims.string -> Prims.string -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      let l1 = FStarC_Compiler_String.length s1 in
      let l2 = FStarC_Compiler_String.length s2 in
      (l2 >= l1) &&
        (let uu___ = FStarC_Compiler_String.substring s2 Prims.int_zero l1 in
         uu___ = s1)
let (getns : Prims.string -> (key * value) Prims.list) =
  fun ns ->
    let f k v acc =
      let uu___ = is_prefix (Prims.strcat ns ":") k in
      if uu___ then (k, v) :: acc else acc in
    let uu___ =
      let uu___1 = FStarC_Compiler_Effect.op_Bang cur_state in
      __proj__E__item__map uu___1 in
    FStarC_Compiler_Util.psmap_fold uu___ f []
let (all : unit -> (key * value) Prims.list) =
  fun uu___ ->
    let f k v acc = (k, v) :: acc in
    let uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang cur_state in
      __proj__E__item__map uu___2 in
    FStarC_Compiler_Util.psmap_fold uu___1 f []
let (save : unit -> ext_state) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang cur_state
let (restore : ext_state -> unit) =
  fun s -> FStarC_Compiler_Effect.op_Colon_Equals cur_state s
let (reset : unit -> unit) =
  fun uu___ ->
    let uu___1 = let uu___2 = FStarC_Compiler_Util.psmap_empty () in E uu___2 in
    FStarC_Compiler_Effect.op_Colon_Equals cur_state uu___1