open Prims
type key = Prims.string
type value = Prims.string
type ext_state =
  | E of Prims.string FStarC_PSMap.t 
let uu___is_E (projectee : ext_state) : Prims.bool= true
let __proj__E__item__map (projectee : ext_state) :
  Prims.string FStarC_PSMap.t= match projectee with | E map -> map
let defaults : (Prims.string * Prims.string) Prims.list=
  [("context_pruning", "true"); ("prune_decls", "true")]
let init : ext_state=
  let uu___ =
    let uu___1 = FStarC_PSMap.empty () in
    FStarC_List.fold_right
      (fun uu___2 m -> match uu___2 with | (k, v) -> FStarC_PSMap.add m k v)
      defaults uu___1 in
  E uu___
let cur_state : ext_state FStarC_Effect.ref= FStarC_Effect.alloc init
let set (k : key) (v : value) : unit=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Effect.op_Bang cur_state in
        __proj__E__item__map uu___3 in
      FStarC_PSMap.add uu___2 k v in
    E uu___1 in
  FStarC_Effect.op_Colon_Equals cur_state uu___
let get (k : key) : value=
  let r =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang cur_state in
        __proj__E__item__map uu___2 in
      FStarC_PSMap.try_find uu___1 k in
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some v -> v in
  r
let enabled (k : key) : Prims.bool=
  let v = get k in
  let v1 = FStarC_String.lowercase v in
  (v1 <> "") &&
    (Prims.op_Negation (((v1 = "off") || (v1 = "false")) || (v1 = "0")))
let is_prefix (s1 : Prims.string) (s2 : Prims.string) : Prims.bool=
  let l1 = FStarC_String.length s1 in
  let l2 = FStarC_String.length s2 in
  (l2 >= l1) &&
    (let uu___ = FStarC_String.substring s2 Prims.int_zero l1 in uu___ = s1)
let getns (ns : Prims.string) : (key * value) Prims.list=
  let f k v acc =
    let uu___ = is_prefix (Prims.strcat ns ":") k in
    if uu___ then (k, v) :: acc else acc in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang cur_state in
    __proj__E__item__map uu___1 in
  FStarC_PSMap.fold uu___ f []
let all (uu___ : unit) : (key * value) Prims.list=
  let f k v acc = (k, v) :: acc in
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang cur_state in
    __proj__E__item__map uu___2 in
  FStarC_PSMap.fold uu___1 f []
let save (uu___ : unit) : ext_state= FStarC_Effect.op_Bang cur_state
let restore (s : ext_state) : unit= FStarC_Effect.op_Colon_Equals cur_state s
let reset (uu___ : unit) : unit= FStarC_Effect.op_Colon_Equals cur_state init
