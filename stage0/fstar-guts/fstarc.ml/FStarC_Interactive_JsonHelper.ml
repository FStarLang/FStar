open Prims
type assoct = (Prims.string * FStarC_Json.json) Prims.list
let try_assoc (key : Prims.string) (d : assoct) :
  FStarC_Json.json FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Util.try_find
      (fun uu___1 -> match uu___1 with | (k, uu___2) -> k = key) d in
  FStarC_Option.map FStar_Pervasives_Native.snd uu___
exception InvalidQuery of Prims.string 
let uu___is_InvalidQuery (projectee : Prims.exn) : Prims.bool=
  match projectee with | InvalidQuery uu___ -> true | uu___ -> false
let __proj__InvalidQuery__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | InvalidQuery uu___ -> uu___
exception UnexpectedJsonType of (Prims.string * FStarC_Json.json) 
let uu___is_UnexpectedJsonType (projectee : Prims.exn) : Prims.bool=
  match projectee with | UnexpectedJsonType uu___ -> true | uu___ -> false
let __proj__UnexpectedJsonType__item__uu___ (projectee : Prims.exn) :
  (Prims.string * FStarC_Json.json)=
  match projectee with | UnexpectedJsonType uu___ -> uu___
let write_json (js : FStarC_Json.json) : unit=
  (let uu___1 = FStarC_Json.string_of_json js in
   FStarC_Format.print_raw uu___1);
  FStarC_Format.print_raw "\n"
let js_fail (expected : Prims.string) (got : FStarC_Json.json) : 'a=
  FStarC_Effect.raise (UnexpectedJsonType (expected, got))
let js_int (uu___ : FStarC_Json.json) : Prims.int=
  match uu___ with
  | FStarC_Json.JsonInt i -> i
  | other -> js_fail "int" other
let js_bool (uu___ : FStarC_Json.json) : Prims.bool=
  match uu___ with
  | FStarC_Json.JsonBool b -> b
  | other -> js_fail "int" other
let js_str (uu___ : FStarC_Json.json) : Prims.string=
  match uu___ with
  | FStarC_Json.JsonStr s -> s
  | other -> js_fail "string" other
let js_list (k : FStarC_Json.json -> 'a) (uu___ : FStarC_Json.json) :
  'a Prims.list=
  match uu___ with
  | FStarC_Json.JsonList l -> FStarC_List.map k l
  | other -> js_fail "list" other
let js_assoc (uu___ : FStarC_Json.json) : assoct=
  match uu___ with
  | FStarC_Json.JsonAssoc a -> a
  | other -> js_fail "dictionary" other
let json_debug (uu___ : FStarC_Json.json) : Prims.string=
  match uu___ with
  | FStarC_Json.JsonNull -> "null"
  | FStarC_Json.JsonBool b ->
      FStarC_Format.fmt1 "bool (%s)" (if b then "true" else "false")
  | FStarC_Json.JsonInt i ->
      let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      FStarC_Format.fmt1 "int (%s)" uu___1
  | FStarC_Json.JsonStr s -> FStarC_Format.fmt1 "string (%s)" s
  | FStarC_Json.JsonList uu___1 -> "list (...)"
  | FStarC_Json.JsonAssoc uu___1 -> "dictionary (...)"
