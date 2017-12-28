
open Prims
open FStar_Pervasives
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of Prims.int
  | Array of (sort,sort) FStar_Pervasives_Native.tuple2
  | Arrow of (sort,sort) FStar_Pervasives_Native.tuple2
  | Sort of Prims.string[@@deriving show]
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____28 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____32 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____36 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____40 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____44 -> false
let uu___is_BitVec_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____49 -> false
let __proj__BitVec_sort__item___0: sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____65 -> false
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____93 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____117 -> false
let __proj__Sort__item___0: sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0
let rec strSort: sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Fuel_sort  -> "Fuel"
    | BitVec_sort n1 ->
        let uu____129 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ BitVec %s)" uu____129
    | Array (s1,s2) ->
        let uu____132 = strSort s1 in
        let uu____133 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____132 uu____133
    | Arrow (s1,s2) ->
        let uu____136 = strSort s1 in
        let uu____137 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____136 uu____137
    | Sort s -> s
type op =
  | TrueOp
  | FalseOp
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | BvAnd
  | BvXor
  | BvOr
  | BvAdd
  | BvSub
  | BvShl
  | BvShr
  | BvUdiv
  | BvMod
  | BvMul
  | BvUlt
  | BvUext of Prims.int
  | NatToBv of Prims.int
  | BvToNat
  | ITE
  | Var of Prims.string[@@deriving show]
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____154 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____158 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____162 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____166 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____170 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____174 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____178 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____182 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____186 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____190 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____194 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____198 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____202 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____206 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____210 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____214 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____218 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____222 -> false
let uu___is_BvAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____226 -> false
let uu___is_BvXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____230 -> false
let uu___is_BvOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____234 -> false
let uu___is_BvAdd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____238 -> false
let uu___is_BvSub: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____242 -> false
let uu___is_BvShl: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____246 -> false
let uu___is_BvShr: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____250 -> false
let uu___is_BvUdiv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____254 -> false
let uu___is_BvMod: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____258 -> false
let uu___is_BvMul: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____262 -> false
let uu___is_BvUlt: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____266 -> false
let uu___is_BvUext: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____271 -> false
let __proj__BvUext__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0
let uu___is_NatToBv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____283 -> false
let __proj__NatToBv__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
let uu___is_BvToNat: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____294 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____298 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____303 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists[@@deriving show]
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____314 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____318 -> false
type term' =
  | Integer of Prims.string
  | BoundV of Prims.int
  | FreeV of (Prims.string,sort) FStar_Pervasives_Native.tuple2
  | App of (op,term Prims.list) FStar_Pervasives_Native.tuple2
  | Quant of
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
  sort Prims.list,term) FStar_Pervasives_Native.tuple5
  | Let of (term Prims.list,term) FStar_Pervasives_Native.tuple2
  | Labeled of (term,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | LblPos of (term,Prims.string) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
and term =
  {
  tm: term';
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}[@@deriving show]
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____440 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____452 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____468 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____498 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____546 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____618 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____654 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____688 -> false
let __proj__LblPos__item___0:
  term' -> (term,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LblPos _0 -> _0
let __proj__Mkterm__item__tm: term -> term' =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__tm
let __proj__Mkterm__item__freevars:
  term ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo
  =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__freevars
let __proj__Mkterm__item__rng: term -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__rng
type pat = term[@@deriving show]
type fv = (Prims.string,sort) FStar_Pervasives_Native.tuple2[@@deriving show]
type fvs = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type caption = Prims.string FStar_Pervasives_Native.option[@@deriving show]
type binders = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type constructor_field =
(Prims.string * sort * Prims.bool)


type constructor_t =
(Prims.string * constructor_field Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list

type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string[@@deriving show]
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____853 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____865 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____877 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
{assumption_term : term; assumption_caption : caption; assumption_name : Prims.string; assumption_fact_ids : fact_db_id Prims.list}


let __proj__Mkassumption__item__assumption_term : assumption  ->  term = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_term
end))


let __proj__Mkassumption__item__assumption_caption : assumption  ->  caption = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_caption
end))


let __proj__Mkassumption__item__assumption_name : assumption  ->  Prims.string = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_name
end))


let __proj__Mkassumption__item__assumption_fact_ids : assumption  ->  fact_db_id Prims.list = (fun projectee -> (match (projectee) with
| {assumption_term = __fname__assumption_term; assumption_caption = __fname__assumption_caption; assumption_name = __fname__assumption_name; assumption_fact_ids = __fname__assumption_fact_ids} -> begin
__fname__assumption_fact_ids
end))

type decl =
  | DefPrelude
  | DeclFun of (Prims.string,sort Prims.list,sort,caption)
  FStar_Pervasives_Native.tuple4
  | DefineFun of (Prims.string,sort Prims.list,sort,term,caption)
  FStar_Pervasives_Native.tuple5
  | Assume of assumption
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | RetainAssumptions of Prims.string Prims.list
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  | GetStatistics
  | GetReasonUnknown[@@deriving show]
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1006 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1021 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1075 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1123 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1135 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1147 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1159 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1173 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1190 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1194 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1198 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1202 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1211 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1234 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1238 -> false
type decls_t = decl Prims.list[@@deriving show]
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type error_labels = error_label Prims.list[@@deriving show]
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort:
  'Auu____1258 'Auu____1259 .
    ('Auu____1259,'Auu____1258) FStar_Pervasives_Native.tuple2 ->
      'Auu____1258
  = fun x  -> FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1288 -> false
let freevar_sort: term -> sort =
  fun uu___42_1295  ->
    match uu___42_1295 with
    | { tm = FreeV x; freevars = uu____1297; rng = uu____1298;_} -> fv_sort x
    | uu____1311 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___43_1314  ->
    match uu___43_1314 with
    | { tm = FreeV fv; freevars = uu____1316; rng = uu____1317;_} -> fv
    | uu____1330 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1346 -> []
    | BoundV uu____1351 -> []
    | FreeV fv -> [fv]
    | App (uu____1369,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1379,uu____1380,uu____1381,uu____1382,t1) -> freevars t1
    | Labeled (t1,uu____1401,uu____1402) -> freevars t1
    | LblPos (t1,uu____1404) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1418 = FStar_ST.op_Bang t.freevars in
    match uu____1418 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1513 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1513 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___44_1585  ->
    match uu___44_1585 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___45_1588  ->
    match uu___45_1588 with
    | TrueOp  -> "true"
    | FalseOp  -> "false"
    | Not  -> "not"
    | And  -> "and"
    | Or  -> "or"
    | Imp  -> "implies"
    | Iff  -> "iff"
    | Eq  -> "="
    | LT  -> "<"
    | LTE  -> "<="
    | GT  -> ">"
    | GTE  -> ">="
    | Add  -> "+"
    | Sub  -> "-"
    | Div  -> "div"
    | Mul  -> "*"
    | Minus  -> "-"
    | Mod  -> "mod"
    | ITE  -> "ite"
    | BvAnd  -> "bvand"
    | BvXor  -> "bvxor"
    | BvOr  -> "bvor"
    | BvAdd  -> "bvadd"
    | BvSub  -> "bvsub"
    | BvShl  -> "bvshl"
    | BvShr  -> "bvlshr"
    | BvUdiv  -> "bvudiv"
    | BvMod  -> "bvurem"
    | BvMul  -> "bvmul"
    | BvUlt  -> "bvult"
    | BvToNat  -> "bv2int"
    | BvUext n1 ->
        let uu____1590 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1590
    | NatToBv n1 ->
        let uu____1592 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1592
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___46_1598  ->
    match uu___46_1598 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1602 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1602
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1610 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1610
    | FreeV x ->
        let uu____1616 =
          let uu____1617 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1617 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1616
    | App (op,tms) ->
        let uu____1624 =
          let uu____1625 = op_to_string op in
          let uu____1626 =
            let uu____1627 =
              let uu____1628 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1628 (FStar_String.concat " ") in
            Prims.strcat uu____1627 ")" in
          Prims.strcat uu____1625 uu____1626 in
        Prims.strcat "(" uu____1624
    | Labeled (t1,r1,r2) ->
        let uu____1636 = hash_of_term t1 in
        let uu____1637 =
          let uu____1638 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1638 in
        Prims.strcat uu____1636 uu____1637
    | LblPos (t1,r) ->
        let uu____1641 =
          let uu____1642 = hash_of_term t1 in
          Prims.strcat uu____1642
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1641
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1664 =
          let uu____1665 =
            let uu____1666 =
              let uu____1667 =
                let uu____1668 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1668 (FStar_String.concat " ") in
              let uu____1673 =
                let uu____1674 =
                  let uu____1675 = hash_of_term body in
                  let uu____1676 =
                    let uu____1677 =
                      let uu____1678 = weightToSmt wopt in
                      let uu____1679 =
                        let uu____1680 =
                          let uu____1681 =
                            let uu____1682 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1698 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1698
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1682
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1681 "))" in
                        Prims.strcat " " uu____1680 in
                      Prims.strcat uu____1678 uu____1679 in
                    Prims.strcat " " uu____1677 in
                  Prims.strcat uu____1675 uu____1676 in
                Prims.strcat ")(! " uu____1674 in
              Prims.strcat uu____1667 uu____1673 in
            Prims.strcat " (" uu____1666 in
          Prims.strcat (qop_to_string qop) uu____1665 in
        Prims.strcat "(" uu____1664
    | Let (es,body) ->
        let uu____1711 =
          let uu____1712 =
            let uu____1713 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1713 (FStar_String.concat " ") in
          let uu____1718 =
            let uu____1719 =
              let uu____1720 = hash_of_term body in
              Prims.strcat uu____1720 ")" in
            Prims.strcat ") " uu____1719 in
          Prims.strcat uu____1712 uu____1718 in
        Prims.strcat "(let (" uu____1711
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mkBoxFunctions:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  = fun s  -> (s, (Prims.strcat s "_proj_0"))
let boxIntFun: (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  mkBoxFunctions "BoxInt"
let boxBoolFun: (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  mkBoxFunctions "BoxBool"
let boxStringFun: (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  = mkBoxFunctions "BoxString"
let boxBitVecFun:
  Prims.int -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun sz  ->
    let uu____1748 =
      let uu____1749 = FStar_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu____1749 in
    mkBoxFunctions uu____1748
let isInjective: Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1755 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3") in
       uu____1755 = "Box") &&
        (let uu____1757 =
           let uu____1758 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c  -> c = 46) uu____1758 in
         Prims.op_Negation uu____1757)
    else false
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1775 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1775; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1836 =
        let uu____1837 = FStar_Util.ensure_decimal i in Integer uu____1837 in
      mk uu____1836 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1844 = FStar_Util.string_of_int i in mkInteger uu____1844 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun x  -> fun r  -> mk (FreeV x) r
let mkApp':
  (op,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun f  -> fun r  -> mk (App f) r
let mkApp:
  (Prims.string,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1893  ->
    fun r  -> match uu____1893 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1915) -> mkFalse r
      | App (FalseOp ,uu____1920) -> mkTrue r
      | uu____1925 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1936  ->
    fun r  ->
      match uu____1936 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1944),uu____1945) -> t2
           | (uu____1950,App (TrueOp ,uu____1951)) -> t1
           | (App (FalseOp ,uu____1956),uu____1957) -> mkFalse r
           | (uu____1962,App (FalseOp ,uu____1963)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1980,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1989) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1996 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2011  ->
    fun r  ->
      match uu____2011 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2019),uu____2020) -> mkTrue r
           | (uu____2025,App (TrueOp ,uu____2026)) -> mkTrue r
           | (App (FalseOp ,uu____2031),uu____2032) -> t2
           | (uu____2037,App (FalseOp ,uu____2038)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2055,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2064) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2071 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2086  ->
    fun r  ->
      match uu____2086 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2094,App (TrueOp ,uu____2095)) -> mkTrue r
           | (App (FalseOp ,uu____2100),uu____2101) -> mkTrue r
           | (App (TrueOp ,uu____2106),uu____2107) -> t2
           | (uu____2112,App (Imp ,t1'::t2'::[])) ->
               let uu____2117 =
                 let uu____2124 =
                   let uu____2127 = mkAnd (t1, t1') r in [uu____2127; t2'] in
                 (Imp, uu____2124) in
               mkApp' uu____2117 r
           | uu____2130 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2148  ->
      fun r  -> match uu____2148 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkNatToBv: Prims.int -> term -> FStar_Range.range -> term =
  fun sz  -> fun t  -> fun r  -> mkApp' ((NatToBv sz), [t]) r
let mkBvUext: Prims.int -> term -> FStar_Range.range -> term =
  fun sz  -> fun t  -> fun r  -> mkApp' ((BvUext sz), [t]) r
let mkBvToNat: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (BvToNat, [t]) r
let mkBvAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvAnd
let mkBvXor:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvXor
let mkBvOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvOr
let mkBvAdd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvAdd
let mkBvSub:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvSub
let mkBvShl:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2247  ->
      fun r  ->
        match uu____2247 with
        | (t1,t2) ->
            let uu____2255 =
              let uu____2262 =
                let uu____2265 =
                  let uu____2268 = mkNatToBv sz t2 r in [uu____2268] in
                t1 :: uu____2265 in
              (BvShl, uu____2262) in
            mkApp' uu____2255 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2282  ->
      fun r  ->
        match uu____2282 with
        | (t1,t2) ->
            let uu____2290 =
              let uu____2297 =
                let uu____2300 =
                  let uu____2303 = mkNatToBv sz t2 r in [uu____2303] in
                t1 :: uu____2300 in
              (BvShr, uu____2297) in
            mkApp' uu____2290 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2317  ->
      fun r  ->
        match uu____2317 with
        | (t1,t2) ->
            let uu____2325 =
              let uu____2332 =
                let uu____2335 =
                  let uu____2338 = mkNatToBv sz t2 r in [uu____2338] in
                t1 :: uu____2335 in
              (BvUdiv, uu____2332) in
            mkApp' uu____2325 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2352  ->
      fun r  ->
        match uu____2352 with
        | (t1,t2) ->
            let uu____2360 =
              let uu____2367 =
                let uu____2370 =
                  let uu____2373 = mkNatToBv sz t2 r in [uu____2373] in
                t1 :: uu____2370 in
              (BvMod, uu____2367) in
            mkApp' uu____2360 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2387  ->
      fun r  ->
        match uu____2387 with
        | (t1,t2) ->
            let uu____2395 =
              let uu____2402 =
                let uu____2405 =
                  let uu____2408 = mkNatToBv sz t2 r in [uu____2408] in
                t1 :: uu____2405 in
              (BvMul, uu____2402) in
            mkApp' uu____2395 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2435  ->
    fun r  ->
      match uu____2435 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2451 -> mk_bin_op Eq (t1, t2) r)
let mkLT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LT
let mkLTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LTE
let mkGT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GT
let mkGTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GTE
let mkAdd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Add
let mkSub:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Sub
let mkDiv:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Div
let mkMul:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mul
let mkMod:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mod
let mkITE:
  (term,term,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2538  ->
    fun r  ->
      match uu____2538 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2549) -> t2
           | App (FalseOp ,uu____2554) -> t3
           | uu____2559 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2560),App (TrueOp ,uu____2561)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2570),uu____2571) ->
                    let uu____2576 =
                      let uu____2581 = mkNot t1 t1.rng in (uu____2581, t3) in
                    mkImp uu____2576 r
                | (uu____2582,App (TrueOp ,uu____2583)) -> mkImp (t1, t2) r
                | (uu____2588,uu____2589) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2632  ->
    fun r  ->
      match uu____2632 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2674) -> body
             | uu____2679 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2698  ->
    fun r  ->
      match uu____2698 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2732 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2732 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2751 = FStar_ST.op_Bang t1.freevars in
        match uu____2751 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2834 ->
            (match t1.tm with
             | Integer uu____2843 -> t1
             | BoundV uu____2844 -> t1
             | FreeV x ->
                 let uu____2850 = index_of x in
                 (match uu____2850 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2860 =
                   let uu____2867 = FStar_List.map (aux ix) tms in
                   (op, uu____2867) in
                 mkApp' uu____2860 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2875 =
                   let uu____2876 =
                     let uu____2883 = aux ix t2 in (uu____2883, r1, r2) in
                   Labeled uu____2876 in
                 mk uu____2875 t2.rng
             | LblPos (t2,r) ->
                 let uu____2886 =
                   let uu____2887 =
                     let uu____2892 = aux ix t2 in (uu____2892, r) in
                   LblPos uu____2887 in
                 mk uu____2886 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2915 =
                   let uu____2934 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2955 = aux (ix + n1) body in
                   (qop, uu____2934, wopt, vars, uu____2955) in
                 mkQuant uu____2915 t1.rng
             | Let (es,body) ->
                 let uu____2974 =
                   FStar_List.fold_left
                     (fun uu____2992  ->
                        fun e  ->
                          match uu____2992 with
                          | (ix1,l) ->
                              let uu____3012 =
                                let uu____3015 = aux ix1 e in uu____3015 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____3012))
                     (ix, []) es in
                 (match uu____2974 with
                  | (ix1,es_rev) ->
                      let uu____3026 =
                        let uu____3033 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____3033) in
                      mkLet uu____3026 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3057 -> t1
        | FreeV uu____3058 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3075 =
              let uu____3082 = FStar_List.map (aux shift) tms2 in
              (op, uu____3082) in
            mkApp' uu____3075 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3090 =
              let uu____3091 =
                let uu____3098 = aux shift t2 in (uu____3098, r1, r2) in
              Labeled uu____3091 in
            mk uu____3090 t2.rng
        | LblPos (t2,r) ->
            let uu____3101 =
              let uu____3102 =
                let uu____3107 = aux shift t2 in (uu____3107, r) in
              LblPos uu____3102 in
            mk uu____3101 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____3135 =
              let uu____3154 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____3171 = aux shift1 body in
              (qop, uu____3154, wopt, vars, uu____3171) in
            mkQuant uu____3135 t1.rng
        | Let (es,body) ->
            let uu____3186 =
              FStar_List.fold_left
                (fun uu____3204  ->
                   fun e  ->
                     match uu____3204 with
                     | (ix,es1) ->
                         let uu____3224 =
                           let uu____3227 = aux shift e in uu____3227 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____3224))
                (shift, []) es in
            (match uu____3186 with
             | (shift1,es_rev) ->
                 let uu____3238 =
                   let uu____3245 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____3245) in
                 mkLet uu____3238 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____3257 = abstr [fv] t in inst [s] uu____3257
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3280  ->
    match uu____3280 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3322 =
          let uu____3341 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____3358 = FStar_List.map fv_sort vars in
          let uu____3365 = abstr vars body in
          (qop, uu____3341, wopt, uu____3358, uu____3365) in
        mkQuant uu____3322
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3394  ->
    fun r  ->
      match uu____3394 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3458  ->
    fun r  ->
      match uu____3458 with
      | (pats,wopt,vars,body) ->
          let uu____3490 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____3490 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3513  ->
    fun r  ->
      match uu____3513 with
      | (pats,vars,body) ->
          let uu____3536 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3536 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3559  ->
    fun r  ->
      match uu____3559 with
      | (pats,vars,body) ->
          let uu____3582 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3582 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3605  ->
    fun r  ->
      match uu____3605 with
      | (bindings,body) ->
          let uu____3631 = FStar_List.split bindings in
          (match uu____3631 with
           | (vars,es) ->
               let uu____3650 =
                 let uu____3657 = abstr vars body in (es, uu____3657) in
               mkLet uu____3650 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3678  ->
    match uu____3678 with
    | (nm,vars,s,tm,c) ->
        let uu____3712 =
          let uu____3725 = FStar_List.map fv_sort vars in
          let uu____3732 = abstr vars tm in
          (nm, uu____3725, s, uu____3732, c) in
        DefineFun uu____3712
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3738 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3738
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3747  ->
    fun id1  ->
      match uu____3747 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3757 =
              let uu____3758 =
                let uu____3763 = mkInteger' id1 norng in
                let uu____3764 =
                  let uu____3765 =
                    let uu____3772 = constr_id_of_sort sort in
                    let uu____3773 =
                      let uu____3776 = mkApp (tok_name, []) norng in
                      [uu____3776] in
                    (uu____3772, uu____3773) in
                  mkApp uu____3765 norng in
                (uu____3763, uu____3764) in
              mkEq uu____3758 norng in
            {
              assumption_term = uu____3757;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string,sort Prims.list,sort,Prims.int)
    FStar_Pervasives_Native.tuple4 -> decl
  =
  fun uu____3793  ->
    match uu____3793 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1 in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3825 =
                      let uu____3830 =
                        let uu____3831 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____3831 in
                      (uu____3830, s) in
                    mkFreeV uu____3825 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____3839 =
            let uu____3846 = constr_id_of_sort sort in (uu____3846, [capp]) in
          mkApp uu____3839 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____3851 =
            let uu____3852 =
              let uu____3863 =
                let uu____3864 =
                  let uu____3869 = mkInteger id2 norng in
                  (uu____3869, cid_app) in
                mkEq uu____3864 norng in
              ([[capp]], bvar_names, uu____3863) in
            mkForall uu____3852 norng in
          {
            assumption_term = uu____3851;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decls_t
  =
  fun uu____3890  ->
    match uu____3890 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____3911 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____3911 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____3931 = let uu____3936 = bvar_name i in (uu____3936, s) in
          mkFreeV uu____3931 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3957  ->
                    match uu____3957 with
                    | (uu____3964,s,uu____3966) ->
                        let uu____3967 = bvar i s in uu____3967 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____3976 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4004  ->
                    match uu____4004 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____4027 =
                              let uu____4028 =
                                let uu____4039 =
                                  let uu____4040 =
                                    let uu____4045 =
                                      let uu____4046 = bvar i s in
                                      uu____4046 norng in
                                    (cproj_app, uu____4045) in
                                  mkEq uu____4040 norng in
                                ([[capp]], bvar_names, uu____4039) in
                              mkForall uu____4028 norng in
                            {
                              assumption_term = uu____4027;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____3976 FStar_List.flatten
let constructor_to_decl: constructor_t -> decls_t =
  fun uu____4068  ->
    match uu____4068 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4096  ->
                  match uu____4096 with
                  | (uu____4103,sort1,uu____4105) -> sort1)) in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id1) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____4123 =
              let uu____4128 =
                let uu____4129 =
                  let uu____4136 = constr_id_of_sort sort in
                  (uu____4136, [xx]) in
                mkApp uu____4129 norng in
              let uu____4139 =
                let uu____4140 = FStar_Util.string_of_int id1 in
                mkInteger uu____4140 norng in
              (uu____4128, uu____4139) in
            mkEq uu____4123 norng in
          let uu____4141 =
            let uu____4156 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4206  ->
                        match uu____4206 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4236 = mkApp (proj, [xx]) norng in
                              (uu____4236, [])
                            else
                              (let fi =
                                 let uu____4255 =
                                   let uu____4256 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____4256 in
                                 (uu____4255, s) in
                               let uu____4257 = mkFreeV fi norng in
                               (uu____4257, [fi])))) in
            FStar_All.pipe_right uu____4156 FStar_List.split in
          match uu____4141 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____4338 =
                  let uu____4343 = mkApp (name, proj_terms) norng in
                  (xx, uu____4343) in
                mkEq uu____4338 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4351 -> mkExists ([], ex_vars1, disc_inv_body) norng in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (FStar_Pervasives_Native.Some "Discriminator definition")) in
              def in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else [] in
        let uu____4392 =
          let uu____4395 =
            let uu____4396 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____4396 in
          uu____4395 :: cdecl :: cid :: projs in
        let uu____4397 =
          let uu____4400 =
            let uu____4403 =
              let uu____4404 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____4404 in
            [uu____4403] in
          FStar_List.append [disc] uu____4400 in
        FStar_List.append uu____4392 uu____4397
let name_binders_inner:
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
            Prims.string Prims.list,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____4451 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4506  ->
                    fun s  ->
                      match uu____4506 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4556 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____4560 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____4560 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____4573 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____4573 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____4451 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4650 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____4650 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
let termToSmt: Prims.bool -> Prims.string -> term -> Prims.string =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
          fun depth  ->
            let n1 = FStar_ST.op_Bang ctr in
            FStar_Util.incr ctr;
            if n1 = (Prims.parse_int "0")
            then enclosing_name
            else
              (let uu____4834 = FStar_Util.string_of_int n1 in
               FStar_Util.format2 "%s.%s" enclosing_name uu____4834) in
        let remove_guard_free pats =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun ps  ->
                  FStar_All.pipe_right ps
                    (FStar_List.map
                       (fun tm  ->
                          match tm.tm with
                          | App
                              (Var
                               "Prims.guard_free",{ tm = BoundV uu____4876;
                                                    freevars = uu____4877;
                                                    rng = uu____4878;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____4892 -> tm)))) in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1")) in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____4932 = FStar_List.nth names1 i in
              FStar_All.pipe_right uu____4932 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____4947 = op_to_string op in
              let uu____4948 =
                let uu____4949 = FStar_List.map (aux1 n1 names1) tms in
                FStar_All.pipe_right uu____4949 (FStar_String.concat "\n") in
              FStar_Util.format2 "(%s %s)" uu____4947 uu____4948
          | Labeled (t2,uu____4955,uu____4956) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____4959 = aux1 n1 names1 t2 in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____4959 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid () in
              let uu____4982 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts in
              (match uu____4982 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ") in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5031 ->
                         let uu____5036 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5052 =
                                     let uu____5053 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5059 = aux1 n2 names2 p in
                                            FStar_Util.format1 "%s"
                                              uu____5059) pats2 in
                                     FStar_String.concat " " uu____5053 in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5052)) in
                         FStar_All.pipe_right uu____5036
                           (FStar_String.concat "\n") in
                   let uu____5062 =
                     let uu____5065 =
                       let uu____5068 =
                         let uu____5071 = aux1 n2 names2 body in
                         let uu____5072 =
                           let uu____5075 = weightToSmt wopt in
                           [uu____5075; pats_str; qid] in
                         uu____5071 :: uu____5072 in
                       binders1 :: uu____5068 in
                     (qop_to_string qop) :: uu____5065 in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5062)
          | Let (es,body) ->
              let uu____5082 =
                FStar_List.fold_left
                  (fun uu____5119  ->
                     fun e  ->
                       match uu____5119 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5169 = FStar_Util.string_of_int n0 in
                             Prims.strcat "@lb" uu____5169 in
                           let names01 = (nm, Term_sort) :: names0 in
                           let b =
                             let uu____5182 = aux1 n1 names1 e in
                             FStar_Util.format2 "(%s %s)" nm uu____5182 in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es in
              (match uu____5082 with
               | (names2,binders,n2) ->
                   let uu____5214 = aux1 n2 names2 body in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5214)
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5222 = FStar_Range.string_of_range t1.rng in
            let uu____5223 = FStar_Range.string_of_use_range t1.rng in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5222
              uu____5223 s
          else s in
        aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___47_5229  ->
    match uu___47_5229 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5233 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5248 -> (hd1, "...") in
        (match uu____5233 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt': Prims.bool -> Prims.string -> decl -> Prims.string =
  fun print_ranges  ->
    fun z3options  ->
      fun decl  ->
        let escape s = FStar_Util.replace_char s 39 95 in
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Caption c ->
            let uu____5279 = FStar_Options.log_queries () in
            if uu____5279
            then
              let uu____5280 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___48_5284  ->
                     match uu___48_5284 with | [] -> "" | h::t -> h) in
              FStar_Util.format1 "\n; %s" uu____5280
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts in
            let uu____5303 = caption_to_string c in
            let uu____5304 = strSort retsort in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5303 f
              (FStar_String.concat " " l) uu____5304
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5314 = name_macro_binders arg_sorts in
            (match uu____5314 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5346 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                   inst uu____5346 body in
                 let uu____5359 = caption_to_string c in
                 let uu____5360 = strSort retsort in
                 let uu____5361 = termToSmt print_ranges (escape f) body1 in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5359 f (FStar_String.concat " " binders) uu____5360
                   uu____5361)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___49_5379  ->
                      match uu___49_5379 with
                      | Name n1 ->
                          Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                      | Namespace ns ->
                          Prims.strcat "Namespace "
                            (FStar_Ident.text_of_lid ns)
                      | Tag t -> Prims.strcat "Tag " t)) in
            let fids =
              let uu____5384 = FStar_Options.log_queries () in
              if uu____5384
              then
                let uu____5385 =
                  let uu____5386 = fact_ids_to_string a.assumption_fact_ids in
                  FStar_String.concat "; " uu____5386 in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5385
              else "" in
            let n1 = escape a.assumption_name in
            let uu____5391 = caption_to_string a.assumption_caption in
            let uu____5392 = termToSmt print_ranges n1 a.assumption_term in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5391
              fids uu____5392 n1
        | Eval t ->
            let uu____5394 = termToSmt print_ranges "eval" t in
            FStar_Util.format1 "(eval %s)" uu____5394
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5396 -> ""
        | CheckSat  ->
            "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
        | GetUnsatCore  ->
            "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
        | Push  -> "(push)"
        | Pop  -> "(pop)"
        | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
        | GetStatistics  ->
            "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
        | GetReasonUnknown  ->
            "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  -> fun decl  -> declToSmt' true z3options decl
and declToSmt_no_caps: Prims.string -> decl -> Prims.string =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_unit", [], Term_sort, (Prims.parse_int "6"), true);
      ((FStar_Pervasives_Native.fst boxIntFun),
        [((FStar_Pervasives_Native.snd boxIntFun), Int_sort, true)],
        Term_sort, (Prims.parse_int "7"), true);
      ((FStar_Pervasives_Native.fst boxBoolFun),
        [((FStar_Pervasives_Native.snd boxBoolFun), Bool_sort, true)],
        Term_sort, (Prims.parse_int "8"), true);
      ((FStar_Pervasives_Native.fst boxStringFun),
        [((FStar_Pervasives_Native.snd boxStringFun), String_sort, true)],
        Term_sort, (Prims.parse_int "9"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let uu____5725 =
        let uu____5728 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____5728
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____5725 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____5743 =
      let uu____5762 =
        let uu____5763 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5763 in
      let uu____5768 =
        let uu____5777 =
          let uu____5784 =
            let uu____5785 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____5785 in
          (uu____5784, (BitVec_sort sz), true) in
        [uu____5777] in
      (uu____5762, uu____5768, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____5743 constructor_to_decl
let __range_c: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let mk_Range_const: Prims.unit -> term =
  fun uu____5843  ->
    let i = FStar_ST.op_Bang __range_c in
    (let uu____5894 =
       let uu____5895 = FStar_ST.op_Bang __range_c in
       uu____5895 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals __range_c uu____5894);
    (let uu____5992 =
       let uu____5999 = let uu____6002 = mkInteger' i norng in [uu____6002] in
       ("Range_const", uu____5999) in
     mkApp uu____5992 norng)
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____6024 =
        let uu____6031 = let uu____6034 = mkInteger' i norng in [uu____6034] in
        ("Tm_uvar", uu____6031) in
      mkApp uu____6024 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6055 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6067 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____6067 u v1 t
let boxInt: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun)
      (FStar_Pervasives_Native.snd boxIntFun) t
let unboxInt: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun)
      (FStar_Pervasives_Native.fst boxIntFun) t
let boxBool: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun)
      (FStar_Pervasives_Native.snd boxBoolFun) t
let unboxBool: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun)
      (FStar_Pervasives_Native.fst boxBoolFun) t
let boxString: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun)
      (FStar_Pervasives_Native.snd boxStringFun) t
let unboxString: term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun)
      (FStar_Pervasives_Native.fst boxStringFun) t
let boxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6092 =
        let uu____6093 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6093 in
      let uu____6098 =
        let uu____6099 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6099 in
      elim_box true uu____6092 uu____6098 t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6110 =
        let uu____6111 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6111 in
      let uu____6116 =
        let uu____6117 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6117 in
      elim_box true uu____6110 uu____6116 t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6129 -> FStar_Exn.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6137 -> FStar_Exn.raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6153 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____6153
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6165 = op_to_string op in
        let uu____6166 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____6165 uu____6166
    | Labeled (t1,r1,r2) ->
        let uu____6170 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6170
    | LblPos (t1,s) ->
        let uu____6173 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6173
    | Quant (qop,l,uu____6176,uu____6177,t1) ->
        let uu____6195 = print_smt_term_list_list l in
        let uu____6196 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6195
          uu____6196
    | Let (es,body) ->
        let uu____6203 = print_smt_term_list es in
        let uu____6204 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____6203 uu____6204
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____6208 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____6208 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6227 =
             let uu____6228 =
               let uu____6229 = print_smt_term_list l1 in
               Prims.strcat uu____6229 " ] " in
             Prims.strcat "; [ " uu____6228 in
           Prims.strcat s uu____6227) "" l
let getBoxedInteger: term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6244 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____6244
         | uu____6245 -> FStar_Pervasives_Native.None)
    | uu____6246 -> FStar_Pervasives_Native.None
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6255::t1::t2::[]);
                       freevars = uu____6258; rng = uu____6259;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6272::t1::t2::[]);
                       freevars = uu____6275; rng = uu____6276;_}::[])
        -> let uu____6289 = mkEq (t1, t2) norng in mkNot uu____6289 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6292; rng = uu____6293;_}::[])
        ->
        let uu____6306 =
          let uu____6311 = unboxInt t1 in
          let uu____6312 = unboxInt t2 in (uu____6311, uu____6312) in
        mkLTE uu____6306 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6315; rng = uu____6316;_}::[])
        ->
        let uu____6329 =
          let uu____6334 = unboxInt t1 in
          let uu____6335 = unboxInt t2 in (uu____6334, uu____6335) in
        mkLT uu____6329 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6338; rng = uu____6339;_}::[])
        ->
        let uu____6352 =
          let uu____6357 = unboxInt t1 in
          let uu____6358 = unboxInt t2 in (uu____6357, uu____6358) in
        mkGTE uu____6352 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6361; rng = uu____6362;_}::[])
        ->
        let uu____6375 =
          let uu____6380 = unboxInt t1 in
          let uu____6381 = unboxInt t2 in (uu____6380, uu____6381) in
        mkGT uu____6375 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6384; rng = uu____6385;_}::[])
        ->
        let uu____6398 =
          let uu____6403 = unboxBool t1 in
          let uu____6404 = unboxBool t2 in (uu____6403, uu____6404) in
        mkAnd uu____6398 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6407; rng = uu____6408;_}::[])
        ->
        let uu____6421 =
          let uu____6426 = unboxBool t1 in
          let uu____6427 = unboxBool t2 in (uu____6426, uu____6427) in
        mkOr uu____6421 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6429; rng = uu____6430;_}::[])
        -> let uu____6443 = unboxBool t1 in mkNot uu____6443 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6447; rng = uu____6448;_}::[])
        when
        let uu____6461 = getBoxedInteger t0 in FStar_Util.is_some uu____6461
        ->
        let sz =
          let uu____6465 = getBoxedInteger t0 in
          match uu____6465 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6469 -> failwith "impossible" in
        let uu____6472 =
          let uu____6477 = unboxBitVec sz t1 in
          let uu____6478 = unboxBitVec sz t2 in (uu____6477, uu____6478) in
        mkBvUlt uu____6472 t.rng
    | App
        (Var
         "Prims.equals",uu____6479::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6483;
                                      rng = uu____6484;_}::uu____6485::[])
        when
        let uu____6498 = getBoxedInteger t0 in FStar_Util.is_some uu____6498
        ->
        let sz =
          let uu____6502 = getBoxedInteger t0 in
          match uu____6502 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6506 -> failwith "impossible" in
        let uu____6509 =
          let uu____6514 = unboxBitVec sz t1 in
          let uu____6515 = unboxBitVec sz t2 in (uu____6514, uu____6515) in
        mkBvUlt uu____6509 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___50_6519 = unboxBool t1 in
        {
          tm = (uu___50_6519.tm);
          freevars = (uu___50_6519.freevars);
          rng = (t.rng)
        }
    | uu____6520 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6553 = FStar_Options.unthrottle_inductives () in
        if uu____6553
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel:
  term FStar_Pervasives_Native.option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | FStar_Pervasives_Native.None  -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
let mk_NoHoist: term -> term -> term =
  fun dummy  -> fun b  -> mkApp ("NoHoist", [dummy; b]) b.rng
let mk_Destruct: term -> FStar_Range.range -> term =
  fun v1  -> mkApp ("Destruct", [v1])
let mk_Rank: term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x])
let mk_tester: Prims.string -> term -> term =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng
let mk_ApplyTF: term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng
let mk_ApplyTT: term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r
let mk_String_const: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____6626 =
        let uu____6633 = let uu____6636 = mkInteger' i norng in [uu____6636] in
        ("FString_const", uu____6633) in
      mkApp uu____6626 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6648 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____6648 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6668 =
         let uu____6675 =
           let uu____6678 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____6678] in
         ("SFuel", uu____6675) in
       mkApp uu____6668 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option ->
      FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (FStar_Pervasives_Native.Some p11,FStar_Pervasives_Native.Some p21)
            ->
            let uu____6712 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____6712
        | (FStar_Pervasives_Native.Some p,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.None
let mk_and_opt_l:
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6765 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6765
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6780 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6780
let mk_haseq: term -> term =
  fun t  ->
    let uu____6788 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____6788