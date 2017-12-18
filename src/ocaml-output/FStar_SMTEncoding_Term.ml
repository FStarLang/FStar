open Prims
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
    match projectee with | Integer _0 -> true | uu____432 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____444 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____460 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____490 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____538 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____610 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____646 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____680 -> false
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
  (Prims.string,sort,Prims.bool) FStar_Pervasives_Native.tuple3[@@deriving
                                                                 show]
type constructor_t =
  (Prims.string,constructor_field Prims.list,sort,Prims.int,Prims.bool)
    FStar_Pervasives_Native.tuple5[@@deriving show]
type constructors = constructor_t Prims.list[@@deriving show]
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string[@@deriving show]
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____833 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____845 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____857 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term;
  assumption_caption: caption;
  assumption_name: Prims.string;
  assumption_fact_ids: fact_db_id Prims.list;}[@@deriving show]
let __proj__Mkassumption__item__assumption_term: assumption -> term =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_term
let __proj__Mkassumption__item__assumption_caption: assumption -> caption =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_caption
let __proj__Mkassumption__item__assumption_name: assumption -> Prims.string =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_name
let __proj__Mkassumption__item__assumption_fact_ids:
  assumption -> fact_db_id Prims.list =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_fact_ids
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
    match projectee with | DefPrelude  -> true | uu____986 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1001 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1055 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1103 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1115 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1127 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1139 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1153 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1170 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1174 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1178 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1182 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1191 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1214 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1218 -> false
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
  'Auu____1238 'Auu____1239 .
    ('Auu____1239,'Auu____1238) FStar_Pervasives_Native.tuple2 ->
      'Auu____1238
  = fun x  -> FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1268 -> false
let freevar_sort: term -> sort =
  fun uu___74_1275  ->
    match uu___74_1275 with
    | { tm = FreeV x; freevars = uu____1277; rng = uu____1278;_} -> fv_sort x
    | uu____1291 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___75_1294  ->
    match uu___75_1294 with
    | { tm = FreeV fv; freevars = uu____1296; rng = uu____1297;_} -> fv
    | uu____1310 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1326 -> []
    | BoundV uu____1331 -> []
    | FreeV fv -> [fv]
    | App (uu____1349,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1359,uu____1360,uu____1361,uu____1362,t1) -> freevars t1
    | Labeled (t1,uu____1381,uu____1382) -> freevars t1
    | LblPos (t1,uu____1384) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1398 = FStar_ST.op_Bang t.freevars in
    match uu____1398 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1493 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1493 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___76_1565  ->
    match uu___76_1565 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___77_1568  ->
    match uu___77_1568 with
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
        let uu____1570 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1570
    | NatToBv n1 ->
        let uu____1572 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1572
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___78_1578  ->
    match uu___78_1578 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1582 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1582
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1590 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1590
    | FreeV x ->
        let uu____1596 =
          let uu____1597 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1597 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1596
    | App (op,tms) ->
        let uu____1604 =
          let uu____1605 = op_to_string op in
          let uu____1606 =
            let uu____1607 =
              let uu____1608 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1608 (FStar_String.concat " ") in
            Prims.strcat uu____1607 ")" in
          Prims.strcat uu____1605 uu____1606 in
        Prims.strcat "(" uu____1604
    | Labeled (t1,r1,r2) ->
        let uu____1616 = hash_of_term t1 in
        let uu____1617 =
          let uu____1618 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1618 in
        Prims.strcat uu____1616 uu____1617
    | LblPos (t1,r) ->
        let uu____1621 =
          let uu____1622 = hash_of_term t1 in
          Prims.strcat uu____1622
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1621
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1644 =
          let uu____1645 =
            let uu____1646 =
              let uu____1647 =
                let uu____1648 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1648 (FStar_String.concat " ") in
              let uu____1653 =
                let uu____1654 =
                  let uu____1655 = hash_of_term body in
                  let uu____1656 =
                    let uu____1657 =
                      let uu____1658 = weightToSmt wopt in
                      let uu____1659 =
                        let uu____1660 =
                          let uu____1661 =
                            let uu____1662 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1678 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1678
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1662
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1661 "))" in
                        Prims.strcat " " uu____1660 in
                      Prims.strcat uu____1658 uu____1659 in
                    Prims.strcat " " uu____1657 in
                  Prims.strcat uu____1655 uu____1656 in
                Prims.strcat ")(! " uu____1654 in
              Prims.strcat uu____1647 uu____1653 in
            Prims.strcat " (" uu____1646 in
          Prims.strcat (qop_to_string qop) uu____1645 in
        Prims.strcat "(" uu____1644
    | Let (es,body) ->
        let uu____1691 =
          let uu____1692 =
            let uu____1693 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1693 (FStar_String.concat " ") in
          let uu____1698 =
            let uu____1699 =
              let uu____1700 = hash_of_term body in
              Prims.strcat uu____1700 ")" in
            Prims.strcat ") " uu____1699 in
          Prims.strcat uu____1692 uu____1698 in
        Prims.strcat "(let (" uu____1691
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
    let uu____1728 =
      let uu____1729 = FStar_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu____1729 in
    mkBoxFunctions uu____1728
let isInjective: Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1735 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3") in
       uu____1735 = "Box") &&
        (let uu____1737 =
           let uu____1738 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c  -> c = 46) uu____1738 in
         Prims.op_Negation uu____1737)
    else false
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1755 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1755; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1808 =
        let uu____1809 = FStar_Util.ensure_decimal i in Integer uu____1809 in
      mk uu____1808 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1816 = FStar_Util.string_of_int i in mkInteger uu____1816 r
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
  fun uu____1865  ->
    fun r  -> match uu____1865 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1887) -> mkFalse r
      | App (FalseOp ,uu____1892) -> mkTrue r
      | uu____1897 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1908  ->
    fun r  ->
      match uu____1908 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1916),uu____1917) -> t2
           | (uu____1922,App (TrueOp ,uu____1923)) -> t1
           | (App (FalseOp ,uu____1928),uu____1929) -> mkFalse r
           | (uu____1934,App (FalseOp ,uu____1935)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1952,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1961) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1968 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1983  ->
    fun r  ->
      match uu____1983 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1991),uu____1992) -> mkTrue r
           | (uu____1997,App (TrueOp ,uu____1998)) -> mkTrue r
           | (App (FalseOp ,uu____2003),uu____2004) -> t2
           | (uu____2009,App (FalseOp ,uu____2010)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2027,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2036) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2043 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2058  ->
    fun r  ->
      match uu____2058 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2066,App (TrueOp ,uu____2067)) -> mkTrue r
           | (App (FalseOp ,uu____2072),uu____2073) -> mkTrue r
           | (App (TrueOp ,uu____2078),uu____2079) -> t2
           | (uu____2084,App (Imp ,t1'::t2'::[])) ->
               let uu____2089 =
                 let uu____2096 =
                   let uu____2099 = mkAnd (t1, t1') r in [uu____2099; t2'] in
                 (Imp, uu____2096) in
               mkApp' uu____2089 r
           | uu____2102 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2120  ->
      fun r  -> match uu____2120 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
    fun uu____2219  ->
      fun r  ->
        match uu____2219 with
        | (t1,t2) ->
            let uu____2227 =
              let uu____2234 =
                let uu____2237 =
                  let uu____2240 = mkNatToBv sz t2 r in [uu____2240] in
                t1 :: uu____2237 in
              (BvShl, uu____2234) in
            mkApp' uu____2227 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2254  ->
      fun r  ->
        match uu____2254 with
        | (t1,t2) ->
            let uu____2262 =
              let uu____2269 =
                let uu____2272 =
                  let uu____2275 = mkNatToBv sz t2 r in [uu____2275] in
                t1 :: uu____2272 in
              (BvShr, uu____2269) in
            mkApp' uu____2262 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2289  ->
      fun r  ->
        match uu____2289 with
        | (t1,t2) ->
            let uu____2297 =
              let uu____2304 =
                let uu____2307 =
                  let uu____2310 = mkNatToBv sz t2 r in [uu____2310] in
                t1 :: uu____2307 in
              (BvUdiv, uu____2304) in
            mkApp' uu____2297 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2324  ->
      fun r  ->
        match uu____2324 with
        | (t1,t2) ->
            let uu____2332 =
              let uu____2339 =
                let uu____2342 =
                  let uu____2345 = mkNatToBv sz t2 r in [uu____2345] in
                t1 :: uu____2342 in
              (BvMod, uu____2339) in
            mkApp' uu____2332 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2359  ->
      fun r  ->
        match uu____2359 with
        | (t1,t2) ->
            let uu____2367 =
              let uu____2374 =
                let uu____2377 =
                  let uu____2380 = mkNatToBv sz t2 r in [uu____2380] in
                t1 :: uu____2377 in
              (BvMul, uu____2374) in
            mkApp' uu____2367 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2407  ->
    fun r  ->
      match uu____2407 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2423 -> mk_bin_op Eq (t1, t2) r)
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
  fun uu____2510  ->
    fun r  ->
      match uu____2510 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2521) -> t2
           | App (FalseOp ,uu____2526) -> t3
           | uu____2531 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2532),App (TrueOp ,uu____2533)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2542),uu____2543) ->
                    let uu____2548 =
                      let uu____2553 = mkNot t1 t1.rng in (uu____2553, t3) in
                    mkImp uu____2548 r
                | (uu____2554,App (TrueOp ,uu____2555)) -> mkImp (t1, t2) r
                | (uu____2560,uu____2561) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____2604  ->
    fun r  ->
      match uu____2604 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2646) -> body
             | uu____2651 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2670  ->
    fun r  ->
      match uu____2670 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2704 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2704 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2723 = FStar_ST.op_Bang t1.freevars in
        match uu____2723 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2806 ->
            (match t1.tm with
             | Integer uu____2815 -> t1
             | BoundV uu____2816 -> t1
             | FreeV x ->
                 let uu____2822 = index_of x in
                 (match uu____2822 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2832 =
                   let uu____2839 = FStar_List.map (aux ix) tms in
                   (op, uu____2839) in
                 mkApp' uu____2832 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2847 =
                   let uu____2848 =
                     let uu____2855 = aux ix t2 in (uu____2855, r1, r2) in
                   Labeled uu____2848 in
                 mk uu____2847 t2.rng
             | LblPos (t2,r) ->
                 let uu____2858 =
                   let uu____2859 =
                     let uu____2864 = aux ix t2 in (uu____2864, r) in
                   LblPos uu____2859 in
                 mk uu____2858 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2887 =
                   let uu____2906 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2927 = aux (ix + n1) body in
                   (qop, uu____2906, wopt, vars, uu____2927) in
                 mkQuant uu____2887 t1.rng
             | Let (es,body) ->
                 let uu____2946 =
                   FStar_List.fold_left
                     (fun uu____2964  ->
                        fun e  ->
                          match uu____2964 with
                          | (ix1,l) ->
                              let uu____2984 =
                                let uu____2987 = aux ix1 e in uu____2987 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____2984))
                     (ix, []) es in
                 (match uu____2946 with
                  | (ix1,es_rev) ->
                      let uu____2998 =
                        let uu____3005 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____3005) in
                      mkLet uu____2998 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3029 -> t1
        | FreeV uu____3030 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3047 =
              let uu____3054 = FStar_List.map (aux shift) tms2 in
              (op, uu____3054) in
            mkApp' uu____3047 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3062 =
              let uu____3063 =
                let uu____3070 = aux shift t2 in (uu____3070, r1, r2) in
              Labeled uu____3063 in
            mk uu____3062 t2.rng
        | LblPos (t2,r) ->
            let uu____3073 =
              let uu____3074 =
                let uu____3079 = aux shift t2 in (uu____3079, r) in
              LblPos uu____3074 in
            mk uu____3073 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____3107 =
              let uu____3126 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____3143 = aux shift1 body in
              (qop, uu____3126, wopt, vars, uu____3143) in
            mkQuant uu____3107 t1.rng
        | Let (es,body) ->
            let uu____3158 =
              FStar_List.fold_left
                (fun uu____3176  ->
                   fun e  ->
                     match uu____3176 with
                     | (ix,es1) ->
                         let uu____3196 =
                           let uu____3199 = aux shift e in uu____3199 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____3196))
                (shift, []) es in
            (match uu____3158 with
             | (shift1,es_rev) ->
                 let uu____3210 =
                   let uu____3217 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____3217) in
                 mkLet uu____3210 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____3229 = abstr [fv] t in inst [s] uu____3229
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3252  ->
    match uu____3252 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3294 =
          let uu____3313 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____3330 = FStar_List.map fv_sort vars in
          let uu____3337 = abstr vars body in
          (qop, uu____3313, wopt, uu____3330, uu____3337) in
        mkQuant uu____3294
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3366  ->
    fun r  ->
      match uu____3366 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3430  ->
    fun r  ->
      match uu____3430 with
      | (pats,wopt,vars,body) ->
          let uu____3462 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____3462 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3485  ->
    fun r  ->
      match uu____3485 with
      | (pats,vars,body) ->
          let uu____3508 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3508 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3531  ->
    fun r  ->
      match uu____3531 with
      | (pats,vars,body) ->
          let uu____3554 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3554 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3577  ->
    fun r  ->
      match uu____3577 with
      | (bindings,body) ->
          let uu____3603 = FStar_List.split bindings in
          (match uu____3603 with
           | (vars,es) ->
               let uu____3622 =
                 let uu____3629 = abstr vars body in (es, uu____3629) in
               mkLet uu____3622 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3650  ->
    match uu____3650 with
    | (nm,vars,s,tm,c) ->
        let uu____3684 =
          let uu____3697 = FStar_List.map fv_sort vars in
          let uu____3704 = abstr vars tm in
          (nm, uu____3697, s, uu____3704, c) in
        DefineFun uu____3684
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3710 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3710
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3719  ->
    fun id1  ->
      match uu____3719 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3729 =
              let uu____3730 =
                let uu____3735 = mkInteger' id1 norng in
                let uu____3736 =
                  let uu____3737 =
                    let uu____3744 = constr_id_of_sort sort in
                    let uu____3745 =
                      let uu____3748 = mkApp (tok_name, []) norng in
                      [uu____3748] in
                    (uu____3744, uu____3745) in
                  mkApp uu____3737 norng in
                (uu____3735, uu____3736) in
              mkEq uu____3730 norng in
            {
              assumption_term = uu____3729;
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
  fun uu____3765  ->
    match uu____3765 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1 in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3797 =
                      let uu____3802 =
                        let uu____3803 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____3803 in
                      (uu____3802, s) in
                    mkFreeV uu____3797 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____3811 =
            let uu____3818 = constr_id_of_sort sort in (uu____3818, [capp]) in
          mkApp uu____3811 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____3823 =
            let uu____3824 =
              let uu____3835 =
                let uu____3836 =
                  let uu____3841 = mkInteger id2 norng in
                  (uu____3841, cid_app) in
                mkEq uu____3836 norng in
              ([[capp]], bvar_names, uu____3835) in
            mkForall uu____3824 norng in
          {
            assumption_term = uu____3823;
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
  fun uu____3862  ->
    match uu____3862 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____3883 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____3883 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____3903 = let uu____3908 = bvar_name i in (uu____3908, s) in
          mkFreeV uu____3903 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3929  ->
                    match uu____3929 with
                    | (uu____3936,s,uu____3938) ->
                        let uu____3939 = bvar i s in uu____3939 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____3948 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3976  ->
                    match uu____3976 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____3999 =
                              let uu____4000 =
                                let uu____4011 =
                                  let uu____4012 =
                                    let uu____4017 =
                                      let uu____4018 = bvar i s in
                                      uu____4018 norng in
                                    (cproj_app, uu____4017) in
                                  mkEq uu____4012 norng in
                                ([[capp]], bvar_names, uu____4011) in
                              mkForall uu____4000 norng in
                            {
                              assumption_term = uu____3999;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____3948 FStar_List.flatten
let constructor_to_decl: constructor_t -> decls_t =
  fun uu____4040  ->
    match uu____4040 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4068  ->
                  match uu____4068 with
                  | (uu____4075,sort1,uu____4077) -> sort1)) in
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
            let uu____4095 =
              let uu____4100 =
                let uu____4101 =
                  let uu____4108 = constr_id_of_sort sort in
                  (uu____4108, [xx]) in
                mkApp uu____4101 norng in
              let uu____4111 =
                let uu____4112 = FStar_Util.string_of_int id1 in
                mkInteger uu____4112 norng in
              (uu____4100, uu____4111) in
            mkEq uu____4095 norng in
          let uu____4113 =
            let uu____4128 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4178  ->
                        match uu____4178 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4208 = mkApp (proj, [xx]) norng in
                              (uu____4208, [])
                            else
                              (let fi =
                                 let uu____4227 =
                                   let uu____4228 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____4228 in
                                 (uu____4227, s) in
                               let uu____4229 = mkFreeV fi norng in
                               (uu____4229, [fi])))) in
            FStar_All.pipe_right uu____4128 FStar_List.split in
          match uu____4113 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____4310 =
                  let uu____4315 = mkApp (name, proj_terms) norng in
                  (xx, uu____4315) in
                mkEq uu____4310 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4323 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____4364 =
          let uu____4367 =
            let uu____4368 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____4368 in
          uu____4367 :: cdecl :: cid :: projs in
        let uu____4369 =
          let uu____4372 =
            let uu____4375 =
              let uu____4376 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____4376 in
            [uu____4375] in
          FStar_List.append [disc] uu____4372 in
        FStar_List.append uu____4364 uu____4369
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
          let uu____4423 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4478  ->
                    fun s  ->
                      match uu____4478 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4528 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____4532 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____4532 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____4545 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____4545 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____4423 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4622 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____4622 with
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
              (let uu____4786 = FStar_Util.string_of_int n1 in
               FStar_Util.format2 "%s.%s" enclosing_name uu____4786) in
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
                               "Prims.guard_free",{ tm = BoundV uu____4828;
                                                    freevars = uu____4829;
                                                    rng = uu____4830;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____4844 -> tm)))) in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1")) in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____4884 = FStar_List.nth names1 i in
              FStar_All.pipe_right uu____4884 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____4899 = op_to_string op in
              let uu____4900 =
                let uu____4901 = FStar_List.map (aux1 n1 names1) tms in
                FStar_All.pipe_right uu____4901 (FStar_String.concat "\n") in
              FStar_Util.format2 "(%s %s)" uu____4899 uu____4900
          | Labeled (t2,uu____4907,uu____4908) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____4911 = aux1 n1 names1 t2 in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____4911 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid () in
              let uu____4934 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts in
              (match uu____4934 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ") in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____4983 ->
                         let uu____4988 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5004 =
                                     let uu____5005 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5011 = aux1 n2 names2 p in
                                            FStar_Util.format1 "%s"
                                              uu____5011) pats2 in
                                     FStar_String.concat " " uu____5005 in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5004)) in
                         FStar_All.pipe_right uu____4988
                           (FStar_String.concat "\n") in
                   let uu____5014 =
                     let uu____5017 =
                       let uu____5020 =
                         let uu____5023 = aux1 n2 names2 body in
                         let uu____5024 =
                           let uu____5027 = weightToSmt wopt in
                           [uu____5027; pats_str; qid] in
                         uu____5023 :: uu____5024 in
                       binders1 :: uu____5020 in
                     (qop_to_string qop) :: uu____5017 in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5014)
          | Let (es,body) ->
              let uu____5034 =
                FStar_List.fold_left
                  (fun uu____5071  ->
                     fun e  ->
                       match uu____5071 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5121 = FStar_Util.string_of_int n0 in
                             Prims.strcat "@lb" uu____5121 in
                           let names01 = (nm, Term_sort) :: names0 in
                           let b =
                             let uu____5134 = aux1 n1 names1 e in
                             FStar_Util.format2 "(%s %s)" nm uu____5134 in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es in
              (match uu____5034 with
               | (names2,binders,n2) ->
                   let uu____5166 = aux1 n2 names2 body in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5166)
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5174 = FStar_Range.string_of_range t1.rng in
            let uu____5175 = FStar_Range.string_of_use_range t1.rng in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5174
              uu____5175 s
          else s in
        aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___79_5181  ->
    match uu___79_5181 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5185 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5200 -> (hd1, "...") in
        (match uu____5185 with
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
            let uu____5231 = FStar_Options.log_queries () in
            if uu____5231
            then
              let uu____5232 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___80_5236  ->
                     match uu___80_5236 with | [] -> "" | h::t -> h) in
              FStar_Util.format1 "\n; %s" uu____5232
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts in
            let uu____5255 = caption_to_string c in
            let uu____5256 = strSort retsort in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5255 f
              (FStar_String.concat " " l) uu____5256
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5266 = name_macro_binders arg_sorts in
            (match uu____5266 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5298 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                   inst uu____5298 body in
                 let uu____5311 = caption_to_string c in
                 let uu____5312 = strSort retsort in
                 let uu____5313 = termToSmt print_ranges (escape f) body1 in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5311 f (FStar_String.concat " " binders) uu____5312
                   uu____5313)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___81_5331  ->
                      match uu___81_5331 with
                      | Name n1 ->
                          Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                      | Namespace ns ->
                          Prims.strcat "Namespace "
                            (FStar_Ident.text_of_lid ns)
                      | Tag t -> Prims.strcat "Tag " t)) in
            let fids =
              let uu____5336 = FStar_Options.log_queries () in
              if uu____5336
              then
                let uu____5337 =
                  let uu____5338 = fact_ids_to_string a.assumption_fact_ids in
                  FStar_String.concat "; " uu____5338 in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5337
              else "" in
            let n1 = escape a.assumption_name in
            let uu____5343 = caption_to_string a.assumption_caption in
            let uu____5344 = termToSmt print_ranges n1 a.assumption_term in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5343
              fids uu____5344 n1
        | Eval t ->
            let uu____5346 = termToSmt print_ranges "eval" t in
            FStar_Util.format1 "(eval %s)" uu____5346
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5348 -> ""
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
      let uu____5677 =
        let uu____5680 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____5680
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____5677 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____5695 =
      let uu____5714 =
        let uu____5715 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5715 in
      let uu____5720 =
        let uu____5729 =
          let uu____5736 =
            let uu____5737 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____5737 in
          (uu____5736, (BitVec_sort sz), true) in
        [uu____5729] in
      (uu____5714, uu____5720, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____5695 constructor_to_decl
let __range_c: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let mk_Range_const: Prims.unit -> term =
  fun uu____5791  ->
    let i = FStar_ST.op_Bang __range_c in
    (let uu____5842 =
       let uu____5843 = FStar_ST.op_Bang __range_c in
       uu____5843 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals __range_c uu____5842);
    (let uu____5940 =
       let uu____5947 = let uu____5950 = mkInteger' i norng in [uu____5950] in
       ("Range_const", uu____5947) in
     mkApp uu____5940 norng)
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____5972 =
        let uu____5979 = let uu____5982 = mkInteger' i norng in [uu____5982] in
        ("Tm_uvar", uu____5979) in
      mkApp uu____5972 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6003 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6015 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____6015 u v1 t
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
      let uu____6040 =
        let uu____6041 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6041 in
      let uu____6046 =
        let uu____6047 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6047 in
      elim_box true uu____6040 uu____6046 t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6058 =
        let uu____6059 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6059 in
      let uu____6064 =
        let uu____6065 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6065 in
      elim_box true uu____6058 uu____6064 t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6077 -> FStar_Exn.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6085 -> FStar_Exn.raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6101 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____6101
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6113 = op_to_string op in
        let uu____6114 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____6113 uu____6114
    | Labeled (t1,r1,r2) ->
        let uu____6118 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6118
    | LblPos (t1,s) ->
        let uu____6121 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6121
    | Quant (qop,l,uu____6124,uu____6125,t1) ->
        let uu____6143 = print_smt_term_list_list l in
        let uu____6144 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6143
          uu____6144
    | Let (es,body) ->
        let uu____6151 = print_smt_term_list es in
        let uu____6152 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____6151 uu____6152
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____6156 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____6156 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6175 =
             let uu____6176 =
               let uu____6177 = print_smt_term_list l1 in
               Prims.strcat uu____6177 " ] " in
             Prims.strcat "; [ " uu____6176 in
           Prims.strcat s uu____6175) "" l
let getBoxedInteger: term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6192 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____6192
         | uu____6193 -> FStar_Pervasives_Native.None)
    | uu____6194 -> FStar_Pervasives_Native.None
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6203::t1::t2::[]);
                       freevars = uu____6206; rng = uu____6207;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6220::t1::t2::[]);
                       freevars = uu____6223; rng = uu____6224;_}::[])
        -> let uu____6237 = mkEq (t1, t2) norng in mkNot uu____6237 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6240; rng = uu____6241;_}::[])
        ->
        let uu____6254 =
          let uu____6259 = unboxInt t1 in
          let uu____6260 = unboxInt t2 in (uu____6259, uu____6260) in
        mkLTE uu____6254 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6263; rng = uu____6264;_}::[])
        ->
        let uu____6277 =
          let uu____6282 = unboxInt t1 in
          let uu____6283 = unboxInt t2 in (uu____6282, uu____6283) in
        mkLT uu____6277 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6286; rng = uu____6287;_}::[])
        ->
        let uu____6300 =
          let uu____6305 = unboxInt t1 in
          let uu____6306 = unboxInt t2 in (uu____6305, uu____6306) in
        mkGTE uu____6300 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6309; rng = uu____6310;_}::[])
        ->
        let uu____6323 =
          let uu____6328 = unboxInt t1 in
          let uu____6329 = unboxInt t2 in (uu____6328, uu____6329) in
        mkGT uu____6323 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6332; rng = uu____6333;_}::[])
        ->
        let uu____6346 =
          let uu____6351 = unboxBool t1 in
          let uu____6352 = unboxBool t2 in (uu____6351, uu____6352) in
        mkAnd uu____6346 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6355; rng = uu____6356;_}::[])
        ->
        let uu____6369 =
          let uu____6374 = unboxBool t1 in
          let uu____6375 = unboxBool t2 in (uu____6374, uu____6375) in
        mkOr uu____6369 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6377; rng = uu____6378;_}::[])
        -> let uu____6391 = unboxBool t1 in mkNot uu____6391 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6395; rng = uu____6396;_}::[])
        when
        let uu____6409 = getBoxedInteger t0 in FStar_Util.is_some uu____6409
        ->
        let sz =
          let uu____6413 = getBoxedInteger t0 in
          match uu____6413 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6417 -> failwith "impossible" in
        let uu____6420 =
          let uu____6425 = unboxBitVec sz t1 in
          let uu____6426 = unboxBitVec sz t2 in (uu____6425, uu____6426) in
        mkBvUlt uu____6420 t.rng
    | App
        (Var
         "Prims.equals",uu____6427::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6431;
                                      rng = uu____6432;_}::uu____6433::[])
        when
        let uu____6446 = getBoxedInteger t0 in FStar_Util.is_some uu____6446
        ->
        let sz =
          let uu____6450 = getBoxedInteger t0 in
          match uu____6450 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6454 -> failwith "impossible" in
        let uu____6457 =
          let uu____6462 = unboxBitVec sz t1 in
          let uu____6463 = unboxBitVec sz t2 in (uu____6462, uu____6463) in
        mkBvUlt uu____6457 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___82_6467 = unboxBool t1 in
        {
          tm = (uu___82_6467.tm);
          freevars = (uu___82_6467.freevars);
          rng = (t.rng)
        }
    | uu____6468 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6501 = FStar_Options.unthrottle_inductives () in
        if uu____6501
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
      let uu____6574 =
        let uu____6581 = let uu____6584 = mkInteger' i norng in [uu____6584] in
        ("FString_const", uu____6581) in
      mkApp uu____6574 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6596 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____6596 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6616 =
         let uu____6623 =
           let uu____6626 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____6626] in
         ("SFuel", uu____6623) in
       mkApp uu____6616 norng)
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
            let uu____6660 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____6660
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
      let uu____6713 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6713
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6728 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6728
let mk_haseq: term -> term =
  fun t  ->
    let uu____6736 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____6736