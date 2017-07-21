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
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____29 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____34 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____39 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____44 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____49 -> false
let uu___is_BitVec_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____55 -> false
let __proj__BitVec_sort__item___0: sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____73 -> false
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____103 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____129 -> false
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
        let uu____143 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ BitVec %s)" uu____143
    | Array (s1,s2) ->
        let uu____146 = strSort s1 in
        let uu____147 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____146 uu____147
    | Arrow (s1,s2) ->
        let uu____150 = strSort s1 in
        let uu____151 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____150 uu____151
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
  | Var of Prims.string
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____169 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____174 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____179 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____184 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____189 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____194 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____199 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____204 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____209 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____214 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____219 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____224 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____229 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____234 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____239 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____244 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____249 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____254 -> false
let uu___is_BvAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____259 -> false
let uu___is_BvXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____264 -> false
let uu___is_BvOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____269 -> false
let uu___is_BvShl: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____274 -> false
let uu___is_BvShr: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____279 -> false
let uu___is_BvUdiv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____284 -> false
let uu___is_BvMod: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____289 -> false
let uu___is_BvMul: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____294 -> false
let uu___is_BvUlt: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____299 -> false
let uu___is_BvUext: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____305 -> false
let __proj__BvUext__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0
let uu___is_NatToBv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____319 -> false
let __proj__NatToBv__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
let uu___is_BvToNat: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____332 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____337 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____343 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____356 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____361 -> false
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
  | LblPos of (term,Prims.string) FStar_Pervasives_Native.tuple2
and term =
  {
  tm: term';
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____464 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____478 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____496 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____528 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____578 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____652 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____690 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____726 -> false
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
type pat = term
type fv = (Prims.string,sort) FStar_Pervasives_Native.tuple2
type fvs = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type caption = Prims.string FStar_Pervasives_Native.option
type binders = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type constructor_field =
  (Prims.string,sort,Prims.bool) FStar_Pervasives_Native.tuple3
type constructor_t =
  (Prims.string,constructor_field Prims.list,sort,Prims.int,Prims.bool)
    FStar_Pervasives_Native.tuple5
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____866 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____880 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____894 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term;
  assumption_caption: caption;
  assumption_name: Prims.string;
  assumption_fact_ids: fact_db_id Prims.list;}
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
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1029 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1045 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1101 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1151 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1165 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1179 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1193 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1209 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1228 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1233 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1238 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1243 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1253 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1278 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1283 -> false
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort:
  'Auu____1308 'Auu____1309 .
    ('Auu____1309,'Auu____1308) FStar_Pervasives_Native.tuple2 ->
      'Auu____1308
  = fun x  -> FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1340 -> false
let freevar_sort: term -> sort =
  fun uu___87_1348  ->
    match uu___87_1348 with
    | { tm = FreeV x; freevars = uu____1350; rng = uu____1351;_} -> fv_sort x
    | uu____1364 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___88_1368  ->
    match uu___88_1368 with
    | { tm = FreeV fv; freevars = uu____1370; rng = uu____1371;_} -> fv
    | uu____1384 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1401 -> []
    | BoundV uu____1406 -> []
    | FreeV fv -> [fv]
    | App (uu____1424,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1434,uu____1435,uu____1436,uu____1437,t1) -> freevars t1
    | Labeled (t1,uu____1456,uu____1457) -> freevars t1
    | LblPos (t1,uu____1459) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1474 = FStar_ST.read t.freevars in
    match uu____1474 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1513 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1513 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___89_1530  ->
    match uu___89_1530 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___90_1534  ->
    match uu___90_1534 with
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
    | BvShl  -> "bvshl"
    | BvShr  -> "bvlshr"
    | BvUdiv  -> "bvudiv"
    | BvMod  -> "bvurem"
    | BvMul  -> "bvmul"
    | BvUlt  -> "bvult"
    | BvToNat  -> "bv2int"
    | BvUext n1 ->
        let uu____1536 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1536
    | NatToBv n1 ->
        let uu____1538 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1538
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1545  ->
    match uu___91_1545 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1549 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1549
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1557 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1557
    | FreeV x ->
        let uu____1563 =
          let uu____1564 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1564 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1563
    | App (op,tms) ->
        let uu____1571 =
          let uu____1572 = op_to_string op in
          let uu____1573 =
            let uu____1574 =
              let uu____1575 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1575 (FStar_String.concat " ") in
            Prims.strcat uu____1574 ")" in
          Prims.strcat uu____1572 uu____1573 in
        Prims.strcat "(" uu____1571
    | Labeled (t1,r1,r2) ->
        let uu____1583 = hash_of_term t1 in
        let uu____1584 =
          let uu____1585 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1585 in
        Prims.strcat uu____1583 uu____1584
    | LblPos (t1,r) ->
        let uu____1588 =
          let uu____1589 = hash_of_term t1 in
          Prims.strcat uu____1589
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1588
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1611 =
          let uu____1612 =
            let uu____1613 =
              let uu____1614 =
                let uu____1615 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1615 (FStar_String.concat " ") in
              let uu____1620 =
                let uu____1621 =
                  let uu____1622 = hash_of_term body in
                  let uu____1623 =
                    let uu____1624 =
                      let uu____1625 = weightToSmt wopt in
                      let uu____1626 =
                        let uu____1627 =
                          let uu____1628 =
                            let uu____1629 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1645 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1645
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1629
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1628 "))" in
                        Prims.strcat " " uu____1627 in
                      Prims.strcat uu____1625 uu____1626 in
                    Prims.strcat " " uu____1624 in
                  Prims.strcat uu____1622 uu____1623 in
                Prims.strcat ")(! " uu____1621 in
              Prims.strcat uu____1614 uu____1620 in
            Prims.strcat " (" uu____1613 in
          Prims.strcat (qop_to_string qop) uu____1612 in
        Prims.strcat "(" uu____1611
    | Let (es,body) ->
        let uu____1658 =
          let uu____1659 =
            let uu____1660 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1660 (FStar_String.concat " ") in
          let uu____1665 =
            let uu____1666 =
              let uu____1667 = hash_of_term body in
              Prims.strcat uu____1667 ")" in
            Prims.strcat ") " uu____1666 in
          Prims.strcat uu____1659 uu____1665 in
        Prims.strcat "(let (" uu____1658
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
    let uu____1697 =
      let uu____1698 = FStar_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu____1698 in
    mkBoxFunctions uu____1697
let isInjective: Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1705 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3") in
       uu____1705 = "Box") &&
        (let uu____1707 =
           let uu____1708 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c  -> c = '.') uu____1708 in
         Prims.op_Negation uu____1707)
    else false
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1722 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1722; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1767 =
        let uu____1768 = FStar_Util.ensure_decimal i in Integer uu____1768 in
      mk uu____1767 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1777 = FStar_Util.string_of_int i in mkInteger uu____1777 r
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
  fun uu____1834  ->
    fun r  -> match uu____1834 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1858) -> mkFalse r
      | App (FalseOp ,uu____1863) -> mkTrue r
      | uu____1868 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1881  ->
    fun r  ->
      match uu____1881 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1889),uu____1890) -> t2
           | (uu____1895,App (TrueOp ,uu____1896)) -> t1
           | (App (FalseOp ,uu____1901),uu____1902) -> mkFalse r
           | (uu____1907,App (FalseOp ,uu____1908)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1925,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1934) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1941 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1958  ->
    fun r  ->
      match uu____1958 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1966),uu____1967) -> mkTrue r
           | (uu____1972,App (TrueOp ,uu____1973)) -> mkTrue r
           | (App (FalseOp ,uu____1978),uu____1979) -> t2
           | (uu____1984,App (FalseOp ,uu____1985)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2002,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2011) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2018 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2035  ->
    fun r  ->
      match uu____2035 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2043,App (TrueOp ,uu____2044)) -> mkTrue r
           | (App (FalseOp ,uu____2049),uu____2050) -> mkTrue r
           | (App (TrueOp ,uu____2055),uu____2056) -> t2
           | (uu____2061,App (Imp ,t1'::t2'::[])) ->
               let uu____2066 =
                 let uu____2073 =
                   let uu____2076 = mkAnd (t1, t1') r in [uu____2076; t2'] in
                 (Imp, uu____2073) in
               mkApp' uu____2066 r
           | uu____2079 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2100  ->
      fun r  -> match uu____2100 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
let mkBvShl:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2202  ->
      fun r  ->
        match uu____2202 with
        | (t1,t2) ->
            let uu____2210 =
              let uu____2217 =
                let uu____2220 =
                  let uu____2223 = mkNatToBv sz t2 r in [uu____2223] in
                t1 :: uu____2220 in
              (BvShl, uu____2217) in
            mkApp' uu____2210 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2240  ->
      fun r  ->
        match uu____2240 with
        | (t1,t2) ->
            let uu____2248 =
              let uu____2255 =
                let uu____2258 =
                  let uu____2261 = mkNatToBv sz t2 r in [uu____2261] in
                t1 :: uu____2258 in
              (BvShr, uu____2255) in
            mkApp' uu____2248 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2278  ->
      fun r  ->
        match uu____2278 with
        | (t1,t2) ->
            let uu____2286 =
              let uu____2293 =
                let uu____2296 =
                  let uu____2299 = mkNatToBv sz t2 r in [uu____2299] in
                t1 :: uu____2296 in
              (BvUdiv, uu____2293) in
            mkApp' uu____2286 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2316  ->
      fun r  ->
        match uu____2316 with
        | (t1,t2) ->
            let uu____2324 =
              let uu____2331 =
                let uu____2334 =
                  let uu____2337 = mkNatToBv sz t2 r in [uu____2337] in
                t1 :: uu____2334 in
              (BvMod, uu____2331) in
            mkApp' uu____2324 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2354  ->
      fun r  ->
        match uu____2354 with
        | (t1,t2) ->
            let uu____2362 =
              let uu____2369 =
                let uu____2372 =
                  let uu____2375 = mkNatToBv sz t2 r in [uu____2375] in
                t1 :: uu____2372 in
              (BvMul, uu____2369) in
            mkApp' uu____2362 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2408  ->
    fun r  ->
      match uu____2408 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2424 -> mk_bin_op Eq (t1, t2) r)
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
  fun uu____2531  ->
    fun r  ->
      match uu____2531 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2542) -> t2
           | App (FalseOp ,uu____2547) -> t3
           | uu____2552 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2553),App (TrueOp ,uu____2554)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2563),uu____2564) ->
                    let uu____2569 =
                      let uu____2574 = mkNot t1 t1.rng in (uu____2574, t3) in
                    mkImp uu____2569 r
                | (uu____2575,App (TrueOp ,uu____2576)) -> mkImp (t1, t2) r
                | (uu____2581,uu____2582) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____2629  ->
    fun r  ->
      match uu____2629 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2671) -> body
             | uu____2676 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2697  ->
    fun r  ->
      match uu____2697 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2733 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2733 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2752 = FStar_ST.read t1.freevars in
        match uu____2752 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2779 ->
            (match t1.tm with
             | Integer uu____2788 -> t1
             | BoundV uu____2789 -> t1
             | FreeV x ->
                 let uu____2795 = index_of x in
                 (match uu____2795 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2805 =
                   let uu____2812 = FStar_List.map (aux ix) tms in
                   (op, uu____2812) in
                 mkApp' uu____2805 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2820 =
                   let uu____2821 =
                     let uu____2828 = aux ix t2 in (uu____2828, r1, r2) in
                   Labeled uu____2821 in
                 mk uu____2820 t2.rng
             | LblPos (t2,r) ->
                 let uu____2831 =
                   let uu____2832 =
                     let uu____2837 = aux ix t2 in (uu____2837, r) in
                   LblPos uu____2832 in
                 mk uu____2831 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2860 =
                   let uu____2879 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2900 = aux (ix + n1) body in
                   (qop, uu____2879, wopt, vars, uu____2900) in
                 mkQuant uu____2860 t1.rng
             | Let (es,body) ->
                 let uu____2919 =
                   FStar_List.fold_left
                     (fun uu____2937  ->
                        fun e  ->
                          match uu____2937 with
                          | (ix1,l) ->
                              let uu____2957 =
                                let uu____2960 = aux ix1 e in uu____2960 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____2957))
                     (ix, []) es in
                 (match uu____2919 with
                  | (ix1,es_rev) ->
                      let uu____2971 =
                        let uu____2978 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____2978) in
                      mkLet uu____2971 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3004 -> t1
        | FreeV uu____3005 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3022 =
              let uu____3029 = FStar_List.map (aux shift) tms2 in
              (op, uu____3029) in
            mkApp' uu____3022 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3037 =
              let uu____3038 =
                let uu____3045 = aux shift t2 in (uu____3045, r1, r2) in
              Labeled uu____3038 in
            mk uu____3037 t2.rng
        | LblPos (t2,r) ->
            let uu____3048 =
              let uu____3049 =
                let uu____3054 = aux shift t2 in (uu____3054, r) in
              LblPos uu____3049 in
            mk uu____3048 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____3082 =
              let uu____3101 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____3118 = aux shift1 body in
              (qop, uu____3101, wopt, vars, uu____3118) in
            mkQuant uu____3082 t1.rng
        | Let (es,body) ->
            let uu____3133 =
              FStar_List.fold_left
                (fun uu____3151  ->
                   fun e  ->
                     match uu____3151 with
                     | (ix,es1) ->
                         let uu____3171 =
                           let uu____3174 = aux shift e in uu____3174 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____3171))
                (shift, []) es in
            (match uu____3133 with
             | (shift1,es_rev) ->
                 let uu____3185 =
                   let uu____3192 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____3192) in
                 mkLet uu____3185 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____3207 = abstr [fv] t in inst [s] uu____3207
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3231  ->
    match uu____3231 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3273 =
          let uu____3292 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____3309 = FStar_List.map fv_sort vars in
          let uu____3316 = abstr vars body in
          (qop, uu____3292, wopt, uu____3309, uu____3316) in
        mkQuant uu____3273
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3347  ->
    fun r  ->
      match uu____3347 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3413  ->
    fun r  ->
      match uu____3413 with
      | (pats,wopt,vars,body) ->
          let uu____3445 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____3445 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3470  ->
    fun r  ->
      match uu____3470 with
      | (pats,vars,body) ->
          let uu____3493 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3493 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3518  ->
    fun r  ->
      match uu____3518 with
      | (pats,vars,body) ->
          let uu____3541 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3541 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3566  ->
    fun r  ->
      match uu____3566 with
      | (bindings,body) ->
          let uu____3592 = FStar_List.split bindings in
          (match uu____3592 with
           | (vars,es) ->
               let uu____3611 =
                 let uu____3618 = abstr vars body in (es, uu____3618) in
               mkLet uu____3611 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3640  ->
    match uu____3640 with
    | (nm,vars,s,tm,c) ->
        let uu____3674 =
          let uu____3687 = FStar_List.map fv_sort vars in
          let uu____3694 = abstr vars tm in
          (nm, uu____3687, s, uu____3694, c) in
        DefineFun uu____3674
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3701 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3701
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3712  ->
    fun id  ->
      match uu____3712 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3722 =
              let uu____3723 =
                let uu____3728 = mkInteger' id norng in
                let uu____3729 =
                  let uu____3730 =
                    let uu____3737 = constr_id_of_sort sort in
                    let uu____3738 =
                      let uu____3741 = mkApp (tok_name, []) norng in
                      [uu____3741] in
                    (uu____3737, uu____3738) in
                  mkApp uu____3730 norng in
                (uu____3728, uu____3729) in
              mkEq uu____3723 norng in
            {
              assumption_term = uu____3722;
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
  fun uu____3759  ->
    match uu____3759 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3791 =
                      let uu____3796 =
                        let uu____3797 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____3797 in
                      (uu____3796, s) in
                    mkFreeV uu____3791 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____3805 =
            let uu____3812 = constr_id_of_sort sort in (uu____3812, [capp]) in
          mkApp uu____3805 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____3817 =
            let uu____3818 =
              let uu____3829 =
                let uu____3830 =
                  let uu____3835 = mkInteger id1 norng in
                  (uu____3835, cid_app) in
                mkEq uu____3830 norng in
              ([[capp]], bvar_names, uu____3829) in
            mkForall uu____3818 norng in
          {
            assumption_term = uu____3817;
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
  fun uu____3857  ->
    match uu____3857 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____3878 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____3878 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____3898 = let uu____3903 = bvar_name i in (uu____3903, s) in
          mkFreeV uu____3898 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3924  ->
                    match uu____3924 with
                    | (uu____3931,s,uu____3933) ->
                        let uu____3934 = bvar i s in uu____3934 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____3943 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3971  ->
                    match uu____3971 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____3994 =
                              let uu____3995 =
                                let uu____4006 =
                                  let uu____4007 =
                                    let uu____4012 =
                                      let uu____4013 = bvar i s in
                                      uu____4013 norng in
                                    (cproj_app, uu____4012) in
                                  mkEq uu____4007 norng in
                                ([[capp]], bvar_names, uu____4006) in
                              mkForall uu____3995 norng in
                            {
                              assumption_term = uu____3994;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____3943 FStar_List.flatten
let constructor_to_decl: constructor_t -> decls_t =
  fun uu____4036  ->
    match uu____4036 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4064  ->
                  match uu____4064 with
                  | (uu____4071,sort1,uu____4073) -> sort1)) in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____4091 =
              let uu____4096 =
                let uu____4097 =
                  let uu____4104 = constr_id_of_sort sort in
                  (uu____4104, [xx]) in
                mkApp uu____4097 norng in
              let uu____4107 =
                let uu____4108 = FStar_Util.string_of_int id in
                mkInteger uu____4108 norng in
              (uu____4096, uu____4107) in
            mkEq uu____4091 norng in
          let uu____4109 =
            let uu____4124 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4174  ->
                        match uu____4174 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4204 = mkApp (proj, [xx]) norng in
                              (uu____4204, [])
                            else
                              (let fi =
                                 let uu____4223 =
                                   let uu____4224 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____4224 in
                                 (uu____4223, s) in
                               let uu____4225 = mkFreeV fi norng in
                               (uu____4225, [fi])))) in
            FStar_All.pipe_right uu____4124 FStar_List.split in
          match uu____4109 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____4306 =
                  let uu____4311 = mkApp (name, proj_terms) norng in
                  (xx, uu____4311) in
                mkEq uu____4306 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4319 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____4360 =
          let uu____4363 =
            let uu____4364 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____4364 in
          uu____4363 :: cdecl :: cid :: projs in
        let uu____4365 =
          let uu____4368 =
            let uu____4371 =
              let uu____4372 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____4372 in
            [uu____4371] in
          FStar_List.append [disc] uu____4368 in
        FStar_List.append uu____4360 uu____4365
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
    let uu____4623 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____4623 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
let termToSmt: Prims.string -> term -> Prims.string =
  fun enclosing_name  ->
    fun t  ->
      let next_qid =
        let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
        fun depth  ->
          let n1 = FStar_ST.read ctr in
          FStar_Util.incr ctr;
          if n1 = (Prims.parse_int "0")
          then enclosing_name
          else
            (let uu____4708 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____4708) in
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
                             "Prims.guard_free",{ tm = BoundV uu____4750;
                                                  freevars = uu____4751;
                                                  rng = uu____4752;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____4766 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____4806 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____4806 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____4821 = op_to_string op in
            let uu____4822 =
              let uu____4823 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____4823 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" uu____4821 uu____4822
        | Labeled (t2,uu____4829,uu____4830) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____4833 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____4833 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____4856 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts in
            (match uu____4856 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____4905 ->
                       let uu____4910 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____4926 =
                                   let uu____4927 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____4933 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____4933)
                                       pats2 in
                                   FStar_String.concat " " uu____4927 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____4926)) in
                       FStar_All.pipe_right uu____4910
                         (FStar_String.concat "\n") in
                 let uu____4936 =
                   let uu____4939 =
                     let uu____4942 =
                       let uu____4945 = aux1 n2 names2 body in
                       let uu____4946 =
                         let uu____4949 = weightToSmt wopt in
                         [uu____4949; pats_str; qid] in
                       uu____4945 :: uu____4946 in
                     binders1 :: uu____4942 in
                   (qop_to_string qop) :: uu____4939 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____4936)
        | Let (es,body) ->
            let uu____4956 =
              FStar_List.fold_left
                (fun uu____4993  ->
                   fun e  ->
                     match uu____4993 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____5043 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____5043 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____5056 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____5056 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____4956 with
             | (names2,binders,n2) ->
                 let uu____5088 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____5088)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____5096 = FStar_Range.string_of_range t1.rng in
          let uu____5097 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5096
            uu____5097 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_5104  ->
    match uu___92_5104 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5108 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5123 -> (hd1, "...") in
        (match uu____5108 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____5141 = FStar_Options.log_queries () in
          if uu____5141
          then
            let uu____5142 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_5146  ->
                   match uu___93_5146 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____5142
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____5165 = caption_to_string c in
          let uu____5166 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5165 f
            (FStar_String.concat " " l) uu____5166
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____5176 = name_macro_binders arg_sorts in
          (match uu____5176 with
           | (names1,binders) ->
               let body1 =
                 let uu____5208 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____5208 body in
               let uu____5221 = caption_to_string c in
               let uu____5222 = strSort retsort in
               let uu____5223 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5221
                 f (FStar_String.concat " " binders) uu____5222 uu____5223)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_5241  ->
                    match uu___94_5241 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____5246 = FStar_Options.log_queries () in
            if uu____5246
            then
              let uu____5247 =
                let uu____5248 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____5248 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5247
            else "" in
          let n1 = escape a.assumption_name in
          let uu____5253 = caption_to_string a.assumption_caption in
          let uu____5254 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5253 fids
            uu____5254 n1
      | Eval t ->
          let uu____5256 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____5256
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____5258 -> ""
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
      | GetStatistics  ->
          "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
      | GetReasonUnknown  ->
          "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
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
      let uu____5583 =
        let uu____5586 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____5586
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____5583 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____5602 =
      let uu____5621 =
        let uu____5622 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5622 in
      let uu____5627 =
        let uu____5636 =
          let uu____5643 =
            let uu____5644 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____5644 in
          (uu____5643, (BitVec_sort sz), true) in
        [uu____5636] in
      (uu____5621, uu____5627, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____5602 constructor_to_decl
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____5713 =
        let uu____5720 = let uu____5723 = mkInteger' i norng in [uu____5723] in
        ("Tm_uvar", uu____5720) in
      mkApp uu____5713 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____5748 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____5763 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____5763 u v1 t
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
      let uu____5796 =
        let uu____5797 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5797 in
      let uu____5802 =
        let uu____5803 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____5803 in
      elim_box true uu____5796 uu____5802 t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____5816 =
        let uu____5817 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____5817 in
      let uu____5822 =
        let uu____5823 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5823 in
      elim_box true uu____5816 uu____5822 t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____5837 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____5847 -> raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____5863 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____5863
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____5875 = op_to_string op in
        let uu____5876 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____5875 uu____5876
    | Labeled (t1,r1,r2) ->
        let uu____5880 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____5880
    | LblPos (t1,s) ->
        let uu____5883 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____5883
    | Quant (qop,l,uu____5886,uu____5887,t1) ->
        let uu____5905 = print_smt_term_list_list l in
        let uu____5906 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____5905
          uu____5906
    | Let (es,body) ->
        let uu____5913 = print_smt_term_list es in
        let uu____5914 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____5913 uu____5914
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____5918 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____5918 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____5937 =
             let uu____5938 =
               let uu____5939 = print_smt_term_list l1 in
               Prims.strcat uu____5939 " ] " in
             Prims.strcat "; [ " uu____5938 in
           Prims.strcat s uu____5937) "" l
let getBoxedInteger: term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____5955 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____5955
         | uu____5956 -> FStar_Pervasives_Native.None)
    | uu____5957 -> FStar_Pervasives_Native.None
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____5968::t1::t2::[]);
                       freevars = uu____5971; rng = uu____5972;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____5985::t1::t2::[]);
                       freevars = uu____5988; rng = uu____5989;_}::[])
        -> let uu____6002 = mkEq (t1, t2) norng in mkNot uu____6002 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6005; rng = uu____6006;_}::[])
        ->
        let uu____6019 =
          let uu____6024 = unboxInt t1 in
          let uu____6025 = unboxInt t2 in (uu____6024, uu____6025) in
        mkLTE uu____6019 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6028; rng = uu____6029;_}::[])
        ->
        let uu____6042 =
          let uu____6047 = unboxInt t1 in
          let uu____6048 = unboxInt t2 in (uu____6047, uu____6048) in
        mkLT uu____6042 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6051; rng = uu____6052;_}::[])
        ->
        let uu____6065 =
          let uu____6070 = unboxInt t1 in
          let uu____6071 = unboxInt t2 in (uu____6070, uu____6071) in
        mkGTE uu____6065 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6074; rng = uu____6075;_}::[])
        ->
        let uu____6088 =
          let uu____6093 = unboxInt t1 in
          let uu____6094 = unboxInt t2 in (uu____6093, uu____6094) in
        mkGT uu____6088 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6097; rng = uu____6098;_}::[])
        ->
        let uu____6111 =
          let uu____6116 = unboxBool t1 in
          let uu____6117 = unboxBool t2 in (uu____6116, uu____6117) in
        mkAnd uu____6111 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6120; rng = uu____6121;_}::[])
        ->
        let uu____6134 =
          let uu____6139 = unboxBool t1 in
          let uu____6140 = unboxBool t2 in (uu____6139, uu____6140) in
        mkOr uu____6134 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6142; rng = uu____6143;_}::[])
        -> let uu____6156 = unboxBool t1 in mkNot uu____6156 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6160; rng = uu____6161;_}::[])
        when
        let uu____6174 = getBoxedInteger t0 in FStar_Util.is_some uu____6174
        ->
        let sz =
          let uu____6178 = getBoxedInteger t0 in
          match uu____6178 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6182 -> failwith "impossible" in
        let uu____6185 =
          let uu____6190 = unboxBitVec sz t1 in
          let uu____6191 = unboxBitVec sz t2 in (uu____6190, uu____6191) in
        mkBvUlt uu____6185 t.rng
    | App
        (Var
         "Prims.equals",uu____6192::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6196;
                                      rng = uu____6197;_}::uu____6198::[])
        when
        let uu____6211 = getBoxedInteger t0 in FStar_Util.is_some uu____6211
        ->
        let sz =
          let uu____6215 = getBoxedInteger t0 in
          match uu____6215 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6219 -> failwith "impossible" in
        let uu____6222 =
          let uu____6227 = unboxBitVec sz t1 in
          let uu____6228 = unboxBitVec sz t2 in (uu____6227, uu____6228) in
        mkBvUlt uu____6222 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_6232 = unboxBool t1 in
        {
          tm = (uu___95_6232.tm);
          freevars = (uu___95_6232.freevars);
          rng = (t.rng)
        }
    | uu____6233 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6274 = FStar_Options.unthrottle_inductives () in
        if uu____6274
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
      let uu____6365 =
        let uu____6372 = let uu____6375 = mkInteger' i norng in [uu____6375] in
        ("FString_const", uu____6372) in
      mkApp uu____6365 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6390 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____6390 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6414 =
         let uu____6421 =
           let uu____6424 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____6424] in
         ("SFuel", uu____6421) in
       mkApp uu____6414 norng)
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
            let uu____6461 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____6461
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
      let uu____6518 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6518
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6535 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6535
let mk_haseq: term -> term =
  fun t  ->
    let uu____6544 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____6544