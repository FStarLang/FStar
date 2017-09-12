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
    match projectee with | Integer _0 -> true | uu____476 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____490 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____508 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____540 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____590 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____664 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____702 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____738 -> false
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
    match projectee with | Name _0 -> true | uu____896 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____910 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____924 -> false
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
    match projectee with | DefPrelude  -> true | uu____1059 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1075 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1131 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1181 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1195 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1209 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1223 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1239 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1258 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1263 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1268 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1273 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1283 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1308 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1313 -> false
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort:
  'Auu____1338 'Auu____1339 .
    ('Auu____1339,'Auu____1338) FStar_Pervasives_Native.tuple2 ->
      'Auu____1338
  = fun x  -> FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1370 -> false
let freevar_sort: term -> sort =
  fun uu___86_1378  ->
    match uu___86_1378 with
    | { tm = FreeV x; freevars = uu____1380; rng = uu____1381;_} -> fv_sort x
    | uu____1394 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___87_1398  ->
    match uu___87_1398 with
    | { tm = FreeV fv; freevars = uu____1400; rng = uu____1401;_} -> fv
    | uu____1414 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1431 -> []
    | BoundV uu____1436 -> []
    | FreeV fv -> [fv]
    | App (uu____1454,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1464,uu____1465,uu____1466,uu____1467,t1) -> freevars t1
    | Labeled (t1,uu____1486,uu____1487) -> freevars t1
    | LblPos (t1,uu____1489) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1504 = FStar_ST.op_Bang t.freevars in
    match uu____1504 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1577 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1577 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___88_1628  ->
    match uu___88_1628 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___89_1632  ->
    match uu___89_1632 with
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
        let uu____1634 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1634
    | NatToBv n1 ->
        let uu____1636 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1636
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___90_1643  ->
    match uu___90_1643 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1647 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1647
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1655 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1655
    | FreeV x ->
        let uu____1661 =
          let uu____1662 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1662 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1661
    | App (op,tms) ->
        let uu____1669 =
          let uu____1670 = op_to_string op in
          let uu____1671 =
            let uu____1672 =
              let uu____1673 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1673 (FStar_String.concat " ") in
            Prims.strcat uu____1672 ")" in
          Prims.strcat uu____1670 uu____1671 in
        Prims.strcat "(" uu____1669
    | Labeled (t1,r1,r2) ->
        let uu____1681 = hash_of_term t1 in
        let uu____1682 =
          let uu____1683 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1683 in
        Prims.strcat uu____1681 uu____1682
    | LblPos (t1,r) ->
        let uu____1686 =
          let uu____1687 = hash_of_term t1 in
          Prims.strcat uu____1687
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1686
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1709 =
          let uu____1710 =
            let uu____1711 =
              let uu____1712 =
                let uu____1713 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1713 (FStar_String.concat " ") in
              let uu____1718 =
                let uu____1719 =
                  let uu____1720 = hash_of_term body in
                  let uu____1721 =
                    let uu____1722 =
                      let uu____1723 = weightToSmt wopt in
                      let uu____1724 =
                        let uu____1725 =
                          let uu____1726 =
                            let uu____1727 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1743 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1743
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1727
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1726 "))" in
                        Prims.strcat " " uu____1725 in
                      Prims.strcat uu____1723 uu____1724 in
                    Prims.strcat " " uu____1722 in
                  Prims.strcat uu____1720 uu____1721 in
                Prims.strcat ")(! " uu____1719 in
              Prims.strcat uu____1712 uu____1718 in
            Prims.strcat " (" uu____1711 in
          Prims.strcat (qop_to_string qop) uu____1710 in
        Prims.strcat "(" uu____1709
    | Let (es,body) ->
        let uu____1756 =
          let uu____1757 =
            let uu____1758 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1758 (FStar_String.concat " ") in
          let uu____1763 =
            let uu____1764 =
              let uu____1765 = hash_of_term body in
              Prims.strcat uu____1765 ")" in
            Prims.strcat ") " uu____1764 in
          Prims.strcat uu____1757 uu____1763 in
        Prims.strcat "(let (" uu____1756
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
    let uu____1795 =
      let uu____1796 = FStar_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu____1796 in
    mkBoxFunctions uu____1795
let isInjective: Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1803 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3") in
       uu____1803 = "Box") &&
        (let uu____1805 =
           let uu____1806 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c  -> c = 46) uu____1806 in
         Prims.op_Negation uu____1805)
    else false
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1820 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1820; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1877 =
        let uu____1878 = FStar_Util.ensure_decimal i in Integer uu____1878 in
      mk uu____1877 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1887 = FStar_Util.string_of_int i in mkInteger uu____1887 r
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
  fun uu____1944  ->
    fun r  -> match uu____1944 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1968) -> mkFalse r
      | App (FalseOp ,uu____1973) -> mkTrue r
      | uu____1978 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1991  ->
    fun r  ->
      match uu____1991 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1999),uu____2000) -> t2
           | (uu____2005,App (TrueOp ,uu____2006)) -> t1
           | (App (FalseOp ,uu____2011),uu____2012) -> mkFalse r
           | (uu____2017,App (FalseOp ,uu____2018)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2035,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2044) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2051 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2068  ->
    fun r  ->
      match uu____2068 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2076),uu____2077) -> mkTrue r
           | (uu____2082,App (TrueOp ,uu____2083)) -> mkTrue r
           | (App (FalseOp ,uu____2088),uu____2089) -> t2
           | (uu____2094,App (FalseOp ,uu____2095)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2112,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2121) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2128 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2145  ->
    fun r  ->
      match uu____2145 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2153,App (TrueOp ,uu____2154)) -> mkTrue r
           | (App (FalseOp ,uu____2159),uu____2160) -> mkTrue r
           | (App (TrueOp ,uu____2165),uu____2166) -> t2
           | (uu____2171,App (Imp ,t1'::t2'::[])) ->
               let uu____2176 =
                 let uu____2183 =
                   let uu____2186 = mkAnd (t1, t1') r in [uu____2186; t2'] in
                 (Imp, uu____2183) in
               mkApp' uu____2176 r
           | uu____2189 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2210  ->
      fun r  -> match uu____2210 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
    fun uu____2312  ->
      fun r  ->
        match uu____2312 with
        | (t1,t2) ->
            let uu____2320 =
              let uu____2327 =
                let uu____2330 =
                  let uu____2333 = mkNatToBv sz t2 r in [uu____2333] in
                t1 :: uu____2330 in
              (BvShl, uu____2327) in
            mkApp' uu____2320 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2350  ->
      fun r  ->
        match uu____2350 with
        | (t1,t2) ->
            let uu____2358 =
              let uu____2365 =
                let uu____2368 =
                  let uu____2371 = mkNatToBv sz t2 r in [uu____2371] in
                t1 :: uu____2368 in
              (BvShr, uu____2365) in
            mkApp' uu____2358 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2388  ->
      fun r  ->
        match uu____2388 with
        | (t1,t2) ->
            let uu____2396 =
              let uu____2403 =
                let uu____2406 =
                  let uu____2409 = mkNatToBv sz t2 r in [uu____2409] in
                t1 :: uu____2406 in
              (BvUdiv, uu____2403) in
            mkApp' uu____2396 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2426  ->
      fun r  ->
        match uu____2426 with
        | (t1,t2) ->
            let uu____2434 =
              let uu____2441 =
                let uu____2444 =
                  let uu____2447 = mkNatToBv sz t2 r in [uu____2447] in
                t1 :: uu____2444 in
              (BvMod, uu____2441) in
            mkApp' uu____2434 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2464  ->
      fun r  ->
        match uu____2464 with
        | (t1,t2) ->
            let uu____2472 =
              let uu____2479 =
                let uu____2482 =
                  let uu____2485 = mkNatToBv sz t2 r in [uu____2485] in
                t1 :: uu____2482 in
              (BvMul, uu____2479) in
            mkApp' uu____2472 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2518  ->
    fun r  ->
      match uu____2518 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2534 -> mk_bin_op Eq (t1, t2) r)
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
  fun uu____2641  ->
    fun r  ->
      match uu____2641 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2652) -> t2
           | App (FalseOp ,uu____2657) -> t3
           | uu____2662 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2663),App (TrueOp ,uu____2664)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2673),uu____2674) ->
                    let uu____2679 =
                      let uu____2684 = mkNot t1 t1.rng in (uu____2684, t3) in
                    mkImp uu____2679 r
                | (uu____2685,App (TrueOp ,uu____2686)) -> mkImp (t1, t2) r
                | (uu____2691,uu____2692) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____2739  ->
    fun r  ->
      match uu____2739 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2781) -> body
             | uu____2786 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2807  ->
    fun r  ->
      match uu____2807 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2843 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2843 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2862 = FStar_ST.op_Bang t1.freevars in
        match uu____2862 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2923 ->
            (match t1.tm with
             | Integer uu____2932 -> t1
             | BoundV uu____2933 -> t1
             | FreeV x ->
                 let uu____2939 = index_of x in
                 (match uu____2939 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2949 =
                   let uu____2956 = FStar_List.map (aux ix) tms in
                   (op, uu____2956) in
                 mkApp' uu____2949 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2964 =
                   let uu____2965 =
                     let uu____2972 = aux ix t2 in (uu____2972, r1, r2) in
                   Labeled uu____2965 in
                 mk uu____2964 t2.rng
             | LblPos (t2,r) ->
                 let uu____2975 =
                   let uu____2976 =
                     let uu____2981 = aux ix t2 in (uu____2981, r) in
                   LblPos uu____2976 in
                 mk uu____2975 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____3004 =
                   let uu____3023 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____3044 = aux (ix + n1) body in
                   (qop, uu____3023, wopt, vars, uu____3044) in
                 mkQuant uu____3004 t1.rng
             | Let (es,body) ->
                 let uu____3063 =
                   FStar_List.fold_left
                     (fun uu____3081  ->
                        fun e  ->
                          match uu____3081 with
                          | (ix1,l) ->
                              let uu____3101 =
                                let uu____3104 = aux ix1 e in uu____3104 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____3101))
                     (ix, []) es in
                 (match uu____3063 with
                  | (ix1,es_rev) ->
                      let uu____3115 =
                        let uu____3122 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____3122) in
                      mkLet uu____3115 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3148 -> t1
        | FreeV uu____3149 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3166 =
              let uu____3173 = FStar_List.map (aux shift) tms2 in
              (op, uu____3173) in
            mkApp' uu____3166 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3181 =
              let uu____3182 =
                let uu____3189 = aux shift t2 in (uu____3189, r1, r2) in
              Labeled uu____3182 in
            mk uu____3181 t2.rng
        | LblPos (t2,r) ->
            let uu____3192 =
              let uu____3193 =
                let uu____3198 = aux shift t2 in (uu____3198, r) in
              LblPos uu____3193 in
            mk uu____3192 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____3226 =
              let uu____3245 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____3262 = aux shift1 body in
              (qop, uu____3245, wopt, vars, uu____3262) in
            mkQuant uu____3226 t1.rng
        | Let (es,body) ->
            let uu____3277 =
              FStar_List.fold_left
                (fun uu____3295  ->
                   fun e  ->
                     match uu____3295 with
                     | (ix,es1) ->
                         let uu____3315 =
                           let uu____3318 = aux shift e in uu____3318 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____3315))
                (shift, []) es in
            (match uu____3277 with
             | (shift1,es_rev) ->
                 let uu____3329 =
                   let uu____3336 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____3336) in
                 mkLet uu____3329 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____3351 = abstr [fv] t in inst [s] uu____3351
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3375  ->
    match uu____3375 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3417 =
          let uu____3436 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____3453 = FStar_List.map fv_sort vars in
          let uu____3460 = abstr vars body in
          (qop, uu____3436, wopt, uu____3453, uu____3460) in
        mkQuant uu____3417
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3491  ->
    fun r  ->
      match uu____3491 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3557  ->
    fun r  ->
      match uu____3557 with
      | (pats,wopt,vars,body) ->
          let uu____3589 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____3589 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3614  ->
    fun r  ->
      match uu____3614 with
      | (pats,vars,body) ->
          let uu____3637 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3637 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3662  ->
    fun r  ->
      match uu____3662 with
      | (pats,vars,body) ->
          let uu____3685 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3685 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3710  ->
    fun r  ->
      match uu____3710 with
      | (bindings,body) ->
          let uu____3736 = FStar_List.split bindings in
          (match uu____3736 with
           | (vars,es) ->
               let uu____3755 =
                 let uu____3762 = abstr vars body in (es, uu____3762) in
               mkLet uu____3755 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3784  ->
    match uu____3784 with
    | (nm,vars,s,tm,c) ->
        let uu____3818 =
          let uu____3831 = FStar_List.map fv_sort vars in
          let uu____3838 = abstr vars tm in
          (nm, uu____3831, s, uu____3838, c) in
        DefineFun uu____3818
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3845 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3845
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3856  ->
    fun id  ->
      match uu____3856 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3866 =
              let uu____3867 =
                let uu____3872 = mkInteger' id norng in
                let uu____3873 =
                  let uu____3874 =
                    let uu____3881 = constr_id_of_sort sort in
                    let uu____3882 =
                      let uu____3885 = mkApp (tok_name, []) norng in
                      [uu____3885] in
                    (uu____3881, uu____3882) in
                  mkApp uu____3874 norng in
                (uu____3872, uu____3873) in
              mkEq uu____3867 norng in
            {
              assumption_term = uu____3866;
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
  fun uu____3903  ->
    match uu____3903 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3935 =
                      let uu____3940 =
                        let uu____3941 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____3941 in
                      (uu____3940, s) in
                    mkFreeV uu____3935 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____3949 =
            let uu____3956 = constr_id_of_sort sort in (uu____3956, [capp]) in
          mkApp uu____3949 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____3961 =
            let uu____3962 =
              let uu____3973 =
                let uu____3974 =
                  let uu____3979 = mkInteger id1 norng in
                  (uu____3979, cid_app) in
                mkEq uu____3974 norng in
              ([[capp]], bvar_names, uu____3973) in
            mkForall uu____3962 norng in
          {
            assumption_term = uu____3961;
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
  fun uu____4001  ->
    match uu____4001 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____4022 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____4022 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____4042 = let uu____4047 = bvar_name i in (uu____4047, s) in
          mkFreeV uu____4042 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4068  ->
                    match uu____4068 with
                    | (uu____4075,s,uu____4077) ->
                        let uu____4078 = bvar i s in uu____4078 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____4087 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4115  ->
                    match uu____4115 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____4138 =
                              let uu____4139 =
                                let uu____4150 =
                                  let uu____4151 =
                                    let uu____4156 =
                                      let uu____4157 = bvar i s in
                                      uu____4157 norng in
                                    (cproj_app, uu____4156) in
                                  mkEq uu____4151 norng in
                                ([[capp]], bvar_names, uu____4150) in
                              mkForall uu____4139 norng in
                            {
                              assumption_term = uu____4138;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____4087 FStar_List.flatten
let constructor_to_decl: constructor_t -> decls_t =
  fun uu____4180  ->
    match uu____4180 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4208  ->
                  match uu____4208 with
                  | (uu____4215,sort1,uu____4217) -> sort1)) in
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
            let uu____4235 =
              let uu____4240 =
                let uu____4241 =
                  let uu____4248 = constr_id_of_sort sort in
                  (uu____4248, [xx]) in
                mkApp uu____4241 norng in
              let uu____4251 =
                let uu____4252 = FStar_Util.string_of_int id in
                mkInteger uu____4252 norng in
              (uu____4240, uu____4251) in
            mkEq uu____4235 norng in
          let uu____4253 =
            let uu____4268 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4318  ->
                        match uu____4318 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4348 = mkApp (proj, [xx]) norng in
                              (uu____4348, [])
                            else
                              (let fi =
                                 let uu____4367 =
                                   let uu____4368 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____4368 in
                                 (uu____4367, s) in
                               let uu____4369 = mkFreeV fi norng in
                               (uu____4369, [fi])))) in
            FStar_All.pipe_right uu____4268 FStar_List.split in
          match uu____4253 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____4450 =
                  let uu____4455 = mkApp (name, proj_terms) norng in
                  (xx, uu____4455) in
                mkEq uu____4450 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4463 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____4504 =
          let uu____4507 =
            let uu____4508 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____4508 in
          uu____4507 :: cdecl :: cid :: projs in
        let uu____4509 =
          let uu____4512 =
            let uu____4515 =
              let uu____4516 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____4516 in
            [uu____4515] in
          FStar_List.append [disc] uu____4512 in
        FStar_List.append uu____4504 uu____4509
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
          let uu____4567 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4622  ->
                    fun s  ->
                      match uu____4622 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4672 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____4676 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____4676 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____4689 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____4689 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____4567 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4767 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____4767 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
let termToSmt: Prims.string -> term -> Prims.string =
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
            (let uu____4892 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____4892) in
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
                             "Prims.guard_free",{ tm = BoundV uu____4934;
                                                  freevars = uu____4935;
                                                  rng = uu____4936;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____4950 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____4990 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____4990 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____5005 = op_to_string op in
            let uu____5006 =
              let uu____5007 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____5007 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" uu____5005 uu____5006
        | Labeled (t2,uu____5013,uu____5014) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____5017 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____5017 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____5040 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts in
            (match uu____5040 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____5089 ->
                       let uu____5094 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____5110 =
                                   let uu____5111 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____5117 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____5117)
                                       pats2 in
                                   FStar_String.concat " " uu____5111 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____5110)) in
                       FStar_All.pipe_right uu____5094
                         (FStar_String.concat "\n") in
                 let uu____5120 =
                   let uu____5123 =
                     let uu____5126 =
                       let uu____5129 = aux1 n2 names2 body in
                       let uu____5130 =
                         let uu____5133 = weightToSmt wopt in
                         [uu____5133; pats_str; qid] in
                       uu____5129 :: uu____5130 in
                     binders1 :: uu____5126 in
                   (qop_to_string qop) :: uu____5123 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____5120)
        | Let (es,body) ->
            let uu____5140 =
              FStar_List.fold_left
                (fun uu____5177  ->
                   fun e  ->
                     match uu____5177 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____5227 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____5227 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____5240 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____5240 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____5140 with
             | (names2,binders,n2) ->
                 let uu____5272 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____5272)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____5280 = FStar_Range.string_of_range t1.rng in
          let uu____5281 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5280
            uu____5281 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_5288  ->
    match uu___91_5288 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5292 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5307 -> (hd1, "...") in
        (match uu____5292 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s 39 95 in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____5325 = FStar_Options.log_queries () in
          if uu____5325
          then
            let uu____5326 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___92_5330  ->
                   match uu___92_5330 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____5326
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____5349 = caption_to_string c in
          let uu____5350 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5349 f
            (FStar_String.concat " " l) uu____5350
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____5360 = name_macro_binders arg_sorts in
          (match uu____5360 with
           | (names1,binders) ->
               let body1 =
                 let uu____5392 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____5392 body in
               let uu____5405 = caption_to_string c in
               let uu____5406 = strSort retsort in
               let uu____5407 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5405
                 f (FStar_String.concat " " binders) uu____5406 uu____5407)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___93_5425  ->
                    match uu___93_5425 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____5430 = FStar_Options.log_queries () in
            if uu____5430
            then
              let uu____5431 =
                let uu____5432 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____5432 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5431
            else "" in
          let n1 = escape a.assumption_name in
          let uu____5437 = caption_to_string a.assumption_caption in
          let uu____5438 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5437 fids
            uu____5438 n1
      | Eval t ->
          let uu____5440 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____5440
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____5442 -> ""
      | CheckSat  -> "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
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
      let uu____5767 =
        let uu____5770 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____5770
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____5767 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____5786 =
      let uu____5805 =
        let uu____5806 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5806 in
      let uu____5811 =
        let uu____5820 =
          let uu____5827 =
            let uu____5828 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____5828 in
          (uu____5827, (BitVec_sort sz), true) in
        [uu____5820] in
      (uu____5805, uu____5811, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____5786 constructor_to_decl
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____5897 =
        let uu____5904 = let uu____5907 = mkInteger' i norng in [uu____5907] in
        ("Tm_uvar", uu____5904) in
      mkApp uu____5897 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____5932 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____5947 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____5947 u v1 t
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
      let uu____5980 =
        let uu____5981 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5981 in
      let uu____5986 =
        let uu____5987 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____5987 in
      elim_box true uu____5980 uu____5986 t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6000 =
        let uu____6001 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6001 in
      let uu____6006 =
        let uu____6007 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6007 in
      elim_box true uu____6000 uu____6006 t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6021 -> FStar_Exn.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6031 -> FStar_Exn.raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6047 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____6047
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6059 = op_to_string op in
        let uu____6060 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____6059 uu____6060
    | Labeled (t1,r1,r2) ->
        let uu____6064 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6064
    | LblPos (t1,s) ->
        let uu____6067 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6067
    | Quant (qop,l,uu____6070,uu____6071,t1) ->
        let uu____6089 = print_smt_term_list_list l in
        let uu____6090 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6089
          uu____6090
    | Let (es,body) ->
        let uu____6097 = print_smt_term_list es in
        let uu____6098 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____6097 uu____6098
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____6102 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____6102 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6121 =
             let uu____6122 =
               let uu____6123 = print_smt_term_list l1 in
               Prims.strcat uu____6123 " ] " in
             Prims.strcat "; [ " uu____6122 in
           Prims.strcat s uu____6121) "" l
let getBoxedInteger: term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6139 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____6139
         | uu____6140 -> FStar_Pervasives_Native.None)
    | uu____6141 -> FStar_Pervasives_Native.None
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6152::t1::t2::[]);
                       freevars = uu____6155; rng = uu____6156;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6169::t1::t2::[]);
                       freevars = uu____6172; rng = uu____6173;_}::[])
        -> let uu____6186 = mkEq (t1, t2) norng in mkNot uu____6186 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6189; rng = uu____6190;_}::[])
        ->
        let uu____6203 =
          let uu____6208 = unboxInt t1 in
          let uu____6209 = unboxInt t2 in (uu____6208, uu____6209) in
        mkLTE uu____6203 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6212; rng = uu____6213;_}::[])
        ->
        let uu____6226 =
          let uu____6231 = unboxInt t1 in
          let uu____6232 = unboxInt t2 in (uu____6231, uu____6232) in
        mkLT uu____6226 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6235; rng = uu____6236;_}::[])
        ->
        let uu____6249 =
          let uu____6254 = unboxInt t1 in
          let uu____6255 = unboxInt t2 in (uu____6254, uu____6255) in
        mkGTE uu____6249 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6258; rng = uu____6259;_}::[])
        ->
        let uu____6272 =
          let uu____6277 = unboxInt t1 in
          let uu____6278 = unboxInt t2 in (uu____6277, uu____6278) in
        mkGT uu____6272 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6281; rng = uu____6282;_}::[])
        ->
        let uu____6295 =
          let uu____6300 = unboxBool t1 in
          let uu____6301 = unboxBool t2 in (uu____6300, uu____6301) in
        mkAnd uu____6295 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6304; rng = uu____6305;_}::[])
        ->
        let uu____6318 =
          let uu____6323 = unboxBool t1 in
          let uu____6324 = unboxBool t2 in (uu____6323, uu____6324) in
        mkOr uu____6318 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6326; rng = uu____6327;_}::[])
        -> let uu____6340 = unboxBool t1 in mkNot uu____6340 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6344; rng = uu____6345;_}::[])
        when
        let uu____6358 = getBoxedInteger t0 in FStar_Util.is_some uu____6358
        ->
        let sz =
          let uu____6362 = getBoxedInteger t0 in
          match uu____6362 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6366 -> failwith "impossible" in
        let uu____6369 =
          let uu____6374 = unboxBitVec sz t1 in
          let uu____6375 = unboxBitVec sz t2 in (uu____6374, uu____6375) in
        mkBvUlt uu____6369 t.rng
    | App
        (Var
         "Prims.equals",uu____6376::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6380;
                                      rng = uu____6381;_}::uu____6382::[])
        when
        let uu____6395 = getBoxedInteger t0 in FStar_Util.is_some uu____6395
        ->
        let sz =
          let uu____6399 = getBoxedInteger t0 in
          match uu____6399 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6403 -> failwith "impossible" in
        let uu____6406 =
          let uu____6411 = unboxBitVec sz t1 in
          let uu____6412 = unboxBitVec sz t2 in (uu____6411, uu____6412) in
        mkBvUlt uu____6406 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___94_6416 = unboxBool t1 in
        {
          tm = (uu___94_6416.tm);
          freevars = (uu___94_6416.freevars);
          rng = (t.rng)
        }
    | uu____6417 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6458 = FStar_Options.unthrottle_inductives () in
        if uu____6458
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
      let uu____6549 =
        let uu____6556 = let uu____6559 = mkInteger' i norng in [uu____6559] in
        ("FString_const", uu____6556) in
      mkApp uu____6549 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6574 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____6574 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6598 =
         let uu____6605 =
           let uu____6608 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____6608] in
         ("SFuel", uu____6605) in
       mkApp uu____6598 norng)
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
            let uu____6645 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____6645
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
      let uu____6702 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6702
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6719 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6719
let mk_haseq: term -> term =
  fun t  ->
    let uu____6728 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____6728