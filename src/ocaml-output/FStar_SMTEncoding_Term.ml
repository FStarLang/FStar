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
let uu___is_BvAdd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____274 -> false
let uu___is_BvSub: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____279 -> false
let uu___is_BvShl: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____284 -> false
let uu___is_BvShr: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____289 -> false
let uu___is_BvUdiv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____294 -> false
let uu___is_BvMod: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____299 -> false
let uu___is_BvMul: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____304 -> false
let uu___is_BvUlt: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____309 -> false
let uu___is_BvUext: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____315 -> false
let __proj__BvUext__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0
let uu___is_NatToBv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____329 -> false
let __proj__NatToBv__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
let uu___is_BvToNat: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____342 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____347 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____353 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists[@@deriving show]
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____366 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____371 -> false
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
    match projectee with | Integer _0 -> true | uu____486 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____500 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____518 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____550 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____600 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____674 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____712 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____748 -> false
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
    match projectee with | Name _0 -> true | uu____906 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____920 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____934 -> false
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
    match projectee with | DefPrelude  -> true | uu____1069 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1085 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1141 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1191 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1205 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1219 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1233 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1249 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1268 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1273 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1278 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1283 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1293 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1318 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1323 -> false
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
  'Auu____1348 'Auu____1349 .
    ('Auu____1349,'Auu____1348) FStar_Pervasives_Native.tuple2 ->
      'Auu____1348
  = fun x  -> FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1380 -> false
let freevar_sort: term -> sort =
  fun uu___115_1388  ->
    match uu___115_1388 with
    | { tm = FreeV x; freevars = uu____1390; rng = uu____1391;_} -> fv_sort x
    | uu____1404 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___116_1408  ->
    match uu___116_1408 with
    | { tm = FreeV fv; freevars = uu____1410; rng = uu____1411;_} -> fv
    | uu____1424 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1441 -> []
    | BoundV uu____1446 -> []
    | FreeV fv -> [fv]
    | App (uu____1464,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1474,uu____1475,uu____1476,uu____1477,t1) -> freevars t1
    | Labeled (t1,uu____1496,uu____1497) -> freevars t1
    | LblPos (t1,uu____1499) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1514 = FStar_ST.op_Bang t.freevars in
    match uu____1514 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1607 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1607 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___117_1678  ->
    match uu___117_1678 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___118_1682  ->
    match uu___118_1682 with
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
        let uu____1684 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1684
    | NatToBv n1 ->
        let uu____1686 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1686
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___119_1693  ->
    match uu___119_1693 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1697 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1697
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1705 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1705
    | FreeV x ->
        let uu____1711 =
          let uu____1712 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1712 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1711
    | App (op,tms) ->
        let uu____1719 =
          let uu____1720 = op_to_string op in
          let uu____1721 =
            let uu____1722 =
              let uu____1723 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1723 (FStar_String.concat " ") in
            Prims.strcat uu____1722 ")" in
          Prims.strcat uu____1720 uu____1721 in
        Prims.strcat "(" uu____1719
    | Labeled (t1,r1,r2) ->
        let uu____1731 = hash_of_term t1 in
        let uu____1732 =
          let uu____1733 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1733 in
        Prims.strcat uu____1731 uu____1732
    | LblPos (t1,r) ->
        let uu____1736 =
          let uu____1737 = hash_of_term t1 in
          Prims.strcat uu____1737
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1736
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1759 =
          let uu____1760 =
            let uu____1761 =
              let uu____1762 =
                let uu____1763 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1763 (FStar_String.concat " ") in
              let uu____1768 =
                let uu____1769 =
                  let uu____1770 = hash_of_term body in
                  let uu____1771 =
                    let uu____1772 =
                      let uu____1773 = weightToSmt wopt in
                      let uu____1774 =
                        let uu____1775 =
                          let uu____1776 =
                            let uu____1777 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1793 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1793
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1777
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1776 "))" in
                        Prims.strcat " " uu____1775 in
                      Prims.strcat uu____1773 uu____1774 in
                    Prims.strcat " " uu____1772 in
                  Prims.strcat uu____1770 uu____1771 in
                Prims.strcat ")(! " uu____1769 in
              Prims.strcat uu____1762 uu____1768 in
            Prims.strcat " (" uu____1761 in
          Prims.strcat (qop_to_string qop) uu____1760 in
        Prims.strcat "(" uu____1759
    | Let (es,body) ->
        let uu____1806 =
          let uu____1807 =
            let uu____1808 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1808 (FStar_String.concat " ") in
          let uu____1813 =
            let uu____1814 =
              let uu____1815 = hash_of_term body in
              Prims.strcat uu____1815 ")" in
            Prims.strcat ") " uu____1814 in
          Prims.strcat uu____1807 uu____1813 in
        Prims.strcat "(let (" uu____1806
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
    let uu____1845 =
      let uu____1846 = FStar_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu____1846 in
    mkBoxFunctions uu____1845
let isInjective: Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1853 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3") in
       uu____1853 = "Box") &&
        (let uu____1855 =
           let uu____1856 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c  -> c = 46) uu____1856 in
         Prims.op_Negation uu____1855)
    else false
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1870 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1870; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1927 =
        let uu____1928 = FStar_Util.ensure_decimal i in Integer uu____1928 in
      mk uu____1927 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1937 = FStar_Util.string_of_int i in mkInteger uu____1937 r
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
  fun uu____1994  ->
    fun r  -> match uu____1994 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2018) -> mkFalse r
      | App (FalseOp ,uu____2023) -> mkTrue r
      | uu____2028 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2041  ->
    fun r  ->
      match uu____2041 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2049),uu____2050) -> t2
           | (uu____2055,App (TrueOp ,uu____2056)) -> t1
           | (App (FalseOp ,uu____2061),uu____2062) -> mkFalse r
           | (uu____2067,App (FalseOp ,uu____2068)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2085,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2094) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2101 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2118  ->
    fun r  ->
      match uu____2118 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2126),uu____2127) -> mkTrue r
           | (uu____2132,App (TrueOp ,uu____2133)) -> mkTrue r
           | (App (FalseOp ,uu____2138),uu____2139) -> t2
           | (uu____2144,App (FalseOp ,uu____2145)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2162,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2171) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2178 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2195  ->
    fun r  ->
      match uu____2195 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2203,App (TrueOp ,uu____2204)) -> mkTrue r
           | (App (FalseOp ,uu____2209),uu____2210) -> mkTrue r
           | (App (TrueOp ,uu____2215),uu____2216) -> t2
           | (uu____2221,App (Imp ,t1'::t2'::[])) ->
               let uu____2226 =
                 let uu____2233 =
                   let uu____2236 = mkAnd (t1, t1') r in [uu____2236; t2'] in
                 (Imp, uu____2233) in
               mkApp' uu____2226 r
           | uu____2239 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2260  ->
      fun r  -> match uu____2260 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
    fun uu____2382  ->
      fun r  ->
        match uu____2382 with
        | (t1,t2) ->
            let uu____2390 =
              let uu____2397 =
                let uu____2400 =
                  let uu____2403 = mkNatToBv sz t2 r in [uu____2403] in
                t1 :: uu____2400 in
              (BvShl, uu____2397) in
            mkApp' uu____2390 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2420  ->
      fun r  ->
        match uu____2420 with
        | (t1,t2) ->
            let uu____2428 =
              let uu____2435 =
                let uu____2438 =
                  let uu____2441 = mkNatToBv sz t2 r in [uu____2441] in
                t1 :: uu____2438 in
              (BvShr, uu____2435) in
            mkApp' uu____2428 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2458  ->
      fun r  ->
        match uu____2458 with
        | (t1,t2) ->
            let uu____2466 =
              let uu____2473 =
                let uu____2476 =
                  let uu____2479 = mkNatToBv sz t2 r in [uu____2479] in
                t1 :: uu____2476 in
              (BvUdiv, uu____2473) in
            mkApp' uu____2466 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2496  ->
      fun r  ->
        match uu____2496 with
        | (t1,t2) ->
            let uu____2504 =
              let uu____2511 =
                let uu____2514 =
                  let uu____2517 = mkNatToBv sz t2 r in [uu____2517] in
                t1 :: uu____2514 in
              (BvMod, uu____2511) in
            mkApp' uu____2504 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2534  ->
      fun r  ->
        match uu____2534 with
        | (t1,t2) ->
            let uu____2542 =
              let uu____2549 =
                let uu____2552 =
                  let uu____2555 = mkNatToBv sz t2 r in [uu____2555] in
                t1 :: uu____2552 in
              (BvMul, uu____2549) in
            mkApp' uu____2542 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2588  ->
    fun r  ->
      match uu____2588 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2604 -> mk_bin_op Eq (t1, t2) r)
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
  fun uu____2711  ->
    fun r  ->
      match uu____2711 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2722) -> t2
           | App (FalseOp ,uu____2727) -> t3
           | uu____2732 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2733),App (TrueOp ,uu____2734)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2743),uu____2744) ->
                    let uu____2749 =
                      let uu____2754 = mkNot t1 t1.rng in (uu____2754, t3) in
                    mkImp uu____2749 r
                | (uu____2755,App (TrueOp ,uu____2756)) -> mkImp (t1, t2) r
                | (uu____2761,uu____2762) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____2809  ->
    fun r  ->
      match uu____2809 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2851) -> body
             | uu____2856 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2877  ->
    fun r  ->
      match uu____2877 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2913 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2913 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2932 = FStar_ST.op_Bang t1.freevars in
        match uu____2932 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3013 ->
            (match t1.tm with
             | Integer uu____3022 -> t1
             | BoundV uu____3023 -> t1
             | FreeV x ->
                 let uu____3029 = index_of x in
                 (match uu____3029 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3039 =
                   let uu____3046 = FStar_List.map (aux ix) tms in
                   (op, uu____3046) in
                 mkApp' uu____3039 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3054 =
                   let uu____3055 =
                     let uu____3062 = aux ix t2 in (uu____3062, r1, r2) in
                   Labeled uu____3055 in
                 mk uu____3054 t2.rng
             | LblPos (t2,r) ->
                 let uu____3065 =
                   let uu____3066 =
                     let uu____3071 = aux ix t2 in (uu____3071, r) in
                   LblPos uu____3066 in
                 mk uu____3065 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____3094 =
                   let uu____3113 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____3134 = aux (ix + n1) body in
                   (qop, uu____3113, wopt, vars, uu____3134) in
                 mkQuant uu____3094 t1.rng
             | Let (es,body) ->
                 let uu____3153 =
                   FStar_List.fold_left
                     (fun uu____3171  ->
                        fun e  ->
                          match uu____3171 with
                          | (ix1,l) ->
                              let uu____3191 =
                                let uu____3194 = aux ix1 e in uu____3194 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____3191))
                     (ix, []) es in
                 (match uu____3153 with
                  | (ix1,es_rev) ->
                      let uu____3205 =
                        let uu____3212 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____3212) in
                      mkLet uu____3205 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3238 -> t1
        | FreeV uu____3239 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3256 =
              let uu____3263 = FStar_List.map (aux shift) tms2 in
              (op, uu____3263) in
            mkApp' uu____3256 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3271 =
              let uu____3272 =
                let uu____3279 = aux shift t2 in (uu____3279, r1, r2) in
              Labeled uu____3272 in
            mk uu____3271 t2.rng
        | LblPos (t2,r) ->
            let uu____3282 =
              let uu____3283 =
                let uu____3288 = aux shift t2 in (uu____3288, r) in
              LblPos uu____3283 in
            mk uu____3282 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____3316 =
              let uu____3335 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____3352 = aux shift1 body in
              (qop, uu____3335, wopt, vars, uu____3352) in
            mkQuant uu____3316 t1.rng
        | Let (es,body) ->
            let uu____3367 =
              FStar_List.fold_left
                (fun uu____3385  ->
                   fun e  ->
                     match uu____3385 with
                     | (ix,es1) ->
                         let uu____3405 =
                           let uu____3408 = aux shift e in uu____3408 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____3405))
                (shift, []) es in
            (match uu____3367 with
             | (shift1,es_rev) ->
                 let uu____3419 =
                   let uu____3426 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____3426) in
                 mkLet uu____3419 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____3441 = abstr [fv] t in inst [s] uu____3441
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3465  ->
    match uu____3465 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3507 =
          let uu____3526 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____3543 = FStar_List.map fv_sort vars in
          let uu____3550 = abstr vars body in
          (qop, uu____3526, wopt, uu____3543, uu____3550) in
        mkQuant uu____3507
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3581  ->
    fun r  ->
      match uu____3581 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3647  ->
    fun r  ->
      match uu____3647 with
      | (pats,wopt,vars,body) ->
          let uu____3679 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____3679 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3704  ->
    fun r  ->
      match uu____3704 with
      | (pats,vars,body) ->
          let uu____3727 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3727 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3752  ->
    fun r  ->
      match uu____3752 with
      | (pats,vars,body) ->
          let uu____3775 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____3775 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3800  ->
    fun r  ->
      match uu____3800 with
      | (bindings,body) ->
          let uu____3826 = FStar_List.split bindings in
          (match uu____3826 with
           | (vars,es) ->
               let uu____3845 =
                 let uu____3852 = abstr vars body in (es, uu____3852) in
               mkLet uu____3845 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3874  ->
    match uu____3874 with
    | (nm,vars,s,tm,c) ->
        let uu____3908 =
          let uu____3921 = FStar_List.map fv_sort vars in
          let uu____3928 = abstr vars tm in
          (nm, uu____3921, s, uu____3928, c) in
        DefineFun uu____3908
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3935 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3935
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3946  ->
    fun id  ->
      match uu____3946 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3956 =
              let uu____3957 =
                let uu____3962 = mkInteger' id norng in
                let uu____3963 =
                  let uu____3964 =
                    let uu____3971 = constr_id_of_sort sort in
                    let uu____3972 =
                      let uu____3975 = mkApp (tok_name, []) norng in
                      [uu____3975] in
                    (uu____3971, uu____3972) in
                  mkApp uu____3964 norng in
                (uu____3962, uu____3963) in
              mkEq uu____3957 norng in
            {
              assumption_term = uu____3956;
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
  fun uu____3993  ->
    match uu____3993 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____4025 =
                      let uu____4030 =
                        let uu____4031 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____4031 in
                      (uu____4030, s) in
                    mkFreeV uu____4025 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____4039 =
            let uu____4046 = constr_id_of_sort sort in (uu____4046, [capp]) in
          mkApp uu____4039 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____4051 =
            let uu____4052 =
              let uu____4063 =
                let uu____4064 =
                  let uu____4069 = mkInteger id1 norng in
                  (uu____4069, cid_app) in
                mkEq uu____4064 norng in
              ([[capp]], bvar_names, uu____4063) in
            mkForall uu____4052 norng in
          {
            assumption_term = uu____4051;
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
  fun uu____4091  ->
    match uu____4091 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____4112 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____4112 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____4132 = let uu____4137 = bvar_name i in (uu____4137, s) in
          mkFreeV uu____4132 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4158  ->
                    match uu____4158 with
                    | (uu____4165,s,uu____4167) ->
                        let uu____4168 = bvar i s in uu____4168 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____4177 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4205  ->
                    match uu____4205 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____4228 =
                              let uu____4229 =
                                let uu____4240 =
                                  let uu____4241 =
                                    let uu____4246 =
                                      let uu____4247 = bvar i s in
                                      uu____4247 norng in
                                    (cproj_app, uu____4246) in
                                  mkEq uu____4241 norng in
                                ([[capp]], bvar_names, uu____4240) in
                              mkForall uu____4229 norng in
                            {
                              assumption_term = uu____4228;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____4177 FStar_List.flatten
let constructor_to_decl: constructor_t -> decls_t =
  fun uu____4270  ->
    match uu____4270 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4298  ->
                  match uu____4298 with
                  | (uu____4305,sort1,uu____4307) -> sort1)) in
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
            let uu____4325 =
              let uu____4330 =
                let uu____4331 =
                  let uu____4338 = constr_id_of_sort sort in
                  (uu____4338, [xx]) in
                mkApp uu____4331 norng in
              let uu____4341 =
                let uu____4342 = FStar_Util.string_of_int id in
                mkInteger uu____4342 norng in
              (uu____4330, uu____4341) in
            mkEq uu____4325 norng in
          let uu____4343 =
            let uu____4358 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4408  ->
                        match uu____4408 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4438 = mkApp (proj, [xx]) norng in
                              (uu____4438, [])
                            else
                              (let fi =
                                 let uu____4457 =
                                   let uu____4458 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____4458 in
                                 (uu____4457, s) in
                               let uu____4459 = mkFreeV fi norng in
                               (uu____4459, [fi])))) in
            FStar_All.pipe_right uu____4358 FStar_List.split in
          match uu____4343 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____4540 =
                  let uu____4545 = mkApp (name, proj_terms) norng in
                  (xx, uu____4545) in
                mkEq uu____4540 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4553 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____4594 =
          let uu____4597 =
            let uu____4598 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____4598 in
          uu____4597 :: cdecl :: cid :: projs in
        let uu____4599 =
          let uu____4602 =
            let uu____4605 =
              let uu____4606 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____4606 in
            [uu____4605] in
          FStar_List.append [disc] uu____4602 in
        FStar_List.append uu____4594 uu____4599
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
          let uu____4657 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4712  ->
                    fun s  ->
                      match uu____4712 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4762 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____4766 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____4766 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____4779 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____4779 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____4657 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4857 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____4857 with
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
              (let uu____5022 = FStar_Util.string_of_int n1 in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5022) in
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
                               "Prims.guard_free",{ tm = BoundV uu____5064;
                                                    freevars = uu____5065;
                                                    rng = uu____5066;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5080 -> tm)))) in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1")) in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5120 = FStar_List.nth names1 i in
              FStar_All.pipe_right uu____5120 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5135 = op_to_string op in
              let uu____5136 =
                let uu____5137 = FStar_List.map (aux1 n1 names1) tms in
                FStar_All.pipe_right uu____5137 (FStar_String.concat "\n") in
              FStar_Util.format2 "(%s %s)" uu____5135 uu____5136
          | Labeled (t2,uu____5143,uu____5144) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5147 = aux1 n1 names1 t2 in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5147 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid () in
              let uu____5170 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts in
              (match uu____5170 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ") in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5219 ->
                         let uu____5224 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5240 =
                                     let uu____5241 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5247 = aux1 n2 names2 p in
                                            FStar_Util.format1 "%s"
                                              uu____5247) pats2 in
                                     FStar_String.concat " " uu____5241 in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5240)) in
                         FStar_All.pipe_right uu____5224
                           (FStar_String.concat "\n") in
                   let uu____5250 =
                     let uu____5253 =
                       let uu____5256 =
                         let uu____5259 = aux1 n2 names2 body in
                         let uu____5260 =
                           let uu____5263 = weightToSmt wopt in
                           [uu____5263; pats_str; qid] in
                         uu____5259 :: uu____5260 in
                       binders1 :: uu____5256 in
                     (qop_to_string qop) :: uu____5253 in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5250)
          | Let (es,body) ->
              let uu____5270 =
                FStar_List.fold_left
                  (fun uu____5307  ->
                     fun e  ->
                       match uu____5307 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5357 = FStar_Util.string_of_int n0 in
                             Prims.strcat "@lb" uu____5357 in
                           let names01 = (nm, Term_sort) :: names0 in
                           let b =
                             let uu____5370 = aux1 n1 names1 e in
                             FStar_Util.format2 "(%s %s)" nm uu____5370 in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es in
              (match uu____5270 with
               | (names2,binders,n2) ->
                   let uu____5402 = aux1 n2 names2 body in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5402)
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5410 = FStar_Range.string_of_range t1.rng in
            let uu____5411 = FStar_Range.string_of_use_range t1.rng in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5410
              uu____5411 s
          else s in
        aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___120_5418  ->
    match uu___120_5418 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5422 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5437 -> (hd1, "...") in
        (match uu____5422 with
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
            let uu____5466 = FStar_Options.log_queries () in
            if uu____5466
            then
              let uu____5467 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___121_5471  ->
                     match uu___121_5471 with | [] -> "" | h::t -> h) in
              FStar_Util.format1 "\n; %s" uu____5467
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts in
            let uu____5490 = caption_to_string c in
            let uu____5491 = strSort retsort in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5490 f
              (FStar_String.concat " " l) uu____5491
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5501 = name_macro_binders arg_sorts in
            (match uu____5501 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5533 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                   inst uu____5533 body in
                 let uu____5546 = caption_to_string c in
                 let uu____5547 = strSort retsort in
                 let uu____5548 = termToSmt print_ranges (escape f) body1 in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5546 f (FStar_String.concat " " binders) uu____5547
                   uu____5548)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___122_5566  ->
                      match uu___122_5566 with
                      | Name n1 ->
                          Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                      | Namespace ns ->
                          Prims.strcat "Namespace "
                            (FStar_Ident.text_of_lid ns)
                      | Tag t -> Prims.strcat "Tag " t)) in
            let fids =
              let uu____5571 = FStar_Options.log_queries () in
              if uu____5571
              then
                let uu____5572 =
                  let uu____5573 = fact_ids_to_string a.assumption_fact_ids in
                  FStar_String.concat "; " uu____5573 in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5572
              else "" in
            let n1 = escape a.assumption_name in
            let uu____5578 = caption_to_string a.assumption_caption in
            let uu____5579 = termToSmt print_ranges n1 a.assumption_term in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5578
              fids uu____5579 n1
        | Eval t ->
            let uu____5581 = termToSmt print_ranges "eval" t in
            FStar_Util.format1 "(eval %s)" uu____5581
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5583 -> ""
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
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
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
      let uu____5912 =
        let uu____5915 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____5915
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____5912 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____5931 =
      let uu____5950 =
        let uu____5951 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____5951 in
      let uu____5956 =
        let uu____5965 =
          let uu____5972 =
            let uu____5973 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____5973 in
          (uu____5972, (BitVec_sort sz), true) in
        [uu____5965] in
      (uu____5950, uu____5956, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____5931 constructor_to_decl
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____6042 =
        let uu____6049 = let uu____6052 = mkInteger' i norng in [uu____6052] in
        ("Tm_uvar", uu____6049) in
      mkApp uu____6042 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6077 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6092 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____6092 u v1 t
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
      let uu____6125 =
        let uu____6126 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6126 in
      let uu____6131 =
        let uu____6132 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6132 in
      elim_box true uu____6125 uu____6131 t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6145 =
        let uu____6146 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6146 in
      let uu____6151 =
        let uu____6152 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6152 in
      elim_box true uu____6145 uu____6151 t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6166 -> FStar_Exn.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6176 -> FStar_Exn.raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6192 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____6192
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6204 = op_to_string op in
        let uu____6205 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____6204 uu____6205
    | Labeled (t1,r1,r2) ->
        let uu____6209 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6209
    | LblPos (t1,s) ->
        let uu____6212 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6212
    | Quant (qop,l,uu____6215,uu____6216,t1) ->
        let uu____6234 = print_smt_term_list_list l in
        let uu____6235 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6234
          uu____6235
    | Let (es,body) ->
        let uu____6242 = print_smt_term_list es in
        let uu____6243 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____6242 uu____6243
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____6247 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____6247 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6266 =
             let uu____6267 =
               let uu____6268 = print_smt_term_list l1 in
               Prims.strcat uu____6268 " ] " in
             Prims.strcat "; [ " uu____6267 in
           Prims.strcat s uu____6266) "" l
let getBoxedInteger: term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6284 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____6284
         | uu____6285 -> FStar_Pervasives_Native.None)
    | uu____6286 -> FStar_Pervasives_Native.None
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6297::t1::t2::[]);
                       freevars = uu____6300; rng = uu____6301;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6314::t1::t2::[]);
                       freevars = uu____6317; rng = uu____6318;_}::[])
        -> let uu____6331 = mkEq (t1, t2) norng in mkNot uu____6331 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6334; rng = uu____6335;_}::[])
        ->
        let uu____6348 =
          let uu____6353 = unboxInt t1 in
          let uu____6354 = unboxInt t2 in (uu____6353, uu____6354) in
        mkLTE uu____6348 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6357; rng = uu____6358;_}::[])
        ->
        let uu____6371 =
          let uu____6376 = unboxInt t1 in
          let uu____6377 = unboxInt t2 in (uu____6376, uu____6377) in
        mkLT uu____6371 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6380; rng = uu____6381;_}::[])
        ->
        let uu____6394 =
          let uu____6399 = unboxInt t1 in
          let uu____6400 = unboxInt t2 in (uu____6399, uu____6400) in
        mkGTE uu____6394 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6403; rng = uu____6404;_}::[])
        ->
        let uu____6417 =
          let uu____6422 = unboxInt t1 in
          let uu____6423 = unboxInt t2 in (uu____6422, uu____6423) in
        mkGT uu____6417 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6426; rng = uu____6427;_}::[])
        ->
        let uu____6440 =
          let uu____6445 = unboxBool t1 in
          let uu____6446 = unboxBool t2 in (uu____6445, uu____6446) in
        mkAnd uu____6440 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6449; rng = uu____6450;_}::[])
        ->
        let uu____6463 =
          let uu____6468 = unboxBool t1 in
          let uu____6469 = unboxBool t2 in (uu____6468, uu____6469) in
        mkOr uu____6463 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6471; rng = uu____6472;_}::[])
        -> let uu____6485 = unboxBool t1 in mkNot uu____6485 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6489; rng = uu____6490;_}::[])
        when
        let uu____6503 = getBoxedInteger t0 in FStar_Util.is_some uu____6503
        ->
        let sz =
          let uu____6507 = getBoxedInteger t0 in
          match uu____6507 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6511 -> failwith "impossible" in
        let uu____6514 =
          let uu____6519 = unboxBitVec sz t1 in
          let uu____6520 = unboxBitVec sz t2 in (uu____6519, uu____6520) in
        mkBvUlt uu____6514 t.rng
    | App
        (Var
         "Prims.equals",uu____6521::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6525;
                                      rng = uu____6526;_}::uu____6527::[])
        when
        let uu____6540 = getBoxedInteger t0 in FStar_Util.is_some uu____6540
        ->
        let sz =
          let uu____6544 = getBoxedInteger t0 in
          match uu____6544 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6548 -> failwith "impossible" in
        let uu____6551 =
          let uu____6556 = unboxBitVec sz t1 in
          let uu____6557 = unboxBitVec sz t2 in (uu____6556, uu____6557) in
        mkBvUlt uu____6551 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___123_6561 = unboxBool t1 in
        {
          tm = (uu___123_6561.tm);
          freevars = (uu___123_6561.freevars);
          rng = (t.rng)
        }
    | uu____6562 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6603 = FStar_Options.unthrottle_inductives () in
        if uu____6603
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
      let uu____6694 =
        let uu____6701 = let uu____6704 = mkInteger' i norng in [uu____6704] in
        ("FString_const", uu____6701) in
      mkApp uu____6694 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6719 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____6719 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6743 =
         let uu____6750 =
           let uu____6753 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____6753] in
         ("SFuel", uu____6750) in
       mkApp uu____6743 norng)
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
            let uu____6790 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____6790
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
      let uu____6847 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6847
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6864 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6864
let mk_haseq: term -> term =
  fun t  ->
    let uu____6873 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____6873