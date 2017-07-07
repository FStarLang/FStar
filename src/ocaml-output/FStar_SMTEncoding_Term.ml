open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | BitVec_sort of Prims.int
  | Array of (sort,sort) FStar_Pervasives_Native.tuple2
  | Arrow of (sort,sort) FStar_Pervasives_Native.tuple2
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____25 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____30 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____35 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____40 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____45 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____50 -> false
let uu___is_BitVec_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____56 -> false
let __proj__BitVec_sort__item___0: sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____72 -> false
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____94 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____114 -> false
let __proj__Sort__item___0: sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0
let rec strSort: sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | BitVec_sort n1 ->
        let uu____128 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ BitVec %s)" uu____128
    | Array (s1,s2) ->
        let uu____131 = strSort s1 in
        let uu____132 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____131 uu____132
    | Arrow (s1,s2) ->
        let uu____135 = strSort s1 in
        let uu____136 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____135 uu____136
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
  | NatToBv of Prims.int
  | ITE
  | Var of Prims.string
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____150 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____155 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____160 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____165 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____170 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____175 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____180 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____185 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____190 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____195 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____200 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____205 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____210 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____215 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____220 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____225 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____230 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____235 -> false
let uu___is_BvAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____240 -> false
let uu___is_BvXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____245 -> false
let uu___is_BvOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____250 -> false
let uu___is_BvShl: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____255 -> false
let uu___is_BvShr: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____260 -> false
let uu___is_BvUdiv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____265 -> false
let uu___is_BvMod: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____270 -> false
let uu___is_BvMul: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____275 -> false
let uu___is_BvUlt: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____280 -> false
let uu___is_NatToBv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____286 -> false
let __proj__NatToBv__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____299 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____305 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____318 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____323 -> false
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
    match projectee with | Integer _0 -> true | uu____400 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____414 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____430 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____453 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____485 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____529 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____555 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____580 -> false
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
    match projectee with | Name _0 -> true | uu____675 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____689 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____703 -> false
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
    match projectee with | DefPrelude  -> true | uu____817 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____828 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____863 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____895 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____909 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____923 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____937 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____952 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____968 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____973 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____978 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____983 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____991 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1010 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1015 -> false
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort x = FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1059 -> false
let freevar_sort: term -> sort =
  fun uu___87_1065  ->
    match uu___87_1065 with
    | { tm = FreeV x; freevars = uu____1067; rng = uu____1068;_} -> fv_sort x
    | uu____1075 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___88_1079  ->
    match uu___88_1079 with
    | { tm = FreeV fv; freevars = uu____1081; rng = uu____1082;_} -> fv
    | uu____1089 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1100 -> []
    | BoundV uu____1103 -> []
    | FreeV fv -> [fv]
    | App (uu____1113,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1119,uu____1120,uu____1121,uu____1122,t1) -> freevars t1
    | Labeled (t1,uu____1133,uu____1134) -> freevars t1
    | LblPos (t1,uu____1136) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1147 = FStar_ST.read t.freevars in
    match uu____1147 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1170 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1170 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___89_1183  ->
    match uu___89_1183 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___90_1187  ->
    match uu___90_1187 with
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
    | NatToBv n1 ->
        let uu____1189 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1189
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1195  ->
    match uu___91_1195 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1198 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1198
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1206 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1206
    | FreeV x ->
        let uu____1210 =
          let uu____1211 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1211 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1210
    | App (op,tms) ->
        let uu____1216 =
          let uu____1217 = op_to_string op in
          let uu____1218 =
            let uu____1219 =
              let uu____1220 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1220 (FStar_String.concat " ") in
            Prims.strcat uu____1219 ")" in
          Prims.strcat uu____1217 uu____1218 in
        Prims.strcat "(" uu____1216
    | Labeled (t1,r1,r2) ->
        let uu____1226 = hash_of_term t1 in
        let uu____1227 =
          let uu____1228 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1228 in
        Prims.strcat uu____1226 uu____1227
    | LblPos (t1,r) ->
        let uu____1231 =
          let uu____1232 = hash_of_term t1 in
          Prims.strcat uu____1232
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1231
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1246 =
          let uu____1247 =
            let uu____1248 =
              let uu____1249 =
                let uu____1250 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1250 (FStar_String.concat " ") in
              let uu____1253 =
                let uu____1254 =
                  let uu____1255 = hash_of_term body in
                  let uu____1256 =
                    let uu____1257 =
                      let uu____1258 = weightToSmt wopt in
                      let uu____1259 =
                        let uu____1260 =
                          let uu____1261 =
                            let uu____1262 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1272 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1272
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1262
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1261 "))" in
                        Prims.strcat " " uu____1260 in
                      Prims.strcat uu____1258 uu____1259 in
                    Prims.strcat " " uu____1257 in
                  Prims.strcat uu____1255 uu____1256 in
                Prims.strcat ")(! " uu____1254 in
              Prims.strcat uu____1249 uu____1253 in
            Prims.strcat " (" uu____1248 in
          Prims.strcat (qop_to_string qop) uu____1247 in
        Prims.strcat "(" uu____1246
    | Let (es,body) ->
        let uu____1280 =
          let uu____1281 =
            let uu____1282 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1282 (FStar_String.concat " ") in
          let uu____1285 =
            let uu____1286 =
              let uu____1287 = hash_of_term body in
              Prims.strcat uu____1287 ")" in
            Prims.strcat ") " uu____1286 in
          Prims.strcat uu____1281 uu____1285 in
        Prims.strcat "(let (" uu____1280
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1297 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1297; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1330 =
        let uu____1331 = FStar_Util.ensure_decimal i in Integer uu____1331 in
      mk uu____1330 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1340 = FStar_Util.string_of_int i in mkInteger uu____1340 r
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
  fun uu____1384  ->
    fun r  -> match uu____1384 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1402) -> mkFalse r
      | App (FalseOp ,uu____1405) -> mkTrue r
      | uu____1408 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1418  ->
    fun r  ->
      match uu____1418 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1424),uu____1425) -> t2
           | (uu____1428,App (TrueOp ,uu____1429)) -> t1
           | (App (FalseOp ,uu____1432),uu____1433) -> mkFalse r
           | (uu____1436,App (FalseOp ,uu____1437)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1447,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1453) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1457 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1469  ->
    fun r  ->
      match uu____1469 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1475),uu____1476) -> mkTrue r
           | (uu____1479,App (TrueOp ,uu____1480)) -> mkTrue r
           | (App (FalseOp ,uu____1483),uu____1484) -> t2
           | (uu____1487,App (FalseOp ,uu____1488)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1498,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1504) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1508 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1520  ->
    fun r  ->
      match uu____1520 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1526,App (TrueOp ,uu____1527)) -> mkTrue r
           | (App (FalseOp ,uu____1530),uu____1531) -> mkTrue r
           | (App (TrueOp ,uu____1534),uu____1535) -> t2
           | (uu____1538,App (Imp ,t1'::t2'::[])) ->
               let uu____1542 =
                 let uu____1546 =
                   let uu____1548 = mkAnd (t1, t1') r in [uu____1548; t2'] in
                 (Imp, uu____1546) in
               mkApp' uu____1542 r
           | uu____1550 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____1566  ->
      fun r  -> match uu____1566 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkNatToBv: Prims.int -> term -> FStar_Range.range -> term =
  fun sz  -> fun t  -> fun r  -> mkApp' ((NatToBv sz), [t]) r
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
    fun uu____1631  ->
      fun r  ->
        match uu____1631 with
        | (t1,t2) ->
            let uu____1637 =
              let uu____1641 =
                let uu____1643 =
                  let uu____1645 = mkNatToBv sz t2 r in [uu____1645] in
                t1 :: uu____1643 in
              (BvShl, uu____1641) in
            mkApp' uu____1637 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1659  ->
      fun r  ->
        match uu____1659 with
        | (t1,t2) ->
            let uu____1665 =
              let uu____1669 =
                let uu____1671 =
                  let uu____1673 = mkNatToBv sz t2 r in [uu____1673] in
                t1 :: uu____1671 in
              (BvShr, uu____1669) in
            mkApp' uu____1665 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1687  ->
      fun r  ->
        match uu____1687 with
        | (t1,t2) ->
            let uu____1693 =
              let uu____1697 =
                let uu____1699 =
                  let uu____1701 = mkNatToBv sz t2 r in [uu____1701] in
                t1 :: uu____1699 in
              (BvUdiv, uu____1697) in
            mkApp' uu____1693 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1715  ->
      fun r  ->
        match uu____1715 with
        | (t1,t2) ->
            let uu____1721 =
              let uu____1725 =
                let uu____1727 =
                  let uu____1729 = mkNatToBv sz t2 r in [uu____1729] in
                t1 :: uu____1727 in
              (BvMod, uu____1725) in
            mkApp' uu____1721 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1743  ->
      fun r  ->
        match uu____1743 with
        | (t1,t2) ->
            let uu____1749 =
              let uu____1753 =
                let uu____1755 =
                  let uu____1757 = mkNatToBv sz t2 r in [uu____1757] in
                t1 :: uu____1755 in
              (BvMul, uu____1753) in
            mkApp' uu____1749 r
let mkBvUlt:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Eq
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
  fun uu____1864  ->
    fun r  ->
      match uu____1864 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1872) -> t2
           | App (FalseOp ,uu____1875) -> t3
           | uu____1878 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1879),App (TrueOp ,uu____1880)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1885),uu____1886) ->
                    let uu____1889 =
                      let uu____1892 = mkNot t1 t1.rng in (uu____1892, t3) in
                    mkImp uu____1889 r
                | (uu____1893,App (TrueOp ,uu____1894)) -> mkImp (t1, t2) r
                | (uu____1897,uu____1898) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____1932  ->
    fun r  ->
      match uu____1932 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1961) -> body
             | uu____1964 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1978  ->
    fun r  ->
      match uu____1978 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2011 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2011 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2028 = FStar_ST.read t1.freevars in
        match uu____2028 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2044 ->
            (match t1.tm with
             | Integer uu____2049 -> t1
             | BoundV uu____2050 -> t1
             | FreeV x ->
                 let uu____2054 = index_of x in
                 (match uu____2054 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2061 =
                   let uu____2065 = FStar_List.map (aux ix) tms in
                   (op, uu____2065) in
                 mkApp' uu____2061 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2071 =
                   let uu____2072 =
                     let uu____2076 = aux ix t2 in (uu____2076, r1, r2) in
                   Labeled uu____2072 in
                 mk uu____2071 t2.rng
             | LblPos (t2,r) ->
                 let uu____2079 =
                   let uu____2080 =
                     let uu____2083 = aux ix t2 in (uu____2083, r) in
                   LblPos uu____2080 in
                 mk uu____2079 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2100 =
                   let uu____2110 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2123 = aux (ix + n1) body in
                   (qop, uu____2110, wopt, vars, uu____2123) in
                 mkQuant uu____2100 t1.rng
             | Let (es,body) ->
                 let uu____2136 =
                   FStar_List.fold_left
                     (fun uu____2148  ->
                        fun e  ->
                          match uu____2148 with
                          | (ix1,l) ->
                              let uu____2160 =
                                let uu____2162 = aux ix1 e in uu____2162 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____2160))
                     (ix, []) es in
                 (match uu____2136 with
                  | (ix1,es_rev) ->
                      let uu____2169 =
                        let uu____2173 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____2173) in
                      mkLet uu____2169 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____2197 -> t1
        | FreeV uu____2198 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____2211 =
              let uu____2215 = FStar_List.map (aux shift) tms2 in
              (op, uu____2215) in
            mkApp' uu____2211 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____2221 =
              let uu____2222 =
                let uu____2226 = aux shift t2 in (uu____2226, r1, r2) in
              Labeled uu____2222 in
            mk uu____2221 t2.rng
        | LblPos (t2,r) ->
            let uu____2229 =
              let uu____2230 =
                let uu____2233 = aux shift t2 in (uu____2233, r) in
              LblPos uu____2230 in
            mk uu____2229 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____2255 =
              let uu____2265 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____2274 = aux shift1 body in
              (qop, uu____2265, wopt, vars, uu____2274) in
            mkQuant uu____2255 t1.rng
        | Let (es,body) ->
            let uu____2283 =
              FStar_List.fold_left
                (fun uu____2295  ->
                   fun e  ->
                     match uu____2295 with
                     | (ix,es1) ->
                         let uu____2307 =
                           let uu____2309 = aux shift e in uu____2309 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____2307))
                (shift, []) es in
            (match uu____2283 with
             | (shift1,es_rev) ->
                 let uu____2316 =
                   let uu____2320 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____2320) in
                 mkLet uu____2316 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____2334 = abstr [fv] t in inst [s] uu____2334
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2349  ->
    match uu____2349 with
    | (qop,pats,wopt,vars,body) ->
        let uu____2374 =
          let uu____2384 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____2393 = FStar_List.map fv_sort vars in
          let uu____2397 = abstr vars body in
          (qop, uu____2384, wopt, uu____2393, uu____2397) in
        mkQuant uu____2374
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____2416  ->
    fun r  ->
      match uu____2416 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____2455  ->
    fun r  ->
      match uu____2455 with
      | (pats,wopt,vars,body) ->
          let uu____2474 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____2474 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2491  ->
    fun r  ->
      match uu____2491 with
      | (pats,vars,body) ->
          let uu____2505 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2505 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2522  ->
    fun r  ->
      match uu____2522 with
      | (pats,vars,body) ->
          let uu____2536 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2536 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____2553  ->
    fun r  ->
      match uu____2553 with
      | (bindings,body) ->
          let uu____2568 = FStar_List.split bindings in
          (match uu____2568 with
           | (vars,es) ->
               let uu____2579 =
                 let uu____2583 = abstr vars body in (es, uu____2583) in
               mkLet uu____2579 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____2596  ->
    match uu____2596 with
    | (nm,vars,s,tm,c) ->
        let uu____2616 =
          let uu____2623 = FStar_List.map fv_sort vars in
          let uu____2627 = abstr vars tm in
          (nm, uu____2623, s, uu____2627, c) in
        DefineFun uu____2616
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2633 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2633
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____2642  ->
    fun id  ->
      match uu____2642 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2650 =
              let uu____2651 =
                let uu____2654 = mkInteger' id norng in
                let uu____2655 =
                  let uu____2656 =
                    let uu____2660 = constr_id_of_sort sort in
                    let uu____2661 =
                      let uu____2663 = mkApp (tok_name, []) norng in
                      [uu____2663] in
                    (uu____2660, uu____2661) in
                  mkApp uu____2656 norng in
                (uu____2654, uu____2655) in
              mkEq uu____2651 norng in
            {
              assumption_term = uu____2650;
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
  fun uu____2674  ->
    match uu____2674 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2696 =
                      let uu____2699 =
                        let uu____2700 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2700 in
                      (uu____2699, s) in
                    mkFreeV uu____2696 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2706 =
            let uu____2710 = constr_id_of_sort sort in (uu____2710, [capp]) in
          mkApp uu____2706 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2714 =
            let uu____2715 =
              let uu____2721 =
                let uu____2722 =
                  let uu____2725 = mkInteger id1 norng in
                  (uu____2725, cid_app) in
                mkEq uu____2722 norng in
              ([[capp]], bvar_names, uu____2721) in
            mkForall uu____2715 norng in
          {
            assumption_term = uu____2714;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decl Prims.list
  =
  fun uu____2738  ->
    match uu____2738 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2755 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2755 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2775 = let uu____2778 = bvar_name i in (uu____2778, s) in
          mkFreeV uu____2775 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2793  ->
                    match uu____2793 with
                    | (uu____2797,s,uu____2799) ->
                        let uu____2800 = bvar i s in uu____2800 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2807 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2826  ->
                    match uu____2826 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2841 =
                              let uu____2842 =
                                let uu____2848 =
                                  let uu____2849 =
                                    let uu____2852 =
                                      let uu____2853 = bvar i s in
                                      uu____2853 norng in
                                    (cproj_app, uu____2852) in
                                  mkEq uu____2849 norng in
                                ([[capp]], bvar_names, uu____2848) in
                              mkForall uu____2842 norng in
                            {
                              assumption_term = uu____2841;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2807 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2868  ->
    match uu____2868 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2888  ->
                  match uu____2888 with
                  | (uu____2892,sort1,uu____2894) -> sort1)) in
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
            let uu____2907 =
              let uu____2910 =
                let uu____2911 =
                  let uu____2915 = constr_id_of_sort sort in
                  (uu____2915, [xx]) in
                mkApp uu____2911 norng in
              let uu____2917 =
                let uu____2918 = FStar_Util.string_of_int id in
                mkInteger uu____2918 norng in
              (uu____2910, uu____2917) in
            mkEq uu____2907 norng in
          let uu____2919 =
            let uu____2927 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2956  ->
                        match uu____2956 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2973 = mkApp (proj, [xx]) norng in
                              (uu____2973, [])
                            else
                              (let fi =
                                 let uu____2984 =
                                   let uu____2985 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2985 in
                                 (uu____2984, s) in
                               let uu____2986 = mkFreeV fi norng in
                               (uu____2986, [fi])))) in
            FStar_All.pipe_right uu____2927 FStar_List.split in
          match uu____2919 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____3029 =
                  let uu____3032 = mkApp (name, proj_terms) norng in
                  (xx, uu____3032) in
                mkEq uu____3029 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____3037 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____3060 =
          let uu____3062 =
            let uu____3063 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____3063 in
          uu____3062 :: cdecl :: cid :: projs in
        let uu____3064 =
          let uu____3066 =
            let uu____3068 =
              let uu____3069 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____3069 in
            [uu____3068] in
          FStar_List.append [disc] uu____3066 in
        FStar_List.append uu____3060 uu____3064
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
          let uu____3103 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____3136  ->
                    fun s  ->
                      match uu____3136 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____3164 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____3168 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____3168 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____3176 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____3176 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____3103 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____3219 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____3219 with
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
            (let uu____3275 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____3275) in
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
                             "Prims.guard_free",{ tm = BoundV uu____3302;
                                                  freevars = uu____3303;
                                                  rng = uu____3304;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____3312 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____3348 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____3348 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____3358 = op_to_string op in
            let uu____3359 =
              let uu____3360 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____3360 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" uu____3358 uu____3359
        | Labeled (t2,uu____3364,uu____3365) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____3368 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____3368 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____3383 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts in
            (match uu____3383 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____3411 ->
                       let uu____3414 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____3424 =
                                   let uu____3425 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____3430 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____3430)
                                       pats2 in
                                   FStar_String.concat " " uu____3425 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____3424)) in
                       FStar_All.pipe_right uu____3414
                         (FStar_String.concat "\n") in
                 let uu____3432 =
                   let uu____3434 =
                     let uu____3436 =
                       let uu____3438 = aux1 n2 names2 body in
                       let uu____3439 =
                         let uu____3441 = weightToSmt wopt in
                         [uu____3441; pats_str; qid] in
                       uu____3438 :: uu____3439 in
                     binders1 :: uu____3436 in
                   (qop_to_string qop) :: uu____3434 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____3432)
        | Let (es,body) ->
            let uu____3446 =
              FStar_List.fold_left
                (fun uu____3469  ->
                   fun e  ->
                     match uu____3469 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____3497 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____3497 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____3505 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____3505 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____3446 with
             | (names2,binders,n2) ->
                 let uu____3523 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____3523)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____3530 = FStar_Range.string_of_range t1.rng in
          let uu____3531 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____3530
            uu____3531 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_3537  ->
    match uu___92_3537 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____3540 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____3549 -> (hd1, "...") in
        (match uu____3540 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____3566 = FStar_Options.log_queries () in
          if uu____3566
          then
            let uu____3567 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_3570  ->
                   match uu___93_3570 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____3567
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____3584 = caption_to_string c in
          let uu____3585 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3584 f
            (FStar_String.concat " " l) uu____3585
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____3593 = name_macro_binders arg_sorts in
          (match uu____3593 with
           | (names1,binders) ->
               let body1 =
                 let uu____3611 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____3611 body in
               let uu____3619 = caption_to_string c in
               let uu____3620 = strSort retsort in
               let uu____3621 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3619
                 f (FStar_String.concat " " binders) uu____3620 uu____3621)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_3634  ->
                    match uu___94_3634 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3639 = FStar_Options.log_queries () in
            if uu____3639
            then
              let uu____3640 =
                let uu____3641 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3641 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3640
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3645 = caption_to_string a.assumption_caption in
          let uu____3646 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3645 fids
            uu____3646 n1
      | Eval t ->
          let uu____3648 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3648
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3650 -> ""
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
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_unit", [], Term_sort, (Prims.parse_int "6"), true);
      ("BoxInt", [("BoxInt_proj_0", Int_sort, true)], Term_sort,
        (Prims.parse_int "7"), true);
      ("BoxBool", [("BoxBool_proj_0", Bool_sort, true)], Term_sort,
        (Prims.parse_int "8"), true);
      ("BoxString", [("BoxString_proj_0", String_sort, true)], Term_sort,
        (Prims.parse_int "9"), true);
      ("BoxRef", [("BoxRef_proj_0", Ref_sort, true)], Term_sort,
        (Prims.parse_int "10"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let uu____3835 =
        let uu____3837 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3837
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3835 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____3848 =
      let uu____3858 =
        let uu____3859 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____3859 in
      let uu____3860 =
        let uu____3865 =
          let uu____3869 =
            let uu____3870 = FStar_Util.string_of_int sz in
            FStar_Util.format1 "BoxBitVec%s_proj_0" uu____3870 in
          (uu____3869, (BitVec_sort sz), true) in
        [uu____3865] in
      (uu____3858, uu____3860, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____3848 constructor_to_decl
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3913 =
        let uu____3917 = let uu____3919 = mkInteger' i norng in [uu____3919] in
        ("Tm_uvar", uu____3917) in
      mkApp uu____3913 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____3941 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____3955 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____3955 u v1 t
let boxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt" "BoxInt_proj_0" t
let unboxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt_proj_0" "BoxInt" t
let boxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool" "BoxBool_proj_0" t
let unboxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool_proj_0" "BoxBool" t
let boxString: term -> term =
  fun t  -> maybe_elim_box "BoxString" "BoxString_proj_0" t
let unboxString: term -> term =
  fun t  -> maybe_elim_box "BoxString_proj_0" "BoxString" t
let boxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef" "BoxRef_proj_0" t
let unboxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef_proj_0" "BoxRef" t
let boxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let boxOfSize =
        let uu____3997 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____3997 in
      elim_box true boxOfSize (Prims.strcat boxOfSize "_proj_0") t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let boxOfSize =
        let uu____4007 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____4007 in
      elim_box true (Prims.strcat boxOfSize "_proj_0") boxOfSize t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____4017 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____4027 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____4037::t1::t2::[]);
                       freevars = uu____4040; rng = uu____4041;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____4048::t1::t2::[]);
                       freevars = uu____4051; rng = uu____4052;_}::[])
        -> let uu____4059 = mkEq (t1, t2) norng in mkNot uu____4059 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____4062; rng = uu____4063;_}::[])
        ->
        let uu____4070 =
          let uu____4073 = unboxInt t1 in
          let uu____4074 = unboxInt t2 in (uu____4073, uu____4074) in
        mkLTE uu____4070 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____4077; rng = uu____4078;_}::[])
        ->
        let uu____4085 =
          let uu____4088 = unboxInt t1 in
          let uu____4089 = unboxInt t2 in (uu____4088, uu____4089) in
        mkLT uu____4085 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____4092; rng = uu____4093;_}::[])
        ->
        let uu____4100 =
          let uu____4103 = unboxInt t1 in
          let uu____4104 = unboxInt t2 in (uu____4103, uu____4104) in
        mkGTE uu____4100 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____4107; rng = uu____4108;_}::[])
        ->
        let uu____4115 =
          let uu____4118 = unboxInt t1 in
          let uu____4119 = unboxInt t2 in (uu____4118, uu____4119) in
        mkGT uu____4115 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____4122; rng = uu____4123;_}::[])
        ->
        let uu____4130 =
          let uu____4133 = unboxBool t1 in
          let uu____4134 = unboxBool t2 in (uu____4133, uu____4134) in
        mkAnd uu____4130 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____4137; rng = uu____4138;_}::[])
        ->
        let uu____4145 =
          let uu____4148 = unboxBool t1 in
          let uu____4149 = unboxBool t2 in (uu____4148, uu____4149) in
        mkOr uu____4145 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____4151; rng = uu____4152;_}::[])
        -> let uu____4159 = unboxBool t1 in mkNot uu____4159 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_4162 = unboxBool t1 in
        {
          tm = (uu___95_4162.tm);
          freevars = (uu___95_4162.freevars);
          rng = (t.rng)
        }
    | uu____4165 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____4202 = FStar_Options.unthrottle_inductives () in
        if uu____4202
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
      let uu____4284 =
        let uu____4288 = let uu____4290 = mkInteger' i norng in [uu____4290] in
        ("FString_const", uu____4288) in
      mkApp uu____4284 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____4304 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____4304 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____4325 =
         let uu____4329 =
           let uu____4331 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____4331] in
         ("SFuel", uu____4329) in
       mkApp uu____4325 norng)
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
            let uu____4357 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____4357
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
      let uu____4397 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____4397
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____4412 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____4412
let mk_haseq: term -> term =
  fun t  ->
    let uu____4421 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____4421
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4435 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____4435
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4443 = op_to_string op in
        let uu____4444 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____4443 uu____4444
    | Labeled (t1,r1,r2) ->
        let uu____4448 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4448
    | LblPos (t1,s) ->
        let uu____4451 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4451
    | Quant (qop,l,uu____4454,uu____4455,t1) ->
        let uu____4465 = print_smt_term_list_list l in
        let uu____4466 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4465
          uu____4466
    | Let (es,body) ->
        let uu____4471 = print_smt_term_list es in
        let uu____4472 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____4471 uu____4472
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____4475 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____4475 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4488 =
             let uu____4489 =
               let uu____4490 = print_smt_term_list l1 in
               Prims.strcat uu____4490 " ] " in
             Prims.strcat "; [ " uu____4489 in
           Prims.strcat s uu____4488) "" l