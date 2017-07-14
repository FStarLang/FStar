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
  | BvUext of Prims.int
  | NatToBv of Prims.int
  | BvToNat
  | ITE
  | Var of Prims.string
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____154 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____159 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____164 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____169 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____174 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____179 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____184 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____189 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____194 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____199 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____204 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____209 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____214 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____219 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____224 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____229 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____234 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____239 -> false
let uu___is_BvAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____244 -> false
let uu___is_BvXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____249 -> false
let uu___is_BvOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____254 -> false
let uu___is_BvShl: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____259 -> false
let uu___is_BvShr: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____264 -> false
let uu___is_BvUdiv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____269 -> false
let uu___is_BvMod: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____274 -> false
let uu___is_BvMul: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____279 -> false
let uu___is_BvUlt: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____284 -> false
let uu___is_BvUext: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____290 -> false
let __proj__BvUext__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0
let uu___is_NatToBv: op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____304 -> false
let __proj__NatToBv__item___0: op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
let uu___is_BvToNat: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____317 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____322 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____328 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____341 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____346 -> false
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
    match projectee with | Integer _0 -> true | uu____423 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____437 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____453 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____476 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____508 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____552 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____578 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____603 -> false
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
    match projectee with | Name _0 -> true | uu____698 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____712 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____726 -> false
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
    match projectee with | DefPrelude  -> true | uu____840 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____851 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____886 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____918 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____932 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____946 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____960 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____975 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____991 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____996 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1001 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1006 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1014 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1033 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1038 -> false
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
      | uu____1082 -> false
let freevar_sort: term -> sort =
  fun uu___87_1088  ->
    match uu___87_1088 with
    | { tm = FreeV x; freevars = uu____1090; rng = uu____1091;_} -> fv_sort x
    | uu____1098 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___88_1102  ->
    match uu___88_1102 with
    | { tm = FreeV fv; freevars = uu____1104; rng = uu____1105;_} -> fv
    | uu____1112 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1123 -> []
    | BoundV uu____1126 -> []
    | FreeV fv -> [fv]
    | App (uu____1136,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1142,uu____1143,uu____1144,uu____1145,t1) -> freevars t1
    | Labeled (t1,uu____1156,uu____1157) -> freevars t1
    | LblPos (t1,uu____1159) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1170 = FStar_ST.read t.freevars in
    match uu____1170 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1193 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1193 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___89_1206  ->
    match uu___89_1206 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___90_1210  ->
    match uu___90_1210 with
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
        let uu____1212 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1212
    | NatToBv n1 ->
        let uu____1214 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____1214
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1220  ->
    match uu___91_1220 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1223 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1223
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1231 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1231
    | FreeV x ->
        let uu____1235 =
          let uu____1236 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1236 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1235
    | App (op,tms) ->
        let uu____1241 =
          let uu____1242 = op_to_string op in
          let uu____1243 =
            let uu____1244 =
              let uu____1245 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1245 (FStar_String.concat " ") in
            Prims.strcat uu____1244 ")" in
          Prims.strcat uu____1242 uu____1243 in
        Prims.strcat "(" uu____1241
    | Labeled (t1,r1,r2) ->
        let uu____1251 = hash_of_term t1 in
        let uu____1252 =
          let uu____1253 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1253 in
        Prims.strcat uu____1251 uu____1252
    | LblPos (t1,r) ->
        let uu____1256 =
          let uu____1257 = hash_of_term t1 in
          Prims.strcat uu____1257
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1256
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1271 =
          let uu____1272 =
            let uu____1273 =
              let uu____1274 =
                let uu____1275 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1275 (FStar_String.concat " ") in
              let uu____1278 =
                let uu____1279 =
                  let uu____1280 = hash_of_term body in
                  let uu____1281 =
                    let uu____1282 =
                      let uu____1283 = weightToSmt wopt in
                      let uu____1284 =
                        let uu____1285 =
                          let uu____1286 =
                            let uu____1287 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1297 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1297
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1287
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1286 "))" in
                        Prims.strcat " " uu____1285 in
                      Prims.strcat uu____1283 uu____1284 in
                    Prims.strcat " " uu____1282 in
                  Prims.strcat uu____1280 uu____1281 in
                Prims.strcat ")(! " uu____1279 in
              Prims.strcat uu____1274 uu____1278 in
            Prims.strcat " (" uu____1273 in
          Prims.strcat (qop_to_string qop) uu____1272 in
        Prims.strcat "(" uu____1271
    | Let (es,body) ->
        let uu____1305 =
          let uu____1306 =
            let uu____1307 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1307 (FStar_String.concat " ") in
          let uu____1310 =
            let uu____1311 =
              let uu____1312 = hash_of_term body in
              Prims.strcat uu____1312 ")" in
            Prims.strcat ") " uu____1311 in
          Prims.strcat uu____1306 uu____1310 in
        Prims.strcat "(let (" uu____1305
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1322 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1322; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1355 =
        let uu____1356 = FStar_Util.ensure_decimal i in Integer uu____1356 in
      mk uu____1355 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1365 = FStar_Util.string_of_int i in mkInteger uu____1365 r
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
  fun uu____1409  ->
    fun r  -> match uu____1409 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1427) -> mkFalse r
      | App (FalseOp ,uu____1430) -> mkTrue r
      | uu____1433 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1443  ->
    fun r  ->
      match uu____1443 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1449),uu____1450) -> t2
           | (uu____1453,App (TrueOp ,uu____1454)) -> t1
           | (App (FalseOp ,uu____1457),uu____1458) -> mkFalse r
           | (uu____1461,App (FalseOp ,uu____1462)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1472,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1478) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1482 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1494  ->
    fun r  ->
      match uu____1494 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1500),uu____1501) -> mkTrue r
           | (uu____1504,App (TrueOp ,uu____1505)) -> mkTrue r
           | (App (FalseOp ,uu____1508),uu____1509) -> t2
           | (uu____1512,App (FalseOp ,uu____1513)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1523,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1529) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1533 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1545  ->
    fun r  ->
      match uu____1545 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1551,App (TrueOp ,uu____1552)) -> mkTrue r
           | (App (FalseOp ,uu____1555),uu____1556) -> mkTrue r
           | (App (TrueOp ,uu____1559),uu____1560) -> t2
           | (uu____1563,App (Imp ,t1'::t2'::[])) ->
               let uu____1567 =
                 let uu____1571 =
                   let uu____1573 = mkAnd (t1, t1') r in [uu____1573; t2'] in
                 (Imp, uu____1571) in
               mkApp' uu____1567 r
           | uu____1575 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____1591  ->
      fun r  -> match uu____1591 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
    fun uu____1678  ->
      fun r  ->
        match uu____1678 with
        | (t1,t2) ->
            let uu____1684 =
              let uu____1688 =
                let uu____1690 =
                  let uu____1692 = mkNatToBv sz t2 r in [uu____1692] in
                t1 :: uu____1690 in
              (BvShl, uu____1688) in
            mkApp' uu____1684 r
let mkBvShr:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1706  ->
      fun r  ->
        match uu____1706 with
        | (t1,t2) ->
            let uu____1712 =
              let uu____1716 =
                let uu____1718 =
                  let uu____1720 = mkNatToBv sz t2 r in [uu____1720] in
                t1 :: uu____1718 in
              (BvShr, uu____1716) in
            mkApp' uu____1712 r
let mkBvUdiv:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1734  ->
      fun r  ->
        match uu____1734 with
        | (t1,t2) ->
            let uu____1740 =
              let uu____1744 =
                let uu____1746 =
                  let uu____1748 = mkNatToBv sz t2 r in [uu____1748] in
                t1 :: uu____1746 in
              (BvUdiv, uu____1744) in
            mkApp' uu____1740 r
let mkBvMod:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1762  ->
      fun r  ->
        match uu____1762 with
        | (t1,t2) ->
            let uu____1768 =
              let uu____1772 =
                let uu____1774 =
                  let uu____1776 = mkNatToBv sz t2 r in [uu____1776] in
                t1 :: uu____1774 in
              (BvMod, uu____1772) in
            mkApp' uu____1768 r
let mkBvMul:
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____1790  ->
      fun r  ->
        match uu____1790 with
        | (t1,t2) ->
            let uu____1796 =
              let uu____1800 =
                let uu____1802 =
                  let uu____1804 = mkNatToBv sz t2 r in [uu____1804] in
                t1 :: uu____1802 in
              (BvMul, uu____1800) in
            mkApp' uu____1796 r
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
  fun uu____1911  ->
    fun r  ->
      match uu____1911 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1919) -> t2
           | App (FalseOp ,uu____1922) -> t3
           | uu____1925 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1926),App (TrueOp ,uu____1927)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1932),uu____1933) ->
                    let uu____1936 =
                      let uu____1939 = mkNot t1 t1.rng in (uu____1939, t3) in
                    mkImp uu____1936 r
                | (uu____1940,App (TrueOp ,uu____1941)) -> mkImp (t1, t2) r
                | (uu____1944,uu____1945) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____1979  ->
    fun r  ->
      match uu____1979 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2008) -> body
             | uu____2011 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2025  ->
    fun r  ->
      match uu____2025 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2058 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2058 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2075 = FStar_ST.read t1.freevars in
        match uu____2075 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2091 ->
            (match t1.tm with
             | Integer uu____2096 -> t1
             | BoundV uu____2097 -> t1
             | FreeV x ->
                 let uu____2101 = index_of x in
                 (match uu____2101 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2108 =
                   let uu____2112 = FStar_List.map (aux ix) tms in
                   (op, uu____2112) in
                 mkApp' uu____2108 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2118 =
                   let uu____2119 =
                     let uu____2123 = aux ix t2 in (uu____2123, r1, r2) in
                   Labeled uu____2119 in
                 mk uu____2118 t2.rng
             | LblPos (t2,r) ->
                 let uu____2126 =
                   let uu____2127 =
                     let uu____2130 = aux ix t2 in (uu____2130, r) in
                   LblPos uu____2127 in
                 mk uu____2126 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2147 =
                   let uu____2157 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2170 = aux (ix + n1) body in
                   (qop, uu____2157, wopt, vars, uu____2170) in
                 mkQuant uu____2147 t1.rng
             | Let (es,body) ->
                 let uu____2183 =
                   FStar_List.fold_left
                     (fun uu____2195  ->
                        fun e  ->
                          match uu____2195 with
                          | (ix1,l) ->
                              let uu____2207 =
                                let uu____2209 = aux ix1 e in uu____2209 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____2207))
                     (ix, []) es in
                 (match uu____2183 with
                  | (ix1,es_rev) ->
                      let uu____2216 =
                        let uu____2220 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____2220) in
                      mkLet uu____2216 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____2244 -> t1
        | FreeV uu____2245 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____2258 =
              let uu____2262 = FStar_List.map (aux shift) tms2 in
              (op, uu____2262) in
            mkApp' uu____2258 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____2268 =
              let uu____2269 =
                let uu____2273 = aux shift t2 in (uu____2273, r1, r2) in
              Labeled uu____2269 in
            mk uu____2268 t2.rng
        | LblPos (t2,r) ->
            let uu____2276 =
              let uu____2277 =
                let uu____2280 = aux shift t2 in (uu____2280, r) in
              LblPos uu____2277 in
            mk uu____2276 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____2302 =
              let uu____2312 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____2321 = aux shift1 body in
              (qop, uu____2312, wopt, vars, uu____2321) in
            mkQuant uu____2302 t1.rng
        | Let (es,body) ->
            let uu____2330 =
              FStar_List.fold_left
                (fun uu____2342  ->
                   fun e  ->
                     match uu____2342 with
                     | (ix,es1) ->
                         let uu____2354 =
                           let uu____2356 = aux shift e in uu____2356 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____2354))
                (shift, []) es in
            (match uu____2330 with
             | (shift1,es_rev) ->
                 let uu____2363 =
                   let uu____2367 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____2367) in
                 mkLet uu____2363 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____2381 = abstr [fv] t in inst [s] uu____2381
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2396  ->
    match uu____2396 with
    | (qop,pats,wopt,vars,body) ->
        let uu____2421 =
          let uu____2431 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____2440 = FStar_List.map fv_sort vars in
          let uu____2444 = abstr vars body in
          (qop, uu____2431, wopt, uu____2440, uu____2444) in
        mkQuant uu____2421
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____2463  ->
    fun r  ->
      match uu____2463 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____2502  ->
    fun r  ->
      match uu____2502 with
      | (pats,wopt,vars,body) ->
          let uu____2521 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____2521 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2538  ->
    fun r  ->
      match uu____2538 with
      | (pats,vars,body) ->
          let uu____2552 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2552 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2569  ->
    fun r  ->
      match uu____2569 with
      | (pats,vars,body) ->
          let uu____2583 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2583 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____2600  ->
    fun r  ->
      match uu____2600 with
      | (bindings,body) ->
          let uu____2615 = FStar_List.split bindings in
          (match uu____2615 with
           | (vars,es) ->
               let uu____2626 =
                 let uu____2630 = abstr vars body in (es, uu____2630) in
               mkLet uu____2626 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____2643  ->
    match uu____2643 with
    | (nm,vars,s,tm,c) ->
        let uu____2663 =
          let uu____2670 = FStar_List.map fv_sort vars in
          let uu____2674 = abstr vars tm in
          (nm, uu____2670, s, uu____2674, c) in
        DefineFun uu____2663
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2680 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2680
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____2689  ->
    fun id  ->
      match uu____2689 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2697 =
              let uu____2698 =
                let uu____2701 = mkInteger' id norng in
                let uu____2702 =
                  let uu____2703 =
                    let uu____2707 = constr_id_of_sort sort in
                    let uu____2708 =
                      let uu____2710 = mkApp (tok_name, []) norng in
                      [uu____2710] in
                    (uu____2707, uu____2708) in
                  mkApp uu____2703 norng in
                (uu____2701, uu____2702) in
              mkEq uu____2698 norng in
            {
              assumption_term = uu____2697;
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
  fun uu____2721  ->
    match uu____2721 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2743 =
                      let uu____2746 =
                        let uu____2747 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2747 in
                      (uu____2746, s) in
                    mkFreeV uu____2743 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2753 =
            let uu____2757 = constr_id_of_sort sort in (uu____2757, [capp]) in
          mkApp uu____2753 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2761 =
            let uu____2762 =
              let uu____2768 =
                let uu____2769 =
                  let uu____2772 = mkInteger id1 norng in
                  (uu____2772, cid_app) in
                mkEq uu____2769 norng in
              ([[capp]], bvar_names, uu____2768) in
            mkForall uu____2762 norng in
          {
            assumption_term = uu____2761;
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
  fun uu____2785  ->
    match uu____2785 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2802 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2802 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2822 = let uu____2825 = bvar_name i in (uu____2825, s) in
          mkFreeV uu____2822 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2840  ->
                    match uu____2840 with
                    | (uu____2844,s,uu____2846) ->
                        let uu____2847 = bvar i s in uu____2847 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2854 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2873  ->
                    match uu____2873 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2888 =
                              let uu____2889 =
                                let uu____2895 =
                                  let uu____2896 =
                                    let uu____2899 =
                                      let uu____2900 = bvar i s in
                                      uu____2900 norng in
                                    (cproj_app, uu____2899) in
                                  mkEq uu____2896 norng in
                                ([[capp]], bvar_names, uu____2895) in
                              mkForall uu____2889 norng in
                            {
                              assumption_term = uu____2888;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2854 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2915  ->
    match uu____2915 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2935  ->
                  match uu____2935 with
                  | (uu____2939,sort1,uu____2941) -> sort1)) in
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
            let uu____2954 =
              let uu____2957 =
                let uu____2958 =
                  let uu____2962 = constr_id_of_sort sort in
                  (uu____2962, [xx]) in
                mkApp uu____2958 norng in
              let uu____2964 =
                let uu____2965 = FStar_Util.string_of_int id in
                mkInteger uu____2965 norng in
              (uu____2957, uu____2964) in
            mkEq uu____2954 norng in
          let uu____2966 =
            let uu____2974 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____3003  ->
                        match uu____3003 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____3020 = mkApp (proj, [xx]) norng in
                              (uu____3020, [])
                            else
                              (let fi =
                                 let uu____3031 =
                                   let uu____3032 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____3032 in
                                 (uu____3031, s) in
                               let uu____3033 = mkFreeV fi norng in
                               (uu____3033, [fi])))) in
            FStar_All.pipe_right uu____2974 FStar_List.split in
          match uu____2966 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____3076 =
                  let uu____3079 = mkApp (name, proj_terms) norng in
                  (xx, uu____3079) in
                mkEq uu____3076 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____3084 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____3107 =
          let uu____3109 =
            let uu____3110 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____3110 in
          uu____3109 :: cdecl :: cid :: projs in
        let uu____3111 =
          let uu____3113 =
            let uu____3115 =
              let uu____3116 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____3116 in
            [uu____3115] in
          FStar_List.append [disc] uu____3113 in
        FStar_List.append uu____3107 uu____3111
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
          let uu____3150 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____3183  ->
                    fun s  ->
                      match uu____3183 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____3211 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____3215 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____3215 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____3223 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____3223 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____3150 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____3266 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____3266 with
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
            (let uu____3322 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____3322) in
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
                             "Prims.guard_free",{ tm = BoundV uu____3349;
                                                  freevars = uu____3350;
                                                  rng = uu____3351;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____3359 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____3395 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____3395 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____3405 = op_to_string op in
            let uu____3406 =
              let uu____3407 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____3407 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" uu____3405 uu____3406
        | Labeled (t2,uu____3411,uu____3412) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____3415 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____3415 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____3430 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts in
            (match uu____3430 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____3458 ->
                       let uu____3461 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____3471 =
                                   let uu____3472 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____3477 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____3477)
                                       pats2 in
                                   FStar_String.concat " " uu____3472 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____3471)) in
                       FStar_All.pipe_right uu____3461
                         (FStar_String.concat "\n") in
                 let uu____3479 =
                   let uu____3481 =
                     let uu____3483 =
                       let uu____3485 = aux1 n2 names2 body in
                       let uu____3486 =
                         let uu____3488 = weightToSmt wopt in
                         [uu____3488; pats_str; qid] in
                       uu____3485 :: uu____3486 in
                     binders1 :: uu____3483 in
                   (qop_to_string qop) :: uu____3481 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____3479)
        | Let (es,body) ->
            let uu____3493 =
              FStar_List.fold_left
                (fun uu____3516  ->
                   fun e  ->
                     match uu____3516 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____3544 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____3544 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____3552 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____3552 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____3493 with
             | (names2,binders,n2) ->
                 let uu____3570 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____3570)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____3577 = FStar_Range.string_of_range t1.rng in
          let uu____3578 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____3577
            uu____3578 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_3584  ->
    match uu___92_3584 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____3587 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____3596 -> (hd1, "...") in
        (match uu____3587 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____3613 = FStar_Options.log_queries () in
          if uu____3613
          then
            let uu____3614 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_3617  ->
                   match uu___93_3617 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____3614
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____3631 = caption_to_string c in
          let uu____3632 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3631 f
            (FStar_String.concat " " l) uu____3632
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____3640 = name_macro_binders arg_sorts in
          (match uu____3640 with
           | (names1,binders) ->
               let body1 =
                 let uu____3658 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____3658 body in
               let uu____3666 = caption_to_string c in
               let uu____3667 = strSort retsort in
               let uu____3668 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3666
                 f (FStar_String.concat " " binders) uu____3667 uu____3668)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_3681  ->
                    match uu___94_3681 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3686 = FStar_Options.log_queries () in
            if uu____3686
            then
              let uu____3687 =
                let uu____3688 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3688 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3687
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3692 = caption_to_string a.assumption_caption in
          let uu____3693 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3692 fids
            uu____3693 n1
      | Eval t ->
          let uu____3695 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3695
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3697 -> ""
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
      let uu____3882 =
        let uu____3884 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3884
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3882 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mkBvConstructor: Prims.int -> decls_t =
  fun sz  ->
    let uu____3895 =
      let uu____3905 =
        let uu____3906 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____3906 in
      let uu____3907 =
        let uu____3912 =
          let uu____3916 =
            let uu____3917 = FStar_Util.string_of_int sz in
            FStar_Util.format1 "BoxBitVec%s_proj_0" uu____3917 in
          (uu____3916, (BitVec_sort sz), true) in
        [uu____3912] in
      (uu____3905, uu____3907, Term_sort, ((Prims.parse_int "12") + sz),
        true) in
    FStar_All.pipe_right uu____3895 constructor_to_decl
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3960 =
        let uu____3964 = let uu____3966 = mkInteger' i norng in [uu____3966] in
        ("Tm_uvar", uu____3964) in
      mkApp uu____3960 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let elim_box: Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____3988 -> mkApp (u, [t]) t.rng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____4002 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____4002 u v1 t
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
        let uu____4044 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____4044 in
      elim_box true boxOfSize (Prims.strcat boxOfSize "_proj_0") t
let unboxBitVec: Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let boxOfSize =
        let uu____4054 = FStar_Util.string_of_int sz in
        FStar_Util.format1 "BoxBitVec%s" uu____4054 in
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
      | uu____4064 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____4074 -> raise FStar_Util.Impos
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4087 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____4087
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4095 = op_to_string op in
        let uu____4096 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____4095 uu____4096
    | Labeled (t1,r1,r2) ->
        let uu____4100 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4100
    | LblPos (t1,s) ->
        let uu____4103 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4103
    | Quant (qop,l,uu____4106,uu____4107,t1) ->
        let uu____4117 = print_smt_term_list_list l in
        let uu____4118 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4117
          uu____4118
    | Let (es,body) ->
        let uu____4123 = print_smt_term_list es in
        let uu____4124 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____4123 uu____4124
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____4127 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____4127 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4140 =
             let uu____4141 =
               let uu____4142 = print_smt_term_list l1 in
               Prims.strcat uu____4142 " ] " in
             Prims.strcat "; [ " uu____4141 in
           Prims.strcat s uu____4140) "" l
let getBoxedInteger: term -> Prims.int =
  fun t  ->
    match t.tm with
    | App (Var "BoxInt",t2::[]) ->
        (match t2.tm with
         | Integer n1 -> FStar_Util.int_of_string n1
         | uu____4150 -> failwith "Not a boxed integer")
    | uu____4151 -> let uu____4152 = print_smt_term t in failwith uu____4152
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____4162::t1::t2::[]);
                       freevars = uu____4165; rng = uu____4166;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____4173::t1::t2::[]);
                       freevars = uu____4176; rng = uu____4177;_}::[])
        -> let uu____4184 = mkEq (t1, t2) norng in mkNot uu____4184 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____4187; rng = uu____4188;_}::[])
        ->
        let uu____4195 =
          let uu____4198 = unboxInt t1 in
          let uu____4199 = unboxInt t2 in (uu____4198, uu____4199) in
        mkLTE uu____4195 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____4202; rng = uu____4203;_}::[])
        ->
        let uu____4210 =
          let uu____4213 = unboxInt t1 in
          let uu____4214 = unboxInt t2 in (uu____4213, uu____4214) in
        mkLT uu____4210 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____4217; rng = uu____4218;_}::[])
        ->
        let uu____4225 =
          let uu____4228 = unboxInt t1 in
          let uu____4229 = unboxInt t2 in (uu____4228, uu____4229) in
        mkGTE uu____4225 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____4232; rng = uu____4233;_}::[])
        ->
        let uu____4240 =
          let uu____4243 = unboxInt t1 in
          let uu____4244 = unboxInt t2 in (uu____4243, uu____4244) in
        mkGT uu____4240 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____4247; rng = uu____4248;_}::[])
        ->
        let uu____4255 =
          let uu____4258 = unboxBool t1 in
          let uu____4259 = unboxBool t2 in (uu____4258, uu____4259) in
        mkAnd uu____4255 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____4262; rng = uu____4263;_}::[])
        ->
        let uu____4270 =
          let uu____4273 = unboxBool t1 in
          let uu____4274 = unboxBool t2 in (uu____4273, uu____4274) in
        mkOr uu____4270 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____4276; rng = uu____4277;_}::[])
        -> let uu____4284 = unboxBool t1 in mkNot uu____4284 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____4288; rng = uu____4289;_}::[])
        ->
        let uu____4296 =
          let uu____4299 =
            let uu____4300 = getBoxedInteger t0 in unboxBitVec uu____4300 t1 in
          let uu____4301 =
            let uu____4302 = getBoxedInteger t0 in unboxBitVec uu____4302 t2 in
          (uu____4299, uu____4301) in
        mkBvUlt uu____4296 t.rng
    | App
        (Var
         "Prims.equals",uu____4303::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____4307;
                                      rng = uu____4308;_}::uu____4309::[])
        ->
        let uu____4316 =
          let uu____4319 =
            let uu____4320 = getBoxedInteger t0 in unboxBitVec uu____4320 t1 in
          let uu____4321 =
            let uu____4322 = getBoxedInteger t0 in unboxBitVec uu____4322 t2 in
          (uu____4319, uu____4321) in
        mkBvUlt uu____4316 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_4325 = unboxBool t1 in
        {
          tm = (uu___95_4325.tm);
          freevars = (uu___95_4325.freevars);
          rng = (t.rng)
        }
    | uu____4328 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____4365 = FStar_Options.unthrottle_inductives () in
        if uu____4365
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
      let uu____4447 =
        let uu____4451 = let uu____4453 = mkInteger' i norng in [uu____4453] in
        ("FString_const", uu____4451) in
      mkApp uu____4447 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____4467 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____4467 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____4488 =
         let uu____4492 =
           let uu____4494 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____4494] in
         ("SFuel", uu____4492) in
       mkApp uu____4488 norng)
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
            let uu____4520 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____4520
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
      let uu____4560 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____4560
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____4575 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____4575
let mk_haseq: term -> term =
  fun t  ->
    let uu____4584 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____4584