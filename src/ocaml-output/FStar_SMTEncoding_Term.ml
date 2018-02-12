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
  | Sort of Prims.string [@@deriving show]
let (uu___is_Bool_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____28 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____32 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____36 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____40 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____44 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____49 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____65 -> false
  
let (__proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____93 -> false
  
let (__proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____117 -> false
  
let (__proj__Sort__item___0 : sort -> Prims.string) =
  fun projectee  -> match projectee with | Sort _0 -> _0 
let rec (strSort : sort -> Prims.string) =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Fuel_sort  -> "Fuel"
    | BitVec_sort n1 ->
        let uu____129 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____129
    | Array (s1,s2) ->
        let uu____132 = strSort s1  in
        let uu____133 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____132 uu____133
    | Arrow (s1,s2) ->
        let uu____136 = strSort s1  in
        let uu____137 = strSort s2  in
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
  | Var of Prims.string [@@deriving show]
let (uu___is_TrueOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____154 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____158 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____162 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____166 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____170 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____174 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____178 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____182 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____186 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____190 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____194 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____198 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____202 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____206 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____210 -> false 
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____214 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____218 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____222 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____226 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____230 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____234 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____238 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____242 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____246 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____250 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____254 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____258 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____262 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____266 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____271 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____283 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____294 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____298 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____303 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists [@@deriving show]
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____314 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
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
  | LblPos of (term,Prims.string) FStar_Pervasives_Native.tuple2 [@@deriving
                                                                   show]
and term =
  {
  tm: term' ;
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo
    ;
  rng: FStar_Range.range }[@@deriving show]
let (uu___is_Integer : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____492 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____504 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____520 -> false
  
let (__proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____550 -> false
  
let (__proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____598 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____670 -> false
  
let (__proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____706 -> false
  
let (__proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____740 -> false
  
let (__proj__LblPos__item___0 :
  term' -> (term,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__tm
  
let (__proj__Mkterm__item__freevars :
  term ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo)
  =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__freevars
  
let (__proj__Mkterm__item__rng : term -> FStar_Range.range) =
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
  | Tag of Prims.string [@@deriving show]
let (uu___is_Name : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____983 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____995 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1007 -> false
  
let (__proj__Tag__item___0 : fact_db_id -> Prims.string) =
  fun projectee  -> match projectee with | Tag _0 -> _0 
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list }[@@deriving show]
let (__proj__Mkassumption__item__assumption_term : assumption -> term) =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_term
  
let (__proj__Mkassumption__item__assumption_caption : assumption -> caption)
  =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_caption
  
let (__proj__Mkassumption__item__assumption_name :
  assumption -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_name
  
let (__proj__Mkassumption__item__assumption_fact_ids :
  assumption -> fact_db_id Prims.list) =
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
  | GetReasonUnknown [@@deriving show]
let (uu___is_DefPrelude : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1136 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1151 -> false
  
let (__proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1205 -> false
  
let (__proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1253 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1265 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1277 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1289 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1303 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1320 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1324 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1328 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1332 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1341 -> false
  
let (__proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1364 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1368 -> false
  
type decls_t = decl Prims.list[@@deriving show]
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type error_labels = error_label Prims.list[@@deriving show]
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____1388 'Auu____1389 .
    ('Auu____1389,'Auu____1388) FStar_Pervasives_Native.tuple2 ->
      'Auu____1388
  = fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1418 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___46_1425  ->
    match uu___46_1425 with
    | { tm = FreeV x; freevars = uu____1427; rng = uu____1428;_} -> fv_sort x
    | uu____1441 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___47_1444  ->
    match uu___47_1444 with
    | { tm = FreeV fv; freevars = uu____1446; rng = uu____1447;_} -> fv
    | uu____1460 -> failwith "impossible"
  
let rec (freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____1476 -> []
    | BoundV uu____1481 -> []
    | FreeV fv -> [fv]
    | App (uu____1499,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1509,uu____1510,uu____1511,uu____1512,t1) -> freevars t1
    | Labeled (t1,uu____1531,uu____1532) -> freevars t1
    | LblPos (t1,uu____1534) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____1548 = FStar_ST.op_Bang t.freevars  in
    match uu____1548 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1614 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1614  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___48_1657  ->
    match uu___48_1657 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___49_1660  ->
    match uu___49_1660 with
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
        let uu____1662 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1662
    | NatToBv n1 ->
        let uu____1664 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1664
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___50_1670  ->
    match uu___50_1670 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1674 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1674
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1682 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1682
    | FreeV x ->
        let uu____1688 =
          let uu____1689 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1689  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1688
    | App (op,tms) ->
        let uu____1696 =
          let uu____1697 = op_to_string op  in
          let uu____1698 =
            let uu____1699 =
              let uu____1700 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1700 (FStar_String.concat " ")  in
            Prims.strcat uu____1699 ")"  in
          Prims.strcat uu____1697 uu____1698  in
        Prims.strcat "(" uu____1696
    | Labeled (t1,r1,r2) ->
        let uu____1708 = hash_of_term t1  in
        let uu____1709 =
          let uu____1710 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1710  in
        Prims.strcat uu____1708 uu____1709
    | LblPos (t1,r) ->
        let uu____1713 =
          let uu____1714 = hash_of_term t1  in
          Prims.strcat uu____1714
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1713
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1736 =
          let uu____1737 =
            let uu____1738 =
              let uu____1739 =
                let uu____1740 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1740 (FStar_String.concat " ")  in
              let uu____1745 =
                let uu____1746 =
                  let uu____1747 = hash_of_term body  in
                  let uu____1748 =
                    let uu____1749 =
                      let uu____1750 = weightToSmt wopt  in
                      let uu____1751 =
                        let uu____1752 =
                          let uu____1753 =
                            let uu____1754 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1770 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1770
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1754
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1753 "))"  in
                        Prims.strcat " " uu____1752  in
                      Prims.strcat uu____1750 uu____1751  in
                    Prims.strcat " " uu____1749  in
                  Prims.strcat uu____1747 uu____1748  in
                Prims.strcat ")(! " uu____1746  in
              Prims.strcat uu____1739 uu____1745  in
            Prims.strcat " (" uu____1738  in
          Prims.strcat (qop_to_string qop) uu____1737  in
        Prims.strcat "(" uu____1736
    | Let (es,body) ->
        let uu____1783 =
          let uu____1784 =
            let uu____1785 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1785 (FStar_String.concat " ")  in
          let uu____1790 =
            let uu____1791 =
              let uu____1792 = hash_of_term body  in
              Prims.strcat uu____1792 ")"  in
            Prims.strcat ") " uu____1791  in
          Prims.strcat uu____1784 uu____1790  in
        Prims.strcat "(let (" uu____1783

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions :
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
  = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2)
  = mkBoxFunctions "BoxBool" 
let (boxStringFun :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun :
  Prims.int -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun sz  ->
    let uu____1820 =
      let uu____1821 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1821  in
    mkBoxFunctions uu____1820
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1827 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1827 = "Box") &&
        (let uu____1829 =
           let uu____1830 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1830  in
         Prims.op_Negation uu____1829)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____1847 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1847; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____1960 =
        let uu____1961 = FStar_Util.ensure_decimal i  in Integer uu____1961
         in
      mk uu____1960 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____1968 = FStar_Util.string_of_int i  in mkInteger uu____1968 r
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  = fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' :
  (op,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  = fun f  -> fun r  -> mk (App f) r 
let (mkApp :
  (Prims.string,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____2017  ->
    fun r  -> match uu____2017 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2039) -> mkFalse r
      | App (FalseOp ,uu____2044) -> mkTrue r
      | uu____2049 -> mkApp' (Not, [t]) r
  
let (mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2060  ->
    fun r  ->
      match uu____2060 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2068),uu____2069) -> t2
           | (uu____2074,App (TrueOp ,uu____2075)) -> t1
           | (App (FalseOp ,uu____2080),uu____2081) -> mkFalse r
           | (uu____2086,App (FalseOp ,uu____2087)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2104,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2113) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2120 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2135  ->
    fun r  ->
      match uu____2135 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2143),uu____2144) -> mkTrue r
           | (uu____2149,App (TrueOp ,uu____2150)) -> mkTrue r
           | (App (FalseOp ,uu____2155),uu____2156) -> t2
           | (uu____2161,App (FalseOp ,uu____2162)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2179,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2188) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2195 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2210  ->
    fun r  ->
      match uu____2210 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2218,App (TrueOp ,uu____2219)) -> mkTrue r
           | (App (FalseOp ,uu____2224),uu____2225) -> mkTrue r
           | (App (TrueOp ,uu____2230),uu____2231) -> t2
           | (uu____2236,App (Imp ,t1'::t2'::[])) ->
               let uu____2241 =
                 let uu____2248 =
                   let uu____2251 = mkAnd (t1, t1') r  in [uu____2251; t2']
                    in
                 (Imp, uu____2248)  in
               mkApp' uu____2241 r
           | uu____2254 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun op  ->
    fun uu____2272  ->
      fun r  -> match uu____2272 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
let (mkMinus : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r 
let (mkNatToBv : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz  -> fun t  -> fun r  -> mkApp' ((NatToBv sz), [t]) r 
let (mkBvUext : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz  -> fun t  -> fun r  -> mkApp' ((BvUext sz), [t]) r 
let (mkBvToNat : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp' (BvToNat, [t]) r 
let (mkBvAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvAnd 
let (mkBvXor :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvXor 
let (mkBvOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvOr 
let (mkBvAdd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvAdd 
let (mkBvSub :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvSub 
let (mkBvShl :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2371  ->
      fun r  ->
        match uu____2371 with
        | (t1,t2) ->
            let uu____2379 =
              let uu____2386 =
                let uu____2389 =
                  let uu____2392 = mkNatToBv sz t2 r  in [uu____2392]  in
                t1 :: uu____2389  in
              (BvShl, uu____2386)  in
            mkApp' uu____2379 r
  
let (mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2406  ->
      fun r  ->
        match uu____2406 with
        | (t1,t2) ->
            let uu____2414 =
              let uu____2421 =
                let uu____2424 =
                  let uu____2427 = mkNatToBv sz t2 r  in [uu____2427]  in
                t1 :: uu____2424  in
              (BvShr, uu____2421)  in
            mkApp' uu____2414 r
  
let (mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2441  ->
      fun r  ->
        match uu____2441 with
        | (t1,t2) ->
            let uu____2449 =
              let uu____2456 =
                let uu____2459 =
                  let uu____2462 = mkNatToBv sz t2 r  in [uu____2462]  in
                t1 :: uu____2459  in
              (BvUdiv, uu____2456)  in
            mkApp' uu____2449 r
  
let (mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2476  ->
      fun r  ->
        match uu____2476 with
        | (t1,t2) ->
            let uu____2484 =
              let uu____2491 =
                let uu____2494 =
                  let uu____2497 = mkNatToBv sz t2 r  in [uu____2497]  in
                t1 :: uu____2494  in
              (BvMod, uu____2491)  in
            mkApp' uu____2484 r
  
let (mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2511  ->
      fun r  ->
        match uu____2511 with
        | (t1,t2) ->
            let uu____2519 =
              let uu____2526 =
                let uu____2529 =
                  let uu____2532 = mkNatToBv sz t2 r  in [uu____2532]  in
                t1 :: uu____2529  in
              (BvMul, uu____2526)  in
            mkApp' uu____2519 r
  
let (mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvUlt 
let (mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Iff 
let (mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2559  ->
    fun r  ->
      match uu____2559 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2575 -> mk_bin_op Eq (t1, t2) r)
  
let (mkLT :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op LT 
let (mkLTE :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op LTE 
let (mkGT :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op GT 
let (mkGTE :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op GTE 
let (mkAdd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Add 
let (mkSub :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Sub 
let (mkDiv :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Div 
let (mkMul :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Mul 
let (mkMod :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Mod 
let (mkITE :
  (term,term,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____2662  ->
    fun r  ->
      match uu____2662 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2673) -> t2
           | App (FalseOp ,uu____2678) -> t3
           | uu____2683 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2684),App (TrueOp ,uu____2685)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2694),uu____2695) ->
                    let uu____2700 =
                      let uu____2705 = mkNot t1 t1.rng  in (uu____2705, t3)
                       in
                    mkImp uu____2700 r
                | (uu____2706,App (TrueOp ,uu____2707)) -> mkImp (t1, t2) r
                | (uu____2712,uu____2713) -> mkApp' (ITE, [t1; t2; t3]) r))
  
let (mkCases : term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
  
let (mkQuant :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term)
  =
  fun uu____2756  ->
    fun r  ->
      match uu____2756 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2798) -> body
             | uu____2803 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let (mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____2822  ->
    fun r  ->
      match uu____2822 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____2856 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____2856 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____2875 = FStar_ST.op_Bang t1.freevars  in
        match uu____2875 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2929 ->
            (match t1.tm with
             | Integer uu____2938 -> t1
             | BoundV uu____2939 -> t1
             | FreeV x ->
                 let uu____2945 = index_of x  in
                 (match uu____2945 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2955 =
                   let uu____2962 = FStar_List.map (aux ix) tms  in
                   (op, uu____2962)  in
                 mkApp' uu____2955 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2970 =
                   let uu____2971 =
                     let uu____2978 = aux ix t2  in (uu____2978, r1, r2)  in
                   Labeled uu____2971  in
                 mk uu____2970 t2.rng
             | LblPos (t2,r) ->
                 let uu____2981 =
                   let uu____2982 =
                     let uu____2987 = aux ix t2  in (uu____2987, r)  in
                   LblPos uu____2982  in
                 mk uu____2981 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3010 =
                   let uu____3029 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3050 = aux (ix + n1) body  in
                   (qop, uu____3029, wopt, vars, uu____3050)  in
                 mkQuant uu____3010 t1.rng
             | Let (es,body) ->
                 let uu____3069 =
                   FStar_List.fold_left
                     (fun uu____3087  ->
                        fun e  ->
                          match uu____3087 with
                          | (ix1,l) ->
                              let uu____3107 =
                                let uu____3110 = aux ix1 e  in uu____3110 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3107))
                     (ix, []) es
                    in
                 (match uu____3069 with
                  | (ix1,es_rev) ->
                      let uu____3121 =
                        let uu____3128 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3128)  in
                      mkLet uu____3121 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3152 -> t1
        | FreeV uu____3153 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3170 =
              let uu____3177 = FStar_List.map (aux shift) tms2  in
              (op, uu____3177)  in
            mkApp' uu____3170 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3185 =
              let uu____3186 =
                let uu____3193 = aux shift t2  in (uu____3193, r1, r2)  in
              Labeled uu____3186  in
            mk uu____3185 t2.rng
        | LblPos (t2,r) ->
            let uu____3196 =
              let uu____3197 =
                let uu____3202 = aux shift t2  in (uu____3202, r)  in
              LblPos uu____3197  in
            mk uu____3196 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3230 =
              let uu____3249 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3266 = aux shift1 body  in
              (qop, uu____3249, wopt, vars, uu____3266)  in
            mkQuant uu____3230 t1.rng
        | Let (es,body) ->
            let uu____3281 =
              FStar_List.fold_left
                (fun uu____3299  ->
                   fun e  ->
                     match uu____3299 with
                     | (ix,es1) ->
                         let uu____3319 =
                           let uu____3322 = aux shift e  in uu____3322 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3319))
                (shift, []) es
               in
            (match uu____3281 with
             | (shift1,es_rev) ->
                 let uu____3333 =
                   let uu____3340 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3340)  in
                 mkLet uu____3333 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3352 = abstr [fv] t  in inst [s] uu____3352
  
let (mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term)
  =
  fun uu____3375  ->
    match uu____3375 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3417 =
          let uu____3436 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3453 = FStar_List.map fv_sort vars  in
          let uu____3460 = abstr vars body  in
          (qop, uu____3436, wopt, uu____3453, uu____3460)  in
        mkQuant uu____3417
  
let (mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term)
  =
  fun uu____3489  ->
    fun r  ->
      match uu____3489 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let (mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term)
  =
  fun uu____3553  ->
    fun r  ->
      match uu____3553 with
      | (pats,wopt,vars,body) ->
          let uu____3585 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3585 r
  
let (mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3608  ->
    fun r  ->
      match uu____3608 with
      | (pats,vars,body) ->
          let uu____3631 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3631 r
  
let (mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3654  ->
    fun r  ->
      match uu____3654 with
      | (pats,vars,body) ->
          let uu____3677 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3677 r
  
let (mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun uu____3700  ->
    fun r  ->
      match uu____3700 with
      | (bindings,body) ->
          let uu____3726 = FStar_List.split bindings  in
          (match uu____3726 with
           | (vars,es) ->
               let uu____3745 =
                 let uu____3752 = abstr vars body  in (es, uu____3752)  in
               mkLet uu____3745 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl)
  =
  fun uu____3773  ->
    match uu____3773 with
    | (nm,vars,s,tm,c) ->
        let uu____3807 =
          let uu____3820 = FStar_List.map fv_sort vars  in
          let uu____3827 = abstr vars tm  in
          (nm, uu____3820, s, uu____3827, c)  in
        DefineFun uu____3807
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____3833 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____3833
  
let (fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl) =
  fun uu____3842  ->
    fun id1  ->
      match uu____3842 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____3852 =
              let uu____3853 =
                let uu____3858 = mkInteger' id1 norng  in
                let uu____3859 =
                  let uu____3860 =
                    let uu____3867 = constr_id_of_sort sort  in
                    let uu____3868 =
                      let uu____3871 = mkApp (tok_name, []) norng  in
                      [uu____3871]  in
                    (uu____3867, uu____3868)  in
                  mkApp uu____3860 norng  in
                (uu____3858, uu____3859)  in
              mkEq uu____3853 norng  in
            {
              assumption_term = uu____3852;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  (Prims.string,sort Prims.list,sort,Prims.int)
    FStar_Pervasives_Native.tuple4 -> decl)
  =
  fun uu____3888  ->
    match uu____3888 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3920 =
                      let uu____3925 =
                        let uu____3926 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____3926  in
                      (uu____3925, s)  in
                    mkFreeV uu____3920 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____3934 =
            let uu____3941 = constr_id_of_sort sort  in (uu____3941, [capp])
             in
          mkApp uu____3934 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____3946 =
            let uu____3947 =
              let uu____3958 =
                let uu____3959 =
                  let uu____3964 = mkInteger id2 norng  in
                  (uu____3964, cid_app)  in
                mkEq uu____3959 norng  in
              ([[capp]], bvar_names, uu____3958)  in
            mkForall uu____3947 norng  in
          {
            assumption_term = uu____3946;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          }  in
        Assume a
  
let (injective_constructor :
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decls_t)
  =
  fun uu____3985  ->
    match uu____3985 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____4006 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____4006  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____4026 = let uu____4031 = bvar_name i  in (uu____4031, s)
             in
          mkFreeV uu____4026  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4052  ->
                    match uu____4052 with
                    | (uu____4059,s,uu____4061) ->
                        let uu____4062 = bvar i s  in uu____4062 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____4071 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4099  ->
                    match uu____4099 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng  in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector"))
                           in
                        if projectible
                        then
                          let a =
                            let uu____4122 =
                              let uu____4123 =
                                let uu____4134 =
                                  let uu____4135 =
                                    let uu____4140 =
                                      let uu____4141 = bvar i s  in
                                      uu____4141 norng  in
                                    (cproj_app, uu____4140)  in
                                  mkEq uu____4135 norng  in
                                ([[capp]], bvar_names, uu____4134)  in
                              mkForall uu____4123 norng  in
                            {
                              assumption_term = uu____4122;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            }  in
                          [proj_name; Assume a]
                        else [proj_name]))
           in
        FStar_All.pipe_right uu____4071 FStar_List.flatten
  
let (constructor_to_decl : constructor_t -> decls_t) =
  fun uu____4163  ->
    match uu____4163 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4191  ->
                  match uu____4191 with
                  | (uu____4198,sort1,uu____4200) -> sort1))
           in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor"))
           in
        let cid = fresh_constructor (name, field_sorts, sort, id1)  in
        let disc =
          let disc_name = Prims.strcat "is-" name  in
          let xfv = ("x", sort)  in
          let xx = mkFreeV xfv norng  in
          let disc_eq =
            let uu____4218 =
              let uu____4223 =
                let uu____4224 =
                  let uu____4231 = constr_id_of_sort sort  in
                  (uu____4231, [xx])  in
                mkApp uu____4224 norng  in
              let uu____4234 =
                let uu____4235 = FStar_Util.string_of_int id1  in
                mkInteger uu____4235 norng  in
              (uu____4223, uu____4234)  in
            mkEq uu____4218 norng  in
          let uu____4236 =
            let uu____4251 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4301  ->
                        match uu____4301 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4331 = mkApp (proj, [xx]) norng  in
                              (uu____4331, [])
                            else
                              (let fi =
                                 let uu____4350 =
                                   let uu____4351 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4351  in
                                 (uu____4350, s)  in
                               let uu____4352 = mkFreeV fi norng  in
                               (uu____4352, [fi]))))
               in
            FStar_All.pipe_right uu____4251 FStar_List.split  in
          match uu____4236 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4433 =
                  let uu____4438 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4438)  in
                mkEq uu____4433 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4446 -> mkExists ([], ex_vars1, disc_inv_body) norng
                 in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng  in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (FStar_Pervasives_Native.Some "Discriminator definition"))
                 in
              def
           in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else []  in
        let uu____4487 =
          let uu____4490 =
            let uu____4491 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4491  in
          uu____4490 :: cdecl :: cid :: projs  in
        let uu____4492 =
          let uu____4495 =
            let uu____4498 =
              let uu____4499 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4499  in
            [uu____4498]  in
          FStar_List.append [disc] uu____4495  in
        FStar_List.append uu____4487 uu____4492
  
let (name_binders_inner :
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
            Prims.string Prims.list,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____4546 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4601  ->
                    fun s  ->
                      match uu____4601 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4651 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4655 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4655  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____4668 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____4668  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4546 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun sorts  ->
    let uu____4745 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____4745 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
          fun depth  ->
            let n1 = FStar_ST.op_Bang ctr  in
            FStar_Util.incr ctr;
            if n1 = (Prims.parse_int "0")
            then enclosing_name
            else
              (let uu____5030 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5030)
           in
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
                               "Prims.guard_free",{ tm = BoundV uu____5072;
                                                    freevars = uu____5073;
                                                    rng = uu____5074;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5088 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5128 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5128 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5143 = op_to_string op  in
              let uu____5144 =
                let uu____5145 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5145 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5143 uu____5144
          | Labeled (t2,uu____5151,uu____5152) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5155 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5155 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5178 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5178 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5227 ->
                         let uu____5232 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5248 =
                                     let uu____5249 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5255 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5255) pats2
                                        in
                                     FStar_String.concat " " uu____5249  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5248))
                            in
                         FStar_All.pipe_right uu____5232
                           (FStar_String.concat "\n")
                      in
                   let uu____5258 =
                     let uu____5261 =
                       let uu____5264 =
                         let uu____5267 = aux1 n2 names2 body  in
                         let uu____5268 =
                           let uu____5271 = weightToSmt wopt  in
                           [uu____5271; pats_str; qid]  in
                         uu____5267 :: uu____5268  in
                       binders1 :: uu____5264  in
                     (qop_to_string qop) :: uu____5261  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5258)
          | Let (es,body) ->
              let uu____5278 =
                FStar_List.fold_left
                  (fun uu____5315  ->
                     fun e  ->
                       match uu____5315 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5365 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5365  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5378 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5378  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____5278 with
               | (names2,binders,n2) ->
                   let uu____5410 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5410)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5418 = FStar_Range.string_of_range t1.rng  in
            let uu____5419 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5418
              uu____5419 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___51_5425  ->
    match uu___51_5425 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5429 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5444 -> (hd1, "...")  in
        (match uu____5429 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_ranges  ->
    fun z3options  ->
      fun decl  ->
        let escape s = FStar_Util.replace_char s 39 95  in
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Caption c ->
            let uu____5475 = FStar_Options.log_queries ()  in
            if uu____5475
            then
              let uu____5476 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___52_5480  ->
                     match uu___52_5480 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5476
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____5499 = caption_to_string c  in
            let uu____5500 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5499 f
              (FStar_String.concat " " l) uu____5500
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5510 = name_macro_binders arg_sorts  in
            (match uu____5510 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5542 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____5542 body  in
                 let uu____5555 = caption_to_string c  in
                 let uu____5556 = strSort retsort  in
                 let uu____5557 = termToSmt print_ranges (escape f) body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5555 f (FStar_String.concat " " binders) uu____5556
                   uu____5557)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___53_5575  ->
                      match uu___53_5575 with
                      | Name n1 ->
                          Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                      | Namespace ns ->
                          Prims.strcat "Namespace "
                            (FStar_Ident.text_of_lid ns)
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____5580 = FStar_Options.log_queries ()  in
              if uu____5580
              then
                let uu____5581 =
                  let uu____5582 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____5582  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5581
              else ""  in
            let n1 = escape a.assumption_name  in
            let uu____5587 = caption_to_string a.assumption_caption  in
            let uu____5588 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5587
              fids uu____5588 n1
        | Eval t ->
            let uu____5590 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____5590
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5592 -> ""
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

and (declToSmt : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' true z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
       in
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
        Term_sort, (Prims.parse_int "11"), true)]
       in
    let bcons =
      let uu____5921 =
        let uu____5924 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____5924
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____5921 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____5939 =
      let uu____5958 =
        let uu____5959 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5959  in
      let uu____5964 =
        let uu____5973 =
          let uu____5980 =
            let uu____5981 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____5981  in
          (uu____5980, (BitVec_sort sz), true)  in
        [uu____5973]  in
      (uu____5958, uu____5964, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____5939 constructor_to_decl
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : Prims.unit -> term) =
  fun uu____6065  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____6087 =
       let uu____6088 = FStar_ST.op_Bang __range_c  in
       uu____6088 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____6087);
    (let uu____6127 =
       let uu____6134 = let uu____6137 = mkInteger' i norng  in [uu____6137]
          in
       ("Range_const", uu____6134)  in
     mkApp uu____6127 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6159 =
        let uu____6166 = let uu____6169 = mkInteger' i norng  in [uu____6169]
           in
        ("Tm_uvar", uu____6166)  in
      mkApp uu____6159 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6190 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6202 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6202 u v1 t
  
let (boxInt : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun)
      (FStar_Pervasives_Native.snd boxIntFun) t
  
let (unboxInt : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun)
      (FStar_Pervasives_Native.fst boxIntFun) t
  
let (boxBool : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun)
      (FStar_Pervasives_Native.snd boxBoolFun) t
  
let (unboxBool : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun)
      (FStar_Pervasives_Native.fst boxBoolFun) t
  
let (boxString : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun)
      (FStar_Pervasives_Native.snd boxStringFun) t
  
let (unboxString : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun)
      (FStar_Pervasives_Native.fst boxStringFun) t
  
let (boxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6227 =
        let uu____6228 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6228  in
      let uu____6233 =
        let uu____6234 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6234  in
      elim_box true uu____6227 uu____6233 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6245 =
        let uu____6246 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6246  in
      let uu____6251 =
        let uu____6252 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6252  in
      elim_box true uu____6245 uu____6251 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6264 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6272 -> FStar_Exn.raise FStar_Util.Impos
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6288 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____6288
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6300 = op_to_string op  in
        let uu____6301 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____6300 uu____6301
    | Labeled (t1,r1,r2) ->
        let uu____6305 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6305
    | LblPos (t1,s) ->
        let uu____6308 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6308
    | Quant (qop,l,uu____6311,uu____6312,t1) ->
        let uu____6330 = print_smt_term_list_list l  in
        let uu____6331 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6330
          uu____6331
    | Let (es,body) ->
        let uu____6338 = print_smt_term_list es  in
        let uu____6339 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____6338 uu____6339

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____6343 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____6343 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6362 =
             let uu____6363 =
               let uu____6364 = print_smt_term_list l1  in
               Prims.strcat uu____6364 " ] "  in
             Prims.strcat "; [ " uu____6363  in
           Prims.strcat s uu____6362) "" l

let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6379 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6379
         | uu____6380 -> FStar_Pervasives_Native.None)
    | uu____6381 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6390::t1::t2::[]);
                       freevars = uu____6393; rng = uu____6394;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6407::t1::t2::[]);
                       freevars = uu____6410; rng = uu____6411;_}::[])
        -> let uu____6424 = mkEq (t1, t2) norng  in mkNot uu____6424 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6427; rng = uu____6428;_}::[])
        ->
        let uu____6441 =
          let uu____6446 = unboxInt t1  in
          let uu____6447 = unboxInt t2  in (uu____6446, uu____6447)  in
        mkLTE uu____6441 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6450; rng = uu____6451;_}::[])
        ->
        let uu____6464 =
          let uu____6469 = unboxInt t1  in
          let uu____6470 = unboxInt t2  in (uu____6469, uu____6470)  in
        mkLT uu____6464 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6473; rng = uu____6474;_}::[])
        ->
        let uu____6487 =
          let uu____6492 = unboxInt t1  in
          let uu____6493 = unboxInt t2  in (uu____6492, uu____6493)  in
        mkGTE uu____6487 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6496; rng = uu____6497;_}::[])
        ->
        let uu____6510 =
          let uu____6515 = unboxInt t1  in
          let uu____6516 = unboxInt t2  in (uu____6515, uu____6516)  in
        mkGT uu____6510 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6519; rng = uu____6520;_}::[])
        ->
        let uu____6533 =
          let uu____6538 = unboxBool t1  in
          let uu____6539 = unboxBool t2  in (uu____6538, uu____6539)  in
        mkAnd uu____6533 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6542; rng = uu____6543;_}::[])
        ->
        let uu____6556 =
          let uu____6561 = unboxBool t1  in
          let uu____6562 = unboxBool t2  in (uu____6561, uu____6562)  in
        mkOr uu____6556 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6564; rng = uu____6565;_}::[])
        -> let uu____6578 = unboxBool t1  in mkNot uu____6578 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6582; rng = uu____6583;_}::[])
        when
        let uu____6596 = getBoxedInteger t0  in FStar_Util.is_some uu____6596
        ->
        let sz =
          let uu____6600 = getBoxedInteger t0  in
          match uu____6600 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6604 -> failwith "impossible"  in
        let uu____6607 =
          let uu____6612 = unboxBitVec sz t1  in
          let uu____6613 = unboxBitVec sz t2  in (uu____6612, uu____6613)  in
        mkBvUlt uu____6607 t.rng
    | App
        (Var
         "Prims.equals",uu____6614::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6618;
                                      rng = uu____6619;_}::uu____6620::[])
        when
        let uu____6633 = getBoxedInteger t0  in FStar_Util.is_some uu____6633
        ->
        let sz =
          let uu____6637 = getBoxedInteger t0  in
          match uu____6637 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6641 -> failwith "impossible"  in
        let uu____6644 =
          let uu____6649 = unboxBitVec sz t1  in
          let uu____6650 = unboxBitVec sz t2  in (uu____6649, uu____6650)  in
        mkBvUlt uu____6644 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___54_6654 = unboxBool t1  in
        {
          tm = (uu___54_6654.tm);
          freevars = (uu___54_6654.freevars);
          rng = (t.rng)
        }
    | uu____6655 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6688 = FStar_Options.unthrottle_inductives ()  in
        if uu____6688
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
  
let (mk_HasTypeWithFuel :
  term FStar_Pervasives_Native.option -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | FStar_Pervasives_Native.None  -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
  
let (mk_NoHoist : term -> term -> term) =
  fun dummy  -> fun b  -> mkApp ("NoHoist", [dummy; b]) b.rng 
let (mk_Destruct : term -> FStar_Range.range -> term) =
  fun v1  -> mkApp ("Destruct", [v1]) 
let (mk_Rank : term -> FStar_Range.range -> term) =
  fun x  -> mkApp ("Rank", [x]) 
let (mk_tester : Prims.string -> term -> term) =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng 
let (mk_ApplyTF : term -> term -> term) =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng 
let (mk_ApplyTT : term -> term -> FStar_Range.range -> term) =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r 
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6761 =
        let uu____6768 = let uu____6771 = mkInteger' i norng  in [uu____6771]
           in
        ("FString_const", uu____6768)  in
      mkApp uu____6761 r
  
let (mk_Precedes : term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6783 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____6783 mk_Valid
  
let (mk_LexCons : term -> term -> FStar_Range.range -> term) =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6803 =
         let uu____6810 =
           let uu____6813 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____6813]  in
         ("SFuel", uu____6810)  in
       mkApp uu____6803 norng)
  
let (fuel_2 : term) = n_fuel (Prims.parse_int "2") 
let (fuel_100 : term) = n_fuel (Prims.parse_int "100") 
let (mk_and_opt :
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option ->
      FStar_Range.range -> term FStar_Pervasives_Native.option)
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (FStar_Pervasives_Native.Some p11,FStar_Pervasives_Native.Some p21)
            ->
            let uu____6847 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____6847
        | (FStar_Pervasives_Native.Some p,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.None
  
let (mk_and_opt_l :
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option)
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
  
let (mk_and_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____6900 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6900
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____6915 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6915
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____6923 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____6923
  