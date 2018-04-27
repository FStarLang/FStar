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
    match projectee with | Integer _0 -> true | uu____440 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____452 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____468 -> false
  
let (__proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____498 -> false
  
let (__proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____546 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____618 -> false
  
let (__proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____654 -> false
  
let (__proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____688 -> false
  
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
    match projectee with | Name _0 -> true | uu____853 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____865 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____877 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1006 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1021 -> false
  
let (__proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1075 -> false
  
let (__proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1123 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1135 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1147 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1159 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1173 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1190 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1194 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1198 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1202 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1211 -> false
  
let (__proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1234 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1238 -> false
  
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
  'Auu____1258 'Auu____1259 .
    ('Auu____1258,'Auu____1259) FStar_Pervasives_Native.tuple2 ->
      'Auu____1259
  = fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1288 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___48_1295  ->
    match uu___48_1295 with
    | { tm = FreeV x; freevars = uu____1297; rng = uu____1298;_} -> fv_sort x
    | uu____1311 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___49_1314  ->
    match uu___49_1314 with
    | { tm = FreeV fv; freevars = uu____1316; rng = uu____1317;_} -> fv
    | uu____1330 -> failwith "impossible"
  
let rec (freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list) =
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
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____1418 = FStar_ST.op_Bang t.freevars  in
    match uu____1418 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1484 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1484  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___50_1527  ->
    match uu___50_1527 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___51_1530  ->
    match uu___51_1530 with
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
        let uu____1532 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1532
    | NatToBv n1 ->
        let uu____1534 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1534
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___52_1540  ->
    match uu___52_1540 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1544 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1544
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1552 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1552
    | FreeV x ->
        let uu____1558 =
          let uu____1559 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1559  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1558
    | App (op,tms) ->
        let uu____1566 =
          let uu____1567 = op_to_string op  in
          let uu____1568 =
            let uu____1569 =
              let uu____1570 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1570 (FStar_String.concat " ")  in
            Prims.strcat uu____1569 ")"  in
          Prims.strcat uu____1567 uu____1568  in
        Prims.strcat "(" uu____1566
    | Labeled (t1,r1,r2) ->
        let uu____1578 = hash_of_term t1  in
        let uu____1579 =
          let uu____1580 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1580  in
        Prims.strcat uu____1578 uu____1579
    | LblPos (t1,r) ->
        let uu____1583 =
          let uu____1584 = hash_of_term t1  in
          Prims.strcat uu____1584
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1583
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1606 =
          let uu____1607 =
            let uu____1608 =
              let uu____1609 =
                let uu____1610 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1610 (FStar_String.concat " ")  in
              let uu____1615 =
                let uu____1616 =
                  let uu____1617 = hash_of_term body  in
                  let uu____1618 =
                    let uu____1619 =
                      let uu____1620 = weightToSmt wopt  in
                      let uu____1621 =
                        let uu____1622 =
                          let uu____1623 =
                            let uu____1624 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1640 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1640
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1624
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1623 "))"  in
                        Prims.strcat " " uu____1622  in
                      Prims.strcat uu____1620 uu____1621  in
                    Prims.strcat " " uu____1619  in
                  Prims.strcat uu____1617 uu____1618  in
                Prims.strcat ")(! " uu____1616  in
              Prims.strcat uu____1609 uu____1615  in
            Prims.strcat " (" uu____1608  in
          Prims.strcat (qop_to_string qop) uu____1607  in
        Prims.strcat "(" uu____1606
    | Let (es,body) ->
        let uu____1653 =
          let uu____1654 =
            let uu____1655 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1655 (FStar_String.concat " ")  in
          let uu____1660 =
            let uu____1661 =
              let uu____1662 = hash_of_term body  in
              Prims.strcat uu____1662 ")"  in
            Prims.strcat ") " uu____1661  in
          Prims.strcat uu____1654 uu____1660  in
        Prims.strcat "(let (" uu____1653

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
    let uu____1690 =
      let uu____1691 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1691  in
    mkBoxFunctions uu____1690
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1697 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1697 = "Box") &&
        (let uu____1699 =
           let uu____1700 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1700  in
         Prims.op_Negation uu____1699)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____1717 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1717; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____1778 =
        let uu____1779 = FStar_Util.ensure_decimal i  in Integer uu____1779
         in
      mk uu____1778 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____1786 = FStar_Util.string_of_int i  in mkInteger uu____1786 r
  
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
  fun uu____1835  ->
    fun r  -> match uu____1835 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1857) -> mkFalse r
      | App (FalseOp ,uu____1862) -> mkTrue r
      | uu____1867 -> mkApp' (Not, [t]) r
  
let (mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____1878  ->
    fun r  ->
      match uu____1878 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1886),uu____1887) -> t2
           | (uu____1892,App (TrueOp ,uu____1893)) -> t1
           | (App (FalseOp ,uu____1898),uu____1899) -> mkFalse r
           | (uu____1904,App (FalseOp ,uu____1905)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1922,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1931) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1938 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____1953  ->
    fun r  ->
      match uu____1953 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1961),uu____1962) -> mkTrue r
           | (uu____1967,App (TrueOp ,uu____1968)) -> mkTrue r
           | (App (FalseOp ,uu____1973),uu____1974) -> t2
           | (uu____1979,App (FalseOp ,uu____1980)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1997,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2006) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2013 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2028  ->
    fun r  ->
      match uu____2028 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2036,App (TrueOp ,uu____2037)) -> mkTrue r
           | (App (FalseOp ,uu____2042),uu____2043) -> mkTrue r
           | (App (TrueOp ,uu____2048),uu____2049) -> t2
           | (uu____2054,App (Imp ,t1'::t2'::[])) ->
               let uu____2059 =
                 let uu____2066 =
                   let uu____2069 = mkAnd (t1, t1') r  in [uu____2069; t2']
                    in
                 (Imp, uu____2066)  in
               mkApp' uu____2059 r
           | uu____2072 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun op  ->
    fun uu____2090  ->
      fun r  -> match uu____2090 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____2189  ->
      fun r  ->
        match uu____2189 with
        | (t1,t2) ->
            let uu____2197 =
              let uu____2204 =
                let uu____2207 =
                  let uu____2210 = mkNatToBv sz t2 r  in [uu____2210]  in
                t1 :: uu____2207  in
              (BvShl, uu____2204)  in
            mkApp' uu____2197 r
  
let (mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2224  ->
      fun r  ->
        match uu____2224 with
        | (t1,t2) ->
            let uu____2232 =
              let uu____2239 =
                let uu____2242 =
                  let uu____2245 = mkNatToBv sz t2 r  in [uu____2245]  in
                t1 :: uu____2242  in
              (BvShr, uu____2239)  in
            mkApp' uu____2232 r
  
let (mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2259  ->
      fun r  ->
        match uu____2259 with
        | (t1,t2) ->
            let uu____2267 =
              let uu____2274 =
                let uu____2277 =
                  let uu____2280 = mkNatToBv sz t2 r  in [uu____2280]  in
                t1 :: uu____2277  in
              (BvUdiv, uu____2274)  in
            mkApp' uu____2267 r
  
let (mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2294  ->
      fun r  ->
        match uu____2294 with
        | (t1,t2) ->
            let uu____2302 =
              let uu____2309 =
                let uu____2312 =
                  let uu____2315 = mkNatToBv sz t2 r  in [uu____2315]  in
                t1 :: uu____2312  in
              (BvMod, uu____2309)  in
            mkApp' uu____2302 r
  
let (mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2329  ->
      fun r  ->
        match uu____2329 with
        | (t1,t2) ->
            let uu____2337 =
              let uu____2344 =
                let uu____2347 =
                  let uu____2350 = mkNatToBv sz t2 r  in [uu____2350]  in
                t1 :: uu____2347  in
              (BvMul, uu____2344)  in
            mkApp' uu____2337 r
  
let (mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvUlt 
let (mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Iff 
let (mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2377  ->
    fun r  ->
      match uu____2377 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2393 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2480  ->
    fun r  ->
      match uu____2480 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2491) -> t2
           | App (FalseOp ,uu____2496) -> t3
           | uu____2501 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2502),App (TrueOp ,uu____2503)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2512),uu____2513) ->
                    let uu____2518 =
                      let uu____2523 = mkNot t1 t1.rng  in (uu____2523, t3)
                       in
                    mkImp uu____2518 r
                | (uu____2524,App (TrueOp ,uu____2525)) -> mkImp (t1, t2) r
                | (uu____2530,uu____2531) -> mkApp' (ITE, [t1; t2; t3]) r))
  
let (mkCases : term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
  
let (check_pattern_ok : term -> term FStar_Pervasives_Native.option) =
  fun t  ->
    let rec aux t1 =
      match t1.tm with
      | Integer uu____2574 -> FStar_Pervasives_Native.None
      | BoundV uu____2575 -> FStar_Pervasives_Native.None
      | FreeV uu____2576 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____2594 -> true
            | TrueOp  -> true
            | FalseOp  -> true
            | Not  -> false
            | And  -> false
            | Or  -> false
            | Imp  -> false
            | Iff  -> false
            | Eq  -> false
            | LT  -> true
            | LTE  -> true
            | GT  -> true
            | GTE  -> true
            | Add  -> true
            | Sub  -> true
            | Div  -> true
            | Mul  -> true
            | Minus  -> true
            | Mod  -> true
            | BvAnd  -> false
            | BvXor  -> false
            | BvOr  -> false
            | BvAdd  -> false
            | BvSub  -> false
            | BvShl  -> false
            | BvShr  -> false
            | BvUdiv  -> false
            | BvMod  -> false
            | BvMul  -> false
            | BvUlt  -> false
            | BvUext uu____2595 -> false
            | NatToBv uu____2596 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____2601,uu____2602) -> aux t2
      | Quant uu____2603 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____2622 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____2636 = aux t1  in
          (match uu____2636 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____2657 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____2657
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____2669 = op_to_string op  in
        let uu____2670 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____2669 uu____2670
    | Labeled (t1,r1,r2) ->
        let uu____2674 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____2674
    | LblPos (t1,s) ->
        let uu____2677 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____2677
    | Quant (qop,l,uu____2680,uu____2681,t1) ->
        let uu____2699 = print_smt_term_list_list l  in
        let uu____2700 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____2699
          uu____2700
    | Let (es,body) ->
        let uu____2707 = print_smt_term_list es  in
        let uu____2708 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____2707 uu____2708

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____2712 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____2712 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____2731 =
             let uu____2732 =
               let uu____2733 = print_smt_term_list l1  in
               Prims.strcat uu____2733 " ] "  in
             Prims.strcat "; [ " uu____2732  in
           Prims.strcat s uu____2731) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop,term Prims.list Prims.list,Prims.int
                                        FStar_Pervasives_Native.option,
        sort Prims.list,term) FStar_Pervasives_Native.tuple5 -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____2760  ->
        match uu____2760 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____2821 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____2821 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____2836 =
                         let uu____2841 =
                           let uu____2842 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____2842
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____2841)
                          in
                       FStar_Errors.log_issue r uu____2836);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____2846) -> body
               | uu____2851 ->
                   let uu____2852 =
                     let uu____2853 =
                       let uu____2872 = all_pats_ok pats  in
                       (qop, uu____2872, wopt, vars, body)  in
                     Quant uu____2853  in
                   mk uu____2852 r)
  
let (mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____2895  ->
    fun r  ->
      match uu____2895 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____2929 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____2929 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____2948 = FStar_ST.op_Bang t1.freevars  in
        match uu____2948 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3002 ->
            (match t1.tm with
             | Integer uu____3011 -> t1
             | BoundV uu____3012 -> t1
             | FreeV x ->
                 let uu____3018 = index_of x  in
                 (match uu____3018 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3028 =
                   let uu____3035 = FStar_List.map (aux ix) tms  in
                   (op, uu____3035)  in
                 mkApp' uu____3028 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3043 =
                   let uu____3044 =
                     let uu____3051 = aux ix t2  in (uu____3051, r1, r2)  in
                   Labeled uu____3044  in
                 mk uu____3043 t2.rng
             | LblPos (t2,r) ->
                 let uu____3054 =
                   let uu____3055 =
                     let uu____3060 = aux ix t2  in (uu____3060, r)  in
                   LblPos uu____3055  in
                 mk uu____3054 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3083 =
                   let uu____3102 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3123 = aux (ix + n1) body  in
                   (qop, uu____3102, wopt, vars, uu____3123)  in
                 mkQuant t1.rng false uu____3083
             | Let (es,body) ->
                 let uu____3142 =
                   FStar_List.fold_left
                     (fun uu____3160  ->
                        fun e  ->
                          match uu____3160 with
                          | (ix1,l) ->
                              let uu____3180 =
                                let uu____3183 = aux ix1 e  in uu____3183 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3180))
                     (ix, []) es
                    in
                 (match uu____3142 with
                  | (ix1,es_rev) ->
                      let uu____3194 =
                        let uu____3201 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3201)  in
                      mkLet uu____3194 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3225 -> t1
        | FreeV uu____3226 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3243 =
              let uu____3250 = FStar_List.map (aux shift) tms2  in
              (op, uu____3250)  in
            mkApp' uu____3243 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3258 =
              let uu____3259 =
                let uu____3266 = aux shift t2  in (uu____3266, r1, r2)  in
              Labeled uu____3259  in
            mk uu____3258 t2.rng
        | LblPos (t2,r) ->
            let uu____3269 =
              let uu____3270 =
                let uu____3275 = aux shift t2  in (uu____3275, r)  in
              LblPos uu____3270  in
            mk uu____3269 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3303 =
              let uu____3322 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3339 = aux shift1 body  in
              (qop, uu____3322, wopt, vars, uu____3339)  in
            mkQuant t1.rng false uu____3303
        | Let (es,body) ->
            let uu____3354 =
              FStar_List.fold_left
                (fun uu____3372  ->
                   fun e  ->
                     match uu____3372 with
                     | (ix,es1) ->
                         let uu____3392 =
                           let uu____3395 = aux shift e  in uu____3395 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3392))
                (shift, []) es
               in
            (match uu____3354 with
             | (shift1,es_rev) ->
                 let uu____3406 =
                   let uu____3413 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3413)  in
                 mkLet uu____3406 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3425 = abstr [fv] t  in inst [s] uu____3425
  
let (mkQuant' :
  FStar_Range.range ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      fv Prims.list,term) FStar_Pervasives_Native.tuple5 -> term)
  =
  fun r  ->
    fun uu____3449  ->
      match uu____3449 with
      | (qop,pats,wopt,vars,body) ->
          let uu____3489 =
            let uu____3508 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____3525 = FStar_List.map fv_sort vars  in
            let uu____3532 = abstr vars body  in
            (qop, uu____3508, wopt, uu____3525, uu____3532)  in
          mkQuant r true uu____3489
  
let (mkForall :
  FStar_Range.range ->
    (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
      term)
  =
  fun r  ->
    fun uu____3556  ->
      match uu____3556 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple4 -> term)
  =
  fun r  ->
    fun uu____3605  ->
      match uu____3605 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      fvs,term) FStar_Pervasives_Native.tuple4 -> term)
  =
  fun r  ->
    fun uu____3669  ->
      match uu____3669 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range ->
    (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
      term)
  =
  fun r  ->
    fun uu____3721  ->
      match uu____3721 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun uu____3763  ->
    fun r  ->
      match uu____3763 with
      | (bindings,body) ->
          let uu____3789 = FStar_List.split bindings  in
          (match uu____3789 with
           | (vars,es) ->
               let uu____3808 =
                 let uu____3815 = abstr vars body  in (es, uu____3815)  in
               mkLet uu____3808 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl)
  =
  fun uu____3836  ->
    match uu____3836 with
    | (nm,vars,s,tm,c) ->
        let uu____3870 =
          let uu____3883 = FStar_List.map fv_sort vars  in
          let uu____3890 = abstr vars tm  in
          (nm, uu____3883, s, uu____3890, c)  in
        DefineFun uu____3870
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____3896 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____3896
  
let (fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl) =
  fun uu____3905  ->
    fun id1  ->
      match uu____3905 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____3915 =
              let uu____3916 =
                let uu____3921 = mkInteger' id1 norng  in
                let uu____3922 =
                  let uu____3923 =
                    let uu____3930 = constr_id_of_sort sort  in
                    let uu____3931 =
                      let uu____3934 = mkApp (tok_name, []) norng  in
                      [uu____3934]  in
                    (uu____3930, uu____3931)  in
                  mkApp uu____3923 norng  in
                (uu____3921, uu____3922)  in
              mkEq uu____3916 norng  in
            {
              assumption_term = uu____3915;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string,sort Prims.list,sort,Prims.int)
      FStar_Pervasives_Native.tuple4 -> decl)
  =
  fun rng  ->
    fun uu____3954  ->
      match uu____3954 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____3986 =
                        let uu____3991 =
                          let uu____3992 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____3992  in
                        (uu____3991, s)  in
                      mkFreeV uu____3986 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____4000 =
              let uu____4007 = constr_id_of_sort sort  in
              (uu____4007, [capp])  in
            mkApp uu____4000 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____4012 =
              let uu____4013 =
                let uu____4024 =
                  let uu____4025 =
                    let uu____4030 = mkInteger id2 norng  in
                    (uu____4030, cid_app)  in
                  mkEq uu____4025 norng  in
                ([[capp]], bvar_names, uu____4024)  in
              mkForall rng uu____4013  in
            {
              assumption_term = uu____4012;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Consrtructor distinct");
              assumption_name = a_name;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string,constructor_field Prims.list,sort)
      FStar_Pervasives_Native.tuple3 -> decls_t)
  =
  fun rng  ->
    fun uu____4054  ->
      match uu____4054 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____4075 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____4075  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____4095 = let uu____4100 = bvar_name i  in (uu____4100, s)
               in
            mkFreeV uu____4095  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____4121  ->
                      match uu____4121 with
                      | (uu____4128,s,uu____4130) ->
                          let uu____4131 = bvar i s  in uu____4131 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____4140 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____4168  ->
                      match uu____4168 with
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
                              let uu____4191 =
                                let uu____4192 =
                                  let uu____4203 =
                                    let uu____4204 =
                                      let uu____4209 =
                                        let uu____4210 = bvar i s  in
                                        uu____4210 norng  in
                                      (cproj_app, uu____4209)  in
                                    mkEq uu____4204 norng  in
                                  ([[capp]], bvar_names, uu____4203)  in
                                mkForall rng uu____4192  in
                              {
                                assumption_term = uu____4191;
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
          FStar_All.pipe_right uu____4140 FStar_List.flatten
  
let (constructor_to_decl : FStar_Range.range -> constructor_t -> decls_t) =
  fun rng  ->
    fun uu____4235  ->
      match uu____4235 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____4263  ->
                    match uu____4263 with
                    | (uu____4270,sort1,uu____4272) -> sort1))
             in
          let cdecl =
            DeclFun
              (name, field_sorts, sort,
                (FStar_Pervasives_Native.Some "Constructor"))
             in
          let cid = fresh_constructor rng (name, field_sorts, sort, id1)  in
          let disc =
            let disc_name = Prims.strcat "is-" name  in
            let xfv = ("x", sort)  in
            let xx = mkFreeV xfv norng  in
            let disc_eq =
              let uu____4290 =
                let uu____4295 =
                  let uu____4296 =
                    let uu____4303 = constr_id_of_sort sort  in
                    (uu____4303, [xx])  in
                  mkApp uu____4296 norng  in
                let uu____4306 =
                  let uu____4307 = FStar_Util.string_of_int id1  in
                  mkInteger uu____4307 norng  in
                (uu____4295, uu____4306)  in
              mkEq uu____4290 norng  in
            let uu____4308 =
              let uu____4323 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____4373  ->
                          match uu____4373 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____4403 = mkApp (proj, [xx]) norng  in
                                (uu____4403, [])
                              else
                                (let fi =
                                   let uu____4422 =
                                     let uu____4423 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____4423  in
                                   (uu____4422, s)  in
                                 let uu____4424 = mkFreeV fi norng  in
                                 (uu____4424, [fi]))))
                 in
              FStar_All.pipe_right uu____4323 FStar_List.split  in
            match uu____4308 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____4505 =
                    let uu____4510 = mkApp (name, proj_terms) norng  in
                    (xx, uu____4510)  in
                  mkEq uu____4505 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____4518 ->
                      mkExists norng ([], ex_vars1, disc_inv_body)
                   in
                let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng  in
                let def =
                  mkDefineFun
                    (disc_name, [xfv], Bool_sort, disc_ax,
                      (FStar_Pervasives_Native.Some
                         "Discriminator definition"))
                   in
                def
             in
          let projs =
            if injective1
            then injective_constructor rng (name, fields, sort)
            else []  in
          let uu____4559 =
            let uu____4562 =
              let uu____4563 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____4563  in
            uu____4562 :: cdecl :: cid :: projs  in
          let uu____4564 =
            let uu____4567 =
              let uu____4570 =
                let uu____4571 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____4571  in
              [uu____4570]  in
            FStar_List.append [disc] uu____4567  in
          FStar_List.append uu____4559 uu____4564
  
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
          let uu____4618 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4673  ->
                    fun s  ->
                      match uu____4673 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4723 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4727 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4727  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____4740 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____4740  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4618 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun sorts  ->
    let uu____4817 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____4817 with
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
              (let uu____4972 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____4972)
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
                               "Prims.guard_free",{ tm = BoundV uu____5014;
                                                    freevars = uu____5015;
                                                    rng = uu____5016;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5030 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5070 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5070 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5085 = op_to_string op  in
              let uu____5086 =
                let uu____5087 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5087 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5085 uu____5086
          | Labeled (t2,uu____5093,uu____5094) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5097 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5097 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5120 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5120 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5169 ->
                         let uu____5174 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5190 =
                                     let uu____5191 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5197 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5197) pats2
                                        in
                                     FStar_String.concat " " uu____5191  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5190))
                            in
                         FStar_All.pipe_right uu____5174
                           (FStar_String.concat "\n")
                      in
                   let uu____5200 =
                     let uu____5203 =
                       let uu____5206 =
                         let uu____5209 = aux1 n2 names2 body  in
                         let uu____5210 =
                           let uu____5213 = weightToSmt wopt  in
                           [uu____5213; pats_str; qid]  in
                         uu____5209 :: uu____5210  in
                       binders1 :: uu____5206  in
                     (qop_to_string qop) :: uu____5203  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5200)
          | Let (es,body) ->
              let uu____5220 =
                FStar_List.fold_left
                  (fun uu____5257  ->
                     fun e  ->
                       match uu____5257 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5307 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5307  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5320 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5320  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____5220 with
               | (names2,binders,n2) ->
                   let uu____5352 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5352)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5360 = FStar_Range.string_of_range t1.rng  in
            let uu____5361 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5360
              uu____5361 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___53_5367  ->
    match uu___53_5367 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c "\n")
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_ranges  ->
    fun z3options  ->
      fun decl  ->
        let escape s = FStar_Util.replace_char s 39 95  in
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Caption c ->
            let uu____5397 = FStar_Options.log_queries ()  in
            if uu____5397
            then
              let uu____5398 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___54_5402  ->
                     match uu___54_5402 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5398
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____5421 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)"
              (caption_to_string c) f (FStar_String.concat " " l) uu____5421
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5431 = name_macro_binders arg_sorts  in
            (match uu____5431 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5463 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____5463 body  in
                 let uu____5476 = strSort retsort  in
                 let uu____5477 = termToSmt print_ranges (escape f) body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   (caption_to_string c) f (FStar_String.concat " " binders)
                   uu____5476 uu____5477)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___55_5496  ->
                      match uu___55_5496 with
                      | Name n1 ->
                          let uu____5498 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____5498
                      | Namespace ns ->
                          let uu____5500 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____5500
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____5503 = FStar_Options.log_queries ()  in
              if uu____5503
              then
                let uu____5504 =
                  let uu____5505 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____5505  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5504
              else ""  in
            let n1 = escape a.assumption_name  in
            let uu____5510 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))"
              (caption_to_string a.assumption_caption) fids uu____5510 n1
        | Eval t ->
            let uu____5512 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____5512
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5514 -> ""
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
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
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
      let uu____5843 =
        let uu____5846 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____5846
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____5843 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____5861 =
      let uu____5880 =
        let uu____5881 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5881  in
      let uu____5886 =
        let uu____5895 =
          let uu____5902 =
            let uu____5903 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____5903  in
          (uu____5902, (BitVec_sort sz), true)  in
        [uu____5895]  in
      (uu____5880, uu____5886, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____5861 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : Prims.unit -> term) =
  fun uu____5961  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____5983 =
       let uu____5984 = FStar_ST.op_Bang __range_c  in
       uu____5984 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____5983);
    (let uu____6023 =
       let uu____6030 = let uu____6033 = mkInteger' i norng  in [uu____6033]
          in
       ("Range_const", uu____6030)  in
     mkApp uu____6023 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6055 =
        let uu____6062 = let uu____6065 = mkInteger' i norng  in [uu____6065]
           in
        ("Tm_uvar", uu____6062)  in
      mkApp uu____6055 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6086 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6098 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6098 u v1 t
  
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
      let uu____6123 =
        let uu____6124 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6124  in
      let uu____6129 =
        let uu____6130 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6130  in
      elim_box true uu____6123 uu____6129 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6141 =
        let uu____6142 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6142  in
      let uu____6147 =
        let uu____6148 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6148  in
      elim_box true uu____6141 uu____6147 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6160 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6168 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6183 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6183
         | uu____6184 -> FStar_Pervasives_Native.None)
    | uu____6185 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6194::t1::t2::[]);
                       freevars = uu____6197; rng = uu____6198;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6211::t1::t2::[]);
                       freevars = uu____6214; rng = uu____6215;_}::[])
        -> let uu____6228 = mkEq (t1, t2) norng  in mkNot uu____6228 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6231; rng = uu____6232;_}::[])
        ->
        let uu____6245 =
          let uu____6250 = unboxInt t1  in
          let uu____6251 = unboxInt t2  in (uu____6250, uu____6251)  in
        mkLTE uu____6245 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6254; rng = uu____6255;_}::[])
        ->
        let uu____6268 =
          let uu____6273 = unboxInt t1  in
          let uu____6274 = unboxInt t2  in (uu____6273, uu____6274)  in
        mkLT uu____6268 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6277; rng = uu____6278;_}::[])
        ->
        let uu____6291 =
          let uu____6296 = unboxInt t1  in
          let uu____6297 = unboxInt t2  in (uu____6296, uu____6297)  in
        mkGTE uu____6291 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6300; rng = uu____6301;_}::[])
        ->
        let uu____6314 =
          let uu____6319 = unboxInt t1  in
          let uu____6320 = unboxInt t2  in (uu____6319, uu____6320)  in
        mkGT uu____6314 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6323; rng = uu____6324;_}::[])
        ->
        let uu____6337 =
          let uu____6342 = unboxBool t1  in
          let uu____6343 = unboxBool t2  in (uu____6342, uu____6343)  in
        mkAnd uu____6337 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6346; rng = uu____6347;_}::[])
        ->
        let uu____6360 =
          let uu____6365 = unboxBool t1  in
          let uu____6366 = unboxBool t2  in (uu____6365, uu____6366)  in
        mkOr uu____6360 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6368; rng = uu____6369;_}::[])
        -> let uu____6382 = unboxBool t1  in mkNot uu____6382 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6386; rng = uu____6387;_}::[])
        when
        let uu____6400 = getBoxedInteger t0  in FStar_Util.is_some uu____6400
        ->
        let sz =
          let uu____6404 = getBoxedInteger t0  in
          match uu____6404 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6408 -> failwith "impossible"  in
        let uu____6411 =
          let uu____6416 = unboxBitVec sz t1  in
          let uu____6417 = unboxBitVec sz t2  in (uu____6416, uu____6417)  in
        mkBvUlt uu____6411 t.rng
    | App
        (Var
         "Prims.equals",uu____6418::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6422;
                                      rng = uu____6423;_}::uu____6424::[])
        when
        let uu____6437 = getBoxedInteger t0  in FStar_Util.is_some uu____6437
        ->
        let sz =
          let uu____6441 = getBoxedInteger t0  in
          match uu____6441 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6445 -> failwith "impossible"  in
        let uu____6448 =
          let uu____6453 = unboxBitVec sz t1  in
          let uu____6454 = unboxBitVec sz t2  in (uu____6453, uu____6454)  in
        mkBvUlt uu____6448 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___56_6458 = unboxBool t1  in
        {
          tm = (uu___56_6458.tm);
          freevars = (uu___56_6458.freevars);
          rng = (t.rng)
        }
    | uu____6459 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6492 = FStar_Options.unthrottle_inductives ()  in
        if uu____6492
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
let (kick_partial_app : term -> term) =
  fun t  ->
    let uu____6562 =
      let uu____6563 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____6563 t t.rng  in
    FStar_All.pipe_right uu____6562 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6572 =
        let uu____6579 = let uu____6582 = mkInteger' i norng  in [uu____6582]
           in
        ("FString_const", uu____6579)  in
      mkApp uu____6572 r
  
let (mk_Precedes : term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6594 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____6594 mk_Valid
  
let (mk_LexCons : term -> term -> FStar_Range.range -> term) =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6614 =
         let uu____6621 =
           let uu____6624 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____6624]  in
         ("SFuel", uu____6621)  in
       mkApp uu____6614 norng)
  
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
            let uu____6658 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____6658
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
      let uu____6711 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6711
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____6726 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6726
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____6734 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____6734
  