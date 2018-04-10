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
    match projectee with | Bool_sort  -> true | uu____30 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____36 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____42 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____48 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____54 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____61 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____79 -> false
  
let (__proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____109 -> false
  
let (__proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____135 -> false
  
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
        let uu____149 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____149
    | Array (s1,s2) ->
        let uu____152 = strSort s1  in
        let uu____153 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____152 uu____153
    | Arrow (s1,s2) ->
        let uu____156 = strSort s1  in
        let uu____157 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____156 uu____157
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
    match projectee with | TrueOp  -> true | uu____176 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____182 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____188 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____194 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____200 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____206 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____212 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____218 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____224 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____230 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____236 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____242 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____248 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____254 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____260 -> false 
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____266 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____272 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____278 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____284 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____290 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____296 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____302 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____308 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____314 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____320 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____326 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____332 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____338 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____344 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____351 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____365 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____378 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____384 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____391 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists [@@deriving show]
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____404 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____410 -> false
  
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
    match projectee with | Integer _0 -> true | uu____534 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____548 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____566 -> false
  
let (__proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____598 -> false
  
let (__proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____648 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____722 -> false
  
let (__proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____760 -> false
  
let (__proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____796 -> false
  
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
    match projectee with | Name _0 -> true | uu____969 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____983 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____997 -> false
  
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
    match projectee with | DeclFun _0 -> true | uu____1153 -> false
  
let (__proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1209 -> false
  
let (__proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1259 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1273 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1287 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1301 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1317 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1336 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1342 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1348 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1354 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1365 -> false
  
let (__proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1390 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1396 -> false
  
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
  'Auu____1423 'Auu____1424 .
    ('Auu____1423,'Auu____1424) FStar_Pervasives_Native.tuple2 ->
      'Auu____1424
  = fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1458 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___48_1467  ->
    match uu___48_1467 with
    | { tm = FreeV x; freevars = uu____1469; rng = uu____1470;_} -> fv_sort x
    | uu____1483 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___49_1488  ->
    match uu___49_1488 with
    | { tm = FreeV fv; freevars = uu____1490; rng = uu____1491;_} -> fv
    | uu____1504 -> failwith "impossible"
  
let rec (freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____1522 -> []
    | BoundV uu____1527 -> []
    | FreeV fv -> [fv]
    | App (uu____1545,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1555,uu____1556,uu____1557,uu____1558,t1) -> freevars t1
    | Labeled (t1,uu____1577,uu____1578) -> freevars t1
    | LblPos (t1,uu____1580) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____1596 = FStar_ST.op_Bang t.freevars  in
    match uu____1596 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1666 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1666  in
        let uu____1669 =
          FStar_ST.op_Colon_Equals t.freevars
            (FStar_Pervasives_Native.Some fvs)
           in
        fvs
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___50_1715  ->
    match uu___50_1715 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___51_1720  ->
    match uu___51_1720 with
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
        let uu____1722 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1722
    | NatToBv n1 ->
        let uu____1724 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1724
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___52_1732  ->
    match uu___52_1732 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1736 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1736
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1748 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1748
    | FreeV x ->
        let uu____1754 =
          let uu____1755 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1755  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1754
    | App (op,tms) ->
        let uu____1762 =
          let uu____1763 = op_to_string op  in
          let uu____1764 =
            let uu____1765 =
              let uu____1766 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1766 (FStar_String.concat " ")  in
            Prims.strcat uu____1765 ")"  in
          Prims.strcat uu____1763 uu____1764  in
        Prims.strcat "(" uu____1762
    | Labeled (t1,r1,r2) ->
        let uu____1774 = hash_of_term t1  in
        let uu____1775 =
          let uu____1776 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1776  in
        Prims.strcat uu____1774 uu____1775
    | LblPos (t1,r) ->
        let uu____1779 =
          let uu____1780 = hash_of_term t1  in
          Prims.strcat uu____1780
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1779
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1802 =
          let uu____1803 =
            let uu____1804 =
              let uu____1805 =
                let uu____1806 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1806 (FStar_String.concat " ")  in
              let uu____1811 =
                let uu____1812 =
                  let uu____1813 = hash_of_term body  in
                  let uu____1814 =
                    let uu____1815 =
                      let uu____1816 = weightToSmt wopt  in
                      let uu____1817 =
                        let uu____1818 =
                          let uu____1819 =
                            let uu____1820 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1836 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1836
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1820
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1819 "))"  in
                        Prims.strcat " " uu____1818  in
                      Prims.strcat uu____1816 uu____1817  in
                    Prims.strcat " " uu____1815  in
                  Prims.strcat uu____1813 uu____1814  in
                Prims.strcat ")(! " uu____1812  in
              Prims.strcat uu____1805 uu____1811  in
            Prims.strcat " (" uu____1804  in
          Prims.strcat (qop_to_string qop) uu____1803  in
        Prims.strcat "(" uu____1802
    | Let (es,body) ->
        let uu____1849 =
          let uu____1850 =
            let uu____1851 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1851 (FStar_String.concat " ")  in
          let uu____1856 =
            let uu____1857 =
              let uu____1858 = hash_of_term body  in
              Prims.strcat uu____1858 ")"  in
            Prims.strcat ") " uu____1857  in
          Prims.strcat uu____1850 uu____1856  in
        Prims.strcat "(let (" uu____1849

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
    let uu____1890 =
      let uu____1891 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1891  in
    mkBoxFunctions uu____1890
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1899 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1899 = "Box") &&
        (let uu____1901 =
           let uu____1902 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1902  in
         Prims.op_Negation uu____1901)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____1923 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1923; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____1992 =
        let uu____1993 = FStar_Util.ensure_decimal i  in Integer uu____1993
         in
      mk uu____1992 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2004 = FStar_Util.string_of_int i  in mkInteger uu____2004 r
  
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
  fun uu____2069  ->
    fun r  -> match uu____2069 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2095) -> mkFalse r
      | App (FalseOp ,uu____2100) -> mkTrue r
      | uu____2105 -> mkApp' (Not, [t]) r
  
let (mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2120  ->
    fun r  ->
      match uu____2120 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2128),uu____2129) -> t2
           | (uu____2134,App (TrueOp ,uu____2135)) -> t1
           | (App (FalseOp ,uu____2140),uu____2141) -> mkFalse r
           | (uu____2146,App (FalseOp ,uu____2147)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2164,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2173) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2180 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2199  ->
    fun r  ->
      match uu____2199 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2207),uu____2208) -> mkTrue r
           | (uu____2213,App (TrueOp ,uu____2214)) -> mkTrue r
           | (App (FalseOp ,uu____2219),uu____2220) -> t2
           | (uu____2225,App (FalseOp ,uu____2226)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2243,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2252) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2259 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2278  ->
    fun r  ->
      match uu____2278 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2286,App (TrueOp ,uu____2287)) -> mkTrue r
           | (App (FalseOp ,uu____2292),uu____2293) -> mkTrue r
           | (App (TrueOp ,uu____2298),uu____2299) -> t2
           | (uu____2304,App (Imp ,t1'::t2'::[])) ->
               let uu____2309 =
                 let uu____2316 =
                   let uu____2319 = mkAnd (t1, t1') r  in [uu____2319; t2']
                    in
                 (Imp, uu____2316)  in
               mkApp' uu____2309 r
           | uu____2322 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun op  ->
    fun uu____2346  ->
      fun r  -> match uu____2346 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____2491  ->
      fun r  ->
        match uu____2491 with
        | (t1,t2) ->
            let uu____2499 =
              let uu____2506 =
                let uu____2509 =
                  let uu____2512 = mkNatToBv sz t2 r  in [uu____2512]  in
                t1 :: uu____2509  in
              (BvShl, uu____2506)  in
            mkApp' uu____2499 r
  
let (mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2532  ->
      fun r  ->
        match uu____2532 with
        | (t1,t2) ->
            let uu____2540 =
              let uu____2547 =
                let uu____2550 =
                  let uu____2553 = mkNatToBv sz t2 r  in [uu____2553]  in
                t1 :: uu____2550  in
              (BvShr, uu____2547)  in
            mkApp' uu____2540 r
  
let (mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2573  ->
      fun r  ->
        match uu____2573 with
        | (t1,t2) ->
            let uu____2581 =
              let uu____2588 =
                let uu____2591 =
                  let uu____2594 = mkNatToBv sz t2 r  in [uu____2594]  in
                t1 :: uu____2591  in
              (BvUdiv, uu____2588)  in
            mkApp' uu____2581 r
  
let (mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2614  ->
      fun r  ->
        match uu____2614 with
        | (t1,t2) ->
            let uu____2622 =
              let uu____2629 =
                let uu____2632 =
                  let uu____2635 = mkNatToBv sz t2 r  in [uu____2635]  in
                t1 :: uu____2632  in
              (BvMod, uu____2629)  in
            mkApp' uu____2622 r
  
let (mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2655  ->
      fun r  ->
        match uu____2655 with
        | (t1,t2) ->
            let uu____2663 =
              let uu____2670 =
                let uu____2673 =
                  let uu____2676 = mkNatToBv sz t2 r  in [uu____2676]  in
                t1 :: uu____2673  in
              (BvMul, uu____2670)  in
            mkApp' uu____2663 r
  
let (mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvUlt 
let (mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Iff 
let (mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2715  ->
    fun r  ->
      match uu____2715 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2731 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2858  ->
    fun r  ->
      match uu____2858 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2869) -> t2
           | App (FalseOp ,uu____2874) -> t3
           | uu____2879 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2880),App (TrueOp ,uu____2881)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2890),uu____2891) ->
                    let uu____2896 =
                      let uu____2901 = mkNot t1 t1.rng  in (uu____2901, t3)
                       in
                    mkImp uu____2896 r
                | (uu____2902,App (TrueOp ,uu____2903)) -> mkImp (t1, t2) r
                | (uu____2908,uu____2909) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
  fun uu____2960  ->
    fun r  ->
      match uu____2960 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____3002) -> body
             | uu____3007 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let (mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____3030  ->
    fun r  ->
      match uu____3030 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____3070 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____3070 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____3093 = FStar_ST.op_Bang t1.freevars  in
        match uu____3093 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3151 ->
            (match t1.tm with
             | Integer uu____3160 -> t1
             | BoundV uu____3161 -> t1
             | FreeV x ->
                 let uu____3167 = index_of x  in
                 (match uu____3167 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3177 =
                   let uu____3184 = FStar_List.map (aux ix) tms  in
                   (op, uu____3184)  in
                 mkApp' uu____3177 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3192 =
                   let uu____3193 =
                     let uu____3200 = aux ix t2  in (uu____3200, r1, r2)  in
                   Labeled uu____3193  in
                 mk uu____3192 t2.rng
             | LblPos (t2,r) ->
                 let uu____3203 =
                   let uu____3204 =
                     let uu____3209 = aux ix t2  in (uu____3209, r)  in
                   LblPos uu____3204  in
                 mk uu____3203 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3232 =
                   let uu____3251 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3272 = aux (ix + n1) body  in
                   (qop, uu____3251, wopt, vars, uu____3272)  in
                 mkQuant uu____3232 t1.rng
             | Let (es,body) ->
                 let uu____3291 =
                   FStar_List.fold_left
                     (fun uu____3309  ->
                        fun e  ->
                          match uu____3309 with
                          | (ix1,l) ->
                              let uu____3329 =
                                let uu____3332 = aux ix1 e  in uu____3332 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3329))
                     (ix, []) es
                    in
                 (match uu____3291 with
                  | (ix1,es_rev) ->
                      let uu____3343 =
                        let uu____3350 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3350)  in
                      mkLet uu____3343 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3382 -> t1
        | FreeV uu____3383 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3400 =
              let uu____3407 = FStar_List.map (aux shift) tms2  in
              (op, uu____3407)  in
            mkApp' uu____3400 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3415 =
              let uu____3416 =
                let uu____3423 = aux shift t2  in (uu____3423, r1, r2)  in
              Labeled uu____3416  in
            mk uu____3415 t2.rng
        | LblPos (t2,r) ->
            let uu____3426 =
              let uu____3427 =
                let uu____3432 = aux shift t2  in (uu____3432, r)  in
              LblPos uu____3427  in
            mk uu____3426 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3460 =
              let uu____3479 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3496 = aux shift1 body  in
              (qop, uu____3479, wopt, vars, uu____3496)  in
            mkQuant uu____3460 t1.rng
        | Let (es,body) ->
            let uu____3511 =
              FStar_List.fold_left
                (fun uu____3529  ->
                   fun e  ->
                     match uu____3529 with
                     | (ix,es1) ->
                         let uu____3549 =
                           let uu____3552 = aux shift e  in uu____3552 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3549))
                (shift, []) es
               in
            (match uu____3511 with
             | (shift1,es_rev) ->
                 let uu____3563 =
                   let uu____3570 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3570)  in
                 mkLet uu____3563 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3588 = abstr [fv] t  in inst [s] uu____3588
  
let (mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term)
  =
  fun uu____3614  ->
    match uu____3614 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3657 =
          let uu____3676 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3693 = FStar_List.map fv_sort vars  in
          let uu____3700 = abstr vars body  in
          (qop, uu____3676, wopt, uu____3693, uu____3700)  in
        mkQuant uu____3657
  
let (mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term)
  =
  fun uu____3733  ->
    fun r  ->
      match uu____3733 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let (mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term)
  =
  fun uu____3801  ->
    fun r  ->
      match uu____3801 with
      | (pats,wopt,vars,body) ->
          let uu____3833 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3833 r
  
let (mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3862  ->
    fun r  ->
      match uu____3862 with
      | (pats,vars,body) ->
          let uu____3885 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3885 r
  
let (mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3914  ->
    fun r  ->
      match uu____3914 with
      | (pats,vars,body) ->
          let uu____3937 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3937 r
  
let (mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun uu____3966  ->
    fun r  ->
      match uu____3966 with
      | (bindings,body) ->
          let uu____3992 = FStar_List.split bindings  in
          (match uu____3992 with
           | (vars,es) ->
               let uu____4011 =
                 let uu____4018 = abstr vars body  in (es, uu____4018)  in
               mkLet uu____4011 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl)
  =
  fun uu____4041  ->
    match uu____4041 with
    | (nm,vars,s,tm,c) ->
        let uu____4075 =
          let uu____4088 = FStar_List.map fv_sort vars  in
          let uu____4095 = abstr vars tm  in
          (nm, uu____4088, s, uu____4095, c)  in
        DefineFun uu____4075
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____4103 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____4103
  
let (fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl) =
  fun uu____4116  ->
    fun id1  ->
      match uu____4116 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____4126 =
              let uu____4127 =
                let uu____4132 = mkInteger' id1 norng  in
                let uu____4133 =
                  let uu____4134 =
                    let uu____4141 = constr_id_of_sort sort  in
                    let uu____4142 =
                      let uu____4145 = mkApp (tok_name, []) norng  in
                      [uu____4145]  in
                    (uu____4141, uu____4142)  in
                  mkApp uu____4134 norng  in
                (uu____4132, uu____4133)  in
              mkEq uu____4127 norng  in
            {
              assumption_term = uu____4126;
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
  fun uu____4164  ->
    match uu____4164 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____4196 =
                      let uu____4201 =
                        let uu____4202 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____4202  in
                      (uu____4201, s)  in
                    mkFreeV uu____4196 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____4210 =
            let uu____4217 = constr_id_of_sort sort  in (uu____4217, [capp])
             in
          mkApp uu____4210 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____4222 =
            let uu____4223 =
              let uu____4234 =
                let uu____4235 =
                  let uu____4240 = mkInteger id2 norng  in
                  (uu____4240, cid_app)  in
                mkEq uu____4235 norng  in
              ([[capp]], bvar_names, uu____4234)  in
            mkForall uu____4223 norng  in
          {
            assumption_term = uu____4222;
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
  fun uu____4263  ->
    match uu____4263 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____4286 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____4286  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____4313 = let uu____4318 = bvar_name i  in (uu____4318, s)
             in
          mkFreeV uu____4313  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4339  ->
                    match uu____4339 with
                    | (uu____4346,s,uu____4348) ->
                        let uu____4349 = bvar i s  in uu____4349 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____4360 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4388  ->
                    match uu____4388 with
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
                            let uu____4411 =
                              let uu____4412 =
                                let uu____4423 =
                                  let uu____4424 =
                                    let uu____4429 =
                                      let uu____4430 = bvar i s  in
                                      uu____4430 norng  in
                                    (cproj_app, uu____4429)  in
                                  mkEq uu____4424 norng  in
                                ([[capp]], bvar_names, uu____4423)  in
                              mkForall uu____4412 norng  in
                            {
                              assumption_term = uu____4411;
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
        FStar_All.pipe_right uu____4360 FStar_List.flatten
  
let (constructor_to_decl : constructor_t -> decls_t) =
  fun uu____4456  ->
    match uu____4456 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4484  ->
                  match uu____4484 with
                  | (uu____4491,sort1,uu____4493) -> sort1))
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
            let uu____4511 =
              let uu____4516 =
                let uu____4517 =
                  let uu____4524 = constr_id_of_sort sort  in
                  (uu____4524, [xx])  in
                mkApp uu____4517 norng  in
              let uu____4527 =
                let uu____4528 = FStar_Util.string_of_int id1  in
                mkInteger uu____4528 norng  in
              (uu____4516, uu____4527)  in
            mkEq uu____4511 norng  in
          let uu____4529 =
            let uu____4544 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4594  ->
                        match uu____4594 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4624 = mkApp (proj, [xx]) norng  in
                              (uu____4624, [])
                            else
                              (let fi =
                                 let uu____4643 =
                                   let uu____4644 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4644  in
                                 (uu____4643, s)  in
                               let uu____4645 = mkFreeV fi norng  in
                               (uu____4645, [fi]))))
               in
            FStar_All.pipe_right uu____4544 FStar_List.split  in
          match uu____4529 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4726 =
                  let uu____4731 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4731)  in
                mkEq uu____4726 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4739 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____4780 =
          let uu____4783 =
            let uu____4784 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4784  in
          uu____4783 :: cdecl :: cid :: projs  in
        let uu____4785 =
          let uu____4788 =
            let uu____4791 =
              let uu____4792 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4792  in
            [uu____4791]  in
          FStar_List.append [disc] uu____4788  in
        FStar_List.append uu____4780 uu____4785
  
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
          let uu____4847 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4902  ->
                    fun s  ->
                      match uu____4902 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4952 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4956 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4956  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____4969 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____4969  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4847 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun sorts  ->
    let uu____5048 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____5048 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
          fun depth  ->
            let n1 = FStar_ST.op_Bang ctr  in
            let uu____5180 = FStar_Util.incr ctr  in
            if n1 = (Prims.parse_int "0")
            then enclosing_name
            else
              (let uu____5215 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5215)
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
                               "Prims.guard_free",{ tm = BoundV uu____5259;
                                                    freevars = uu____5260;
                                                    rng = uu____5261;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5275 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5337 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5337 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5352 = op_to_string op  in
              let uu____5353 =
                let uu____5354 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5354 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5352 uu____5353
          | Labeled (t2,uu____5360,uu____5361) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5364 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5364 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5387 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5387 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5436 ->
                         let uu____5441 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5457 =
                                     let uu____5458 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5464 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5464) pats2
                                        in
                                     FStar_String.concat " " uu____5458  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5457))
                            in
                         FStar_All.pipe_right uu____5441
                           (FStar_String.concat "\n")
                      in
                   let uu____5467 =
                     let uu____5470 =
                       let uu____5473 =
                         let uu____5476 = aux1 n2 names2 body  in
                         let uu____5477 =
                           let uu____5480 = weightToSmt wopt  in
                           [uu____5480; pats_str; qid]  in
                         uu____5476 :: uu____5477  in
                       binders1 :: uu____5473  in
                     (qop_to_string qop) :: uu____5470  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5467)
          | Let (es,body) ->
              let uu____5487 =
                FStar_List.fold_left
                  (fun uu____5524  ->
                     fun e  ->
                       match uu____5524 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5574 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5574  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5587 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5587  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____5487 with
               | (names2,binders,n2) ->
                   let uu____5619 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5619)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5627 = FStar_Range.string_of_range t1.rng  in
            let uu____5628 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5627
              uu____5628 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___53_5636  ->
    match uu___53_5636 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5640 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5655 -> (hd1, "...")  in
        (match uu____5640 with
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
            let uu____5704 = FStar_Options.log_queries ()  in
            if uu____5704
            then
              let uu____5705 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___54_5709  ->
                     match uu___54_5709 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5705
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____5728 = caption_to_string c  in
            let uu____5729 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5728 f
              (FStar_String.concat " " l) uu____5729
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5739 = name_macro_binders arg_sorts  in
            (match uu____5739 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5771 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____5771 body  in
                 let uu____5784 = caption_to_string c  in
                 let uu____5785 = strSort retsort  in
                 let uu____5786 = termToSmt print_ranges (escape f) body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5784 f (FStar_String.concat " " binders) uu____5785
                   uu____5786)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___55_5807  ->
                      match uu___55_5807 with
                      | Name n1 ->
                          let uu____5809 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____5809
                      | Namespace ns ->
                          let uu____5811 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____5811
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____5814 = FStar_Options.log_queries ()  in
              if uu____5814
              then
                let uu____5815 =
                  let uu____5816 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____5816  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5815
              else ""  in
            let n1 = escape a.assumption_name  in
            let uu____5821 = caption_to_string a.assumption_caption  in
            let uu____5822 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5821
              fids uu____5822 n1
        | Eval t ->
            let uu____5824 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____5824
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5826 -> ""
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
      let uu____6155 =
        let uu____6158 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____6158
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____6155 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____6175 =
      let uu____6194 =
        let uu____6195 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6195  in
      let uu____6200 =
        let uu____6209 =
          let uu____6216 =
            let uu____6217 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____6217  in
          (uu____6216, (BitVec_sort sz), true)  in
        [uu____6209]  in
      (uu____6194, uu____6200, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____6175 constructor_to_decl
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____6277  ->
    let i = FStar_ST.op_Bang __range_c  in
    let uu____6302 =
      let uu____6303 =
        let uu____6304 = FStar_ST.op_Bang __range_c  in
        uu____6304 + (Prims.parse_int "1")  in
      FStar_ST.op_Colon_Equals __range_c uu____6303  in
    let uu____6351 =
      let uu____6358 = let uu____6361 = mkInteger' i norng  in [uu____6361]
         in
      ("Range_const", uu____6358)  in
    mkApp uu____6351 norng
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6393 =
        let uu____6400 = let uu____6403 = mkInteger' i norng  in [uu____6403]
           in
        ("Tm_uvar", uu____6400)  in
      mkApp uu____6393 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6432 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6450 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6450 u v1 t
  
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
      let uu____6491 =
        let uu____6492 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6492  in
      let uu____6497 =
        let uu____6498 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6498  in
      elim_box true uu____6491 uu____6497 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6513 =
        let uu____6514 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6514  in
      let uu____6519 =
        let uu____6520 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6520  in
      elim_box true uu____6513 uu____6519 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6536 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6548 -> FStar_Exn.raise FStar_Util.Impos
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6570 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____6570
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6582 = op_to_string op  in
        let uu____6583 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____6582 uu____6583
    | Labeled (t1,r1,r2) ->
        let uu____6587 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6587
    | LblPos (t1,s) ->
        let uu____6590 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6590
    | Quant (qop,l,uu____6593,uu____6594,t1) ->
        let uu____6612 = print_smt_term_list_list l  in
        let uu____6613 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6612
          uu____6613
    | Let (es,body) ->
        let uu____6620 = print_smt_term_list es  in
        let uu____6621 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____6620 uu____6621

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____6625 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____6625 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6644 =
             let uu____6645 =
               let uu____6646 = print_smt_term_list l1  in
               Prims.strcat uu____6646 " ] "  in
             Prims.strcat "; [ " uu____6645  in
           Prims.strcat s uu____6644) "" l

let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6663 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6663
         | uu____6664 -> FStar_Pervasives_Native.None)
    | uu____6665 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6678::t1::t2::[]);
                       freevars = uu____6681; rng = uu____6682;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6695::t1::t2::[]);
                       freevars = uu____6698; rng = uu____6699;_}::[])
        -> let uu____6712 = mkEq (t1, t2) norng  in mkNot uu____6712 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6715; rng = uu____6716;_}::[])
        ->
        let uu____6729 =
          let uu____6734 = unboxInt t1  in
          let uu____6735 = unboxInt t2  in (uu____6734, uu____6735)  in
        mkLTE uu____6729 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6738; rng = uu____6739;_}::[])
        ->
        let uu____6752 =
          let uu____6757 = unboxInt t1  in
          let uu____6758 = unboxInt t2  in (uu____6757, uu____6758)  in
        mkLT uu____6752 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6761; rng = uu____6762;_}::[])
        ->
        let uu____6775 =
          let uu____6780 = unboxInt t1  in
          let uu____6781 = unboxInt t2  in (uu____6780, uu____6781)  in
        mkGTE uu____6775 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6784; rng = uu____6785;_}::[])
        ->
        let uu____6798 =
          let uu____6803 = unboxInt t1  in
          let uu____6804 = unboxInt t2  in (uu____6803, uu____6804)  in
        mkGT uu____6798 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6807; rng = uu____6808;_}::[])
        ->
        let uu____6821 =
          let uu____6826 = unboxBool t1  in
          let uu____6827 = unboxBool t2  in (uu____6826, uu____6827)  in
        mkAnd uu____6821 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6830; rng = uu____6831;_}::[])
        ->
        let uu____6844 =
          let uu____6849 = unboxBool t1  in
          let uu____6850 = unboxBool t2  in (uu____6849, uu____6850)  in
        mkOr uu____6844 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6852; rng = uu____6853;_}::[])
        -> let uu____6866 = unboxBool t1  in mkNot uu____6866 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6870; rng = uu____6871;_}::[])
        when
        let uu____6884 = getBoxedInteger t0  in FStar_Util.is_some uu____6884
        ->
        let sz =
          let uu____6888 = getBoxedInteger t0  in
          match uu____6888 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6892 -> failwith "impossible"  in
        let uu____6895 =
          let uu____6900 = unboxBitVec sz t1  in
          let uu____6901 = unboxBitVec sz t2  in (uu____6900, uu____6901)  in
        mkBvUlt uu____6895 t.rng
    | App
        (Var
         "Prims.equals",uu____6902::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6906;
                                      rng = uu____6907;_}::uu____6908::[])
        when
        let uu____6921 = getBoxedInteger t0  in FStar_Util.is_some uu____6921
        ->
        let sz =
          let uu____6925 = getBoxedInteger t0  in
          match uu____6925 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6929 -> failwith "impossible"  in
        let uu____6932 =
          let uu____6937 = unboxBitVec sz t1  in
          let uu____6938 = unboxBitVec sz t2  in (uu____6937, uu____6938)  in
        mkBvUlt uu____6932 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___56_6942 = unboxBool t1  in
        {
          tm = (uu___56_6942.tm);
          freevars = (uu___56_6942.freevars);
          rng = (t.rng)
        }
    | uu____6943 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6992 = FStar_Options.unthrottle_inductives ()  in
        if uu____6992
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
      let uu____7103 =
        let uu____7110 = let uu____7113 = mkInteger' i norng  in [uu____7113]
           in
        ("FString_const", uu____7110)  in
      mkApp uu____7103 r
  
let (mk_Precedes : term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____7131 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____7131 mk_Valid
  
let (mk_LexCons : term -> term -> FStar_Range.range -> term) =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____7159 =
         let uu____7166 =
           let uu____7169 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____7169]  in
         ("SFuel", uu____7166)  in
       mkApp uu____7159 norng)
  
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
            let uu____7209 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____7209
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
      let uu____7270 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____7270
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____7289 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____7289
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____7299 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____7299
  