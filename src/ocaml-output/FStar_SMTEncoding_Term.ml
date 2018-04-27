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
    match projectee with | Bool_sort  -> true | uu____34 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____40 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____46 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____52 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____58 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____65 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____83 -> false
  
let (__proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____113 -> false
  
let (__proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____139 -> false
  
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
        let uu____153 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____153
    | Array (s1,s2) ->
        let uu____156 = strSort s1  in
        let uu____157 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____156 uu____157
    | Arrow (s1,s2) ->
        let uu____160 = strSort s1  in
        let uu____161 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____160 uu____161
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
    match projectee with | TrueOp  -> true | uu____183 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____189 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____195 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____201 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____207 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____213 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____219 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____225 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____231 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____237 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____243 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____249 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____255 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____261 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____267 -> false 
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____273 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____279 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____285 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____291 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____297 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____303 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____309 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____315 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____321 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____327 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____333 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____339 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____345 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____351 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____358 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____372 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____385 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____391 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____398 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists [@@deriving show]
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____411 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____417 -> false
  
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
    match projectee with | Integer _0 -> true | uu____552 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____566 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____584 -> false
  
let (__proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____616 -> false
  
let (__proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____666 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____740 -> false
  
let (__proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____778 -> false
  
let (__proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____814 -> false
  
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
    match projectee with | Name _0 -> true | uu____990 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1004 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1018 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1169 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1186 -> false
  
let (__proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1242 -> false
  
let (__proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1292 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1306 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1320 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1334 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1350 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1369 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1375 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1381 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1387 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1398 -> false
  
let (__proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1423 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1429 -> false
  
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
  'Auu____1456 'Auu____1457 .
    ('Auu____1456,'Auu____1457) FStar_Pervasives_Native.tuple2 ->
      'Auu____1457
  = fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1491 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___48_1500  ->
    match uu___48_1500 with
    | { tm = FreeV x; freevars = uu____1502; rng = uu____1503;_} -> fv_sort x
    | uu____1516 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___49_1521  ->
    match uu___49_1521 with
    | { tm = FreeV fv; freevars = uu____1523; rng = uu____1524;_} -> fv
    | uu____1537 -> failwith "impossible"
  
let rec (freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____1555 -> []
    | BoundV uu____1560 -> []
    | FreeV fv -> [fv]
    | App (uu____1578,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1588,uu____1589,uu____1590,uu____1591,t1) -> freevars t1
    | Labeled (t1,uu____1610,uu____1611) -> freevars t1
    | LblPos (t1,uu____1613) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____1629 = FStar_ST.op_Bang t.freevars  in
    match uu____1629 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1703 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1703  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___50_1764  ->
    match uu___50_1764 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___51_1769  ->
    match uu___51_1769 with
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
        let uu____1771 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1771
    | NatToBv n1 ->
        let uu____1773 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1773
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___52_1781  ->
    match uu___52_1781 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1785 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1785
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1797 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1797
    | FreeV x ->
        let uu____1803 =
          let uu____1804 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1804  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1803
    | App (op,tms) ->
        let uu____1811 =
          let uu____1812 = op_to_string op  in
          let uu____1813 =
            let uu____1814 =
              let uu____1815 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1815 (FStar_String.concat " ")  in
            Prims.strcat uu____1814 ")"  in
          Prims.strcat uu____1812 uu____1813  in
        Prims.strcat "(" uu____1811
    | Labeled (t1,r1,r2) ->
        let uu____1823 = hash_of_term t1  in
        let uu____1824 =
          let uu____1825 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1825  in
        Prims.strcat uu____1823 uu____1824
    | LblPos (t1,r) ->
        let uu____1828 =
          let uu____1829 = hash_of_term t1  in
          Prims.strcat uu____1829
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1828
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1851 =
          let uu____1852 =
            let uu____1853 =
              let uu____1854 =
                let uu____1855 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1855 (FStar_String.concat " ")  in
              let uu____1860 =
                let uu____1861 =
                  let uu____1862 = hash_of_term body  in
                  let uu____1863 =
                    let uu____1864 =
                      let uu____1865 = weightToSmt wopt  in
                      let uu____1866 =
                        let uu____1867 =
                          let uu____1868 =
                            let uu____1869 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1885 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1885
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1869
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1868 "))"  in
                        Prims.strcat " " uu____1867  in
                      Prims.strcat uu____1865 uu____1866  in
                    Prims.strcat " " uu____1864  in
                  Prims.strcat uu____1862 uu____1863  in
                Prims.strcat ")(! " uu____1861  in
              Prims.strcat uu____1854 uu____1860  in
            Prims.strcat " (" uu____1853  in
          Prims.strcat (qop_to_string qop) uu____1852  in
        Prims.strcat "(" uu____1851
    | Let (es,body) ->
        let uu____1898 =
          let uu____1899 =
            let uu____1900 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1900 (FStar_String.concat " ")  in
          let uu____1905 =
            let uu____1906 =
              let uu____1907 = hash_of_term body  in
              Prims.strcat uu____1907 ")"  in
            Prims.strcat ") " uu____1906  in
          Prims.strcat uu____1899 uu____1905  in
        Prims.strcat "(let (" uu____1898

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
    let uu____1939 =
      let uu____1940 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1940  in
    mkBoxFunctions uu____1939
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1948 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1948 = "Box") &&
        (let uu____1950 =
           let uu____1951 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1951  in
         Prims.op_Negation uu____1950)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____1972 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1972; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2041 =
        let uu____2042 = FStar_Util.ensure_decimal i  in Integer uu____2042
         in
      mk uu____2041 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2053 = FStar_Util.string_of_int i  in mkInteger uu____2053 r
  
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
  fun uu____2118  ->
    fun r  -> match uu____2118 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2144) -> mkFalse r
      | App (FalseOp ,uu____2149) -> mkTrue r
      | uu____2154 -> mkApp' (Not, [t]) r
  
let (mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2169  ->
    fun r  ->
      match uu____2169 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2177),uu____2178) -> t2
           | (uu____2183,App (TrueOp ,uu____2184)) -> t1
           | (App (FalseOp ,uu____2189),uu____2190) -> mkFalse r
           | (uu____2195,App (FalseOp ,uu____2196)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2213,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2222) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2229 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2248  ->
    fun r  ->
      match uu____2248 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2256),uu____2257) -> mkTrue r
           | (uu____2262,App (TrueOp ,uu____2263)) -> mkTrue r
           | (App (FalseOp ,uu____2268),uu____2269) -> t2
           | (uu____2274,App (FalseOp ,uu____2275)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2292,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2301) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2308 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2327  ->
    fun r  ->
      match uu____2327 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2335,App (TrueOp ,uu____2336)) -> mkTrue r
           | (App (FalseOp ,uu____2341),uu____2342) -> mkTrue r
           | (App (TrueOp ,uu____2347),uu____2348) -> t2
           | (uu____2353,App (Imp ,t1'::t2'::[])) ->
               let uu____2358 =
                 let uu____2365 =
                   let uu____2368 = mkAnd (t1, t1') r  in [uu____2368; t2']
                    in
                 (Imp, uu____2365)  in
               mkApp' uu____2358 r
           | uu____2371 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun op  ->
    fun uu____2395  ->
      fun r  -> match uu____2395 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____2540  ->
      fun r  ->
        match uu____2540 with
        | (t1,t2) ->
            let uu____2548 =
              let uu____2555 =
                let uu____2558 =
                  let uu____2561 = mkNatToBv sz t2 r  in [uu____2561]  in
                t1 :: uu____2558  in
              (BvShl, uu____2555)  in
            mkApp' uu____2548 r
  
let (mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2581  ->
      fun r  ->
        match uu____2581 with
        | (t1,t2) ->
            let uu____2589 =
              let uu____2596 =
                let uu____2599 =
                  let uu____2602 = mkNatToBv sz t2 r  in [uu____2602]  in
                t1 :: uu____2599  in
              (BvShr, uu____2596)  in
            mkApp' uu____2589 r
  
let (mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2622  ->
      fun r  ->
        match uu____2622 with
        | (t1,t2) ->
            let uu____2630 =
              let uu____2637 =
                let uu____2640 =
                  let uu____2643 = mkNatToBv sz t2 r  in [uu____2643]  in
                t1 :: uu____2640  in
              (BvUdiv, uu____2637)  in
            mkApp' uu____2630 r
  
let (mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2663  ->
      fun r  ->
        match uu____2663 with
        | (t1,t2) ->
            let uu____2671 =
              let uu____2678 =
                let uu____2681 =
                  let uu____2684 = mkNatToBv sz t2 r  in [uu____2684]  in
                t1 :: uu____2681  in
              (BvMod, uu____2678)  in
            mkApp' uu____2671 r
  
let (mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2704  ->
      fun r  ->
        match uu____2704 with
        | (t1,t2) ->
            let uu____2712 =
              let uu____2719 =
                let uu____2722 =
                  let uu____2725 = mkNatToBv sz t2 r  in [uu____2725]  in
                t1 :: uu____2722  in
              (BvMul, uu____2719)  in
            mkApp' uu____2712 r
  
let (mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvUlt 
let (mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Iff 
let (mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2764  ->
    fun r  ->
      match uu____2764 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2780 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2907  ->
    fun r  ->
      match uu____2907 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2918) -> t2
           | App (FalseOp ,uu____2923) -> t3
           | uu____2928 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2929),App (TrueOp ,uu____2930)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2939),uu____2940) ->
                    let uu____2945 =
                      let uu____2950 = mkNot t1 t1.rng  in (uu____2950, t3)
                       in
                    mkImp uu____2945 r
                | (uu____2951,App (TrueOp ,uu____2952)) -> mkImp (t1, t2) r
                | (uu____2957,uu____2958) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
  fun uu____3009  ->
    fun r  ->
      match uu____3009 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____3052) -> body
             | uu____3057 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let (mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____3080  ->
    fun r  ->
      match uu____3080 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____3121 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____3121 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____3144 = FStar_ST.op_Bang t1.freevars  in
        match uu____3144 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3202 ->
            (match t1.tm with
             | Integer uu____3211 -> t1
             | BoundV uu____3212 -> t1
             | FreeV x ->
                 let uu____3218 = index_of x  in
                 (match uu____3218 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3228 =
                   let uu____3235 = FStar_List.map (aux ix) tms  in
                   (op, uu____3235)  in
                 mkApp' uu____3228 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3243 =
                   let uu____3244 =
                     let uu____3251 = aux ix t2  in (uu____3251, r1, r2)  in
                   Labeled uu____3244  in
                 mk uu____3243 t2.rng
             | LblPos (t2,r) ->
                 let uu____3254 =
                   let uu____3255 =
                     let uu____3260 = aux ix t2  in (uu____3260, r)  in
                   LblPos uu____3255  in
                 mk uu____3254 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3283 =
                   let uu____3302 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3323 = aux (ix + n1) body  in
                   (qop, uu____3302, wopt, vars, uu____3323)  in
                 mkQuant uu____3283 t1.rng
             | Let (es,body) ->
                 let uu____3342 =
                   FStar_List.fold_left
                     (fun uu____3360  ->
                        fun e  ->
                          match uu____3360 with
                          | (ix1,l) ->
                              let uu____3380 =
                                let uu____3383 = aux ix1 e  in uu____3383 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3380))
                     (ix, []) es
                    in
                 (match uu____3342 with
                  | (ix1,es_rev) ->
                      let uu____3394 =
                        let uu____3401 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3401)  in
                      mkLet uu____3394 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3433 -> t1
        | FreeV uu____3434 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3451 =
              let uu____3458 = FStar_List.map (aux shift) tms2  in
              (op, uu____3458)  in
            mkApp' uu____3451 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3466 =
              let uu____3467 =
                let uu____3474 = aux shift t2  in (uu____3474, r1, r2)  in
              Labeled uu____3467  in
            mk uu____3466 t2.rng
        | LblPos (t2,r) ->
            let uu____3477 =
              let uu____3478 =
                let uu____3483 = aux shift t2  in (uu____3483, r)  in
              LblPos uu____3478  in
            mk uu____3477 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3511 =
              let uu____3530 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3547 = aux shift1 body  in
              (qop, uu____3530, wopt, vars, uu____3547)  in
            mkQuant uu____3511 t1.rng
        | Let (es,body) ->
            let uu____3562 =
              FStar_List.fold_left
                (fun uu____3580  ->
                   fun e  ->
                     match uu____3580 with
                     | (ix,es1) ->
                         let uu____3600 =
                           let uu____3603 = aux shift e  in uu____3603 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3600))
                (shift, []) es
               in
            (match uu____3562 with
             | (shift1,es_rev) ->
                 let uu____3614 =
                   let uu____3621 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3621)  in
                 mkLet uu____3614 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3639 = abstr [fv] t  in inst [s] uu____3639
  
let (mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term)
  =
  fun uu____3665  ->
    match uu____3665 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3708 =
          let uu____3727 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3744 = FStar_List.map fv_sort vars  in
          let uu____3747 = abstr vars body  in
          (qop, uu____3727, wopt, uu____3744, uu____3747)  in
        mkQuant uu____3708
  
let (mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term)
  =
  fun uu____3780  ->
    fun r  ->
      match uu____3780 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let (mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term)
  =
  fun uu____3848  ->
    fun r  ->
      match uu____3848 with
      | (pats,wopt,vars,body) ->
          let uu____3880 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3880 r
  
let (mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3911  ->
    fun r  ->
      match uu____3911 with
      | (pats,vars,body) ->
          let uu____3934 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3934 r
  
let (mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term)
  =
  fun uu____3965  ->
    fun r  ->
      match uu____3965 with
      | (pats,vars,body) ->
          let uu____3988 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3988 r
  
let (mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun uu____4019  ->
    fun r  ->
      match uu____4019 with
      | (bindings,body) ->
          let uu____4045 = FStar_List.split bindings  in
          (match uu____4045 with
           | (vars,es) ->
               let uu____4064 =
                 let uu____4071 = abstr vars body  in (es, uu____4071)  in
               mkLet uu____4064 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl)
  =
  fun uu____4094  ->
    match uu____4094 with
    | (nm,vars,s,tm,c) ->
        let uu____4128 =
          let uu____4141 = FStar_List.map fv_sort vars  in
          let uu____4148 = abstr vars tm  in
          (nm, uu____4141, s, uu____4148, c)  in
        DefineFun uu____4128
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____4156 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____4156
  
let (fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl) =
  fun uu____4169  ->
    fun id1  ->
      match uu____4169 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____4179 =
              let uu____4180 =
                let uu____4185 = mkInteger' id1 norng  in
                let uu____4186 =
                  let uu____4187 =
                    let uu____4194 = constr_id_of_sort sort  in
                    let uu____4195 =
                      let uu____4198 = mkApp (tok_name, []) norng  in
                      [uu____4198]  in
                    (uu____4194, uu____4195)  in
                  mkApp uu____4187 norng  in
                (uu____4185, uu____4186)  in
              mkEq uu____4180 norng  in
            {
              assumption_term = uu____4179;
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
  fun uu____4217  ->
    match uu____4217 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____4249 =
                      let uu____4254 =
                        let uu____4255 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____4255  in
                      (uu____4254, s)  in
                    mkFreeV uu____4249 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____4271 =
            let uu____4278 = constr_id_of_sort sort  in (uu____4278, [capp])
             in
          mkApp uu____4271 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____4283 =
            let uu____4284 =
              let uu____4295 =
                let uu____4296 =
                  let uu____4301 = mkInteger id2 norng  in
                  (uu____4301, cid_app)  in
                mkEq uu____4296 norng  in
              ([[capp]], bvar_names, uu____4295)  in
            mkForall uu____4284 norng  in
          {
            assumption_term = uu____4283;
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
  fun uu____4322  ->
    match uu____4322 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____4345 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____4345  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____4372 = let uu____4377 = bvar_name i  in (uu____4377, s)
             in
          mkFreeV uu____4372  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4404  ->
                    match uu____4404 with
                    | (uu____4411,s,uu____4413) ->
                        let uu____4414 = bvar i s  in uu____4414 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____4433 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4467  ->
                    match uu____4467 with
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
                            let uu____4488 =
                              let uu____4489 =
                                let uu____4500 =
                                  let uu____4501 =
                                    let uu____4506 =
                                      let uu____4507 = bvar i s  in
                                      uu____4507 norng  in
                                    (cproj_app, uu____4506)  in
                                  mkEq uu____4501 norng  in
                                ([[capp]], bvar_names, uu____4500)  in
                              mkForall uu____4489 norng  in
                            {
                              assumption_term = uu____4488;
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
        FStar_All.pipe_right uu____4433 FStar_List.flatten
  
let (constructor_to_decl : constructor_t -> decls_t) =
  fun uu____4529  ->
    match uu____4529 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4563  ->
                  match uu____4563 with
                  | (uu____4570,sort1,uu____4572) -> sort1))
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
            let uu____4588 =
              let uu____4593 =
                let uu____4594 =
                  let uu____4601 = constr_id_of_sort sort  in
                  (uu____4601, [xx])  in
                mkApp uu____4594 norng  in
              let uu____4604 =
                let uu____4605 = FStar_Util.string_of_int id1  in
                mkInteger uu____4605 norng  in
              (uu____4593, uu____4604)  in
            mkEq uu____4588 norng  in
          let uu____4606 =
            let uu____4621 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4677  ->
                        match uu____4677 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4707 = mkApp (proj, [xx]) norng  in
                              (uu____4707, [])
                            else
                              (let fi =
                                 let uu____4726 =
                                   let uu____4727 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4727  in
                                 (uu____4726, s)  in
                               let uu____4728 = mkFreeV fi norng  in
                               (uu____4728, [fi]))))
               in
            FStar_All.pipe_right uu____4621 FStar_List.split  in
          match uu____4606 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4809 =
                  let uu____4814 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4814)  in
                mkEq uu____4809 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4822 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____4859 =
          let uu____4862 =
            let uu____4863 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4863  in
          uu____4862 :: cdecl :: cid :: projs  in
        let uu____4864 =
          let uu____4867 =
            let uu____4870 =
              let uu____4871 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4871  in
            [uu____4870]  in
          FStar_List.append [disc] uu____4867  in
        FStar_List.append uu____4859 uu____4864
  
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
          let uu____4926 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4981  ->
                    fun s  ->
                      match uu____4981 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____5031 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____5035 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____5035  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____5048 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____5048  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4926 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun sorts  ->
    let uu____5127 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____5127 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
          fun uu____5212  ->
            let n1 = FStar_ST.op_Bang ctr  in
            FStar_Util.incr ctr;
            if n1 = (Prims.parse_int "0")
            then enclosing_name
            else
              (let uu____5294 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5294)
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
                               "Prims.guard_free",{ tm = BoundV uu____5338;
                                                    freevars = uu____5339;
                                                    rng = uu____5340;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5354 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5416 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5416 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5439 = op_to_string op  in
              let uu____5440 =
                let uu____5441 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5441 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5439 uu____5440
          | Labeled (t2,uu____5447,uu____5448) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5451 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5451 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5474 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5474 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5523 ->
                         let uu____5528 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5544 =
                                     let uu____5545 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5551 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5551) pats2
                                        in
                                     FStar_String.concat " " uu____5545  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5544))
                            in
                         FStar_All.pipe_right uu____5528
                           (FStar_String.concat "\n")
                      in
                   let uu____5554 =
                     let uu____5557 =
                       let uu____5560 =
                         let uu____5563 = aux1 n2 names2 body  in
                         let uu____5564 =
                           let uu____5567 = weightToSmt wopt  in
                           [uu____5567; pats_str; qid]  in
                         uu____5563 :: uu____5564  in
                       binders1 :: uu____5560  in
                     (qop_to_string qop) :: uu____5557  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5554)
          | Let (es,body) ->
              let uu____5574 =
                FStar_List.fold_left
                  (fun uu____5611  ->
                     fun e  ->
                       match uu____5611 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5661 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5661  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5674 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5674  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____5574 with
               | (names2,binders,n2) ->
                   let uu____5710 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5710)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5718 = FStar_Range.string_of_range t1.rng  in
            let uu____5719 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5718
              uu____5719 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___53_5727  ->
    match uu___53_5727 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5731 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5746 -> (hd1, "...")  in
        (match uu____5731 with
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
            let uu____5795 = FStar_Options.log_queries ()  in
            if uu____5795
            then
              let uu____5796 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___54_5800  ->
                     match uu___54_5800 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5796
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____5819 = caption_to_string c  in
            let uu____5820 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5819 f
              (FStar_String.concat " " l) uu____5820
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5830 = name_macro_binders arg_sorts  in
            (match uu____5830 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5862 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____5862 body  in
                 let uu____5875 = caption_to_string c  in
                 let uu____5876 = strSort retsort  in
                 let uu____5877 = termToSmt print_ranges (escape f) body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____5875 f (FStar_String.concat " " binders) uu____5876
                   uu____5877)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___55_5898  ->
                      match uu___55_5898 with
                      | Name n1 ->
                          let uu____5900 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____5900
                      | Namespace ns ->
                          let uu____5902 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____5902
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____5905 = FStar_Options.log_queries ()  in
              if uu____5905
              then
                let uu____5906 =
                  let uu____5907 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____5907  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5906
              else ""  in
            let n1 = escape a.assumption_name  in
            let uu____5912 = caption_to_string a.assumption_caption  in
            let uu____5913 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5912
              fids uu____5913 n1
        | Eval t ->
            let uu____5915 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____5915
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5917 -> ""
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
      let uu____5946 =
        let uu____5949 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____5949
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____5946 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____5968 =
      let uu____5969 =
        let uu____5970 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5970  in
      let uu____5975 =
        let uu____5978 =
          let uu____5979 =
            let uu____5980 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____5980  in
          (uu____5979, (BitVec_sort sz), true)  in
        [uu____5978]  in
      (uu____5969, uu____5975, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____5968 constructor_to_decl
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____6004  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____6030 =
       let uu____6031 = FStar_ST.op_Bang __range_c  in
       uu____6031 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____6030);
    (let uu____6078 =
       let uu____6085 = let uu____6088 = mkInteger' i norng  in [uu____6088]
          in
       ("Range_const", uu____6085)  in
     mkApp uu____6078 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6120 =
        let uu____6127 = let uu____6130 = mkInteger' i norng  in [uu____6130]
           in
        ("Tm_uvar", uu____6127)  in
      mkApp uu____6120 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6159 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6177 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6177 u v1 t
  
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
      let uu____6218 =
        let uu____6219 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6219  in
      let uu____6224 =
        let uu____6225 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6225  in
      elim_box true uu____6218 uu____6224 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6240 =
        let uu____6241 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6241  in
      let uu____6246 =
        let uu____6247 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6247  in
      elim_box true uu____6240 uu____6246 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6263 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6275 -> FStar_Exn.raise FStar_Util.Impos
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6297 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____6297
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6309 = op_to_string op  in
        let uu____6310 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____6309 uu____6310
    | Labeled (t1,r1,r2) ->
        let uu____6314 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6314
    | LblPos (t1,s) ->
        let uu____6317 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6317
    | Quant (qop,l,uu____6320,uu____6321,t1) ->
        let uu____6339 = print_smt_term_list_list l  in
        let uu____6340 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6339
          uu____6340
    | Let (es,body) ->
        let uu____6347 = print_smt_term_list es  in
        let uu____6348 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____6347 uu____6348

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____6352 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____6352 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6371 =
             let uu____6372 =
               let uu____6373 = print_smt_term_list l1  in
               Prims.strcat uu____6373 " ] "  in
             Prims.strcat "; [ " uu____6372  in
           Prims.strcat s uu____6371) "" l

let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6390 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6390
         | uu____6391 -> FStar_Pervasives_Native.None)
    | uu____6392 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6405::t1::t2::[]);
                       freevars = uu____6408; rng = uu____6409;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6422::t1::t2::[]);
                       freevars = uu____6425; rng = uu____6426;_}::[])
        -> let uu____6439 = mkEq (t1, t2) norng  in mkNot uu____6439 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6442; rng = uu____6443;_}::[])
        ->
        let uu____6456 =
          let uu____6461 = unboxInt t1  in
          let uu____6462 = unboxInt t2  in (uu____6461, uu____6462)  in
        mkLTE uu____6456 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6465; rng = uu____6466;_}::[])
        ->
        let uu____6479 =
          let uu____6484 = unboxInt t1  in
          let uu____6485 = unboxInt t2  in (uu____6484, uu____6485)  in
        mkLT uu____6479 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6488; rng = uu____6489;_}::[])
        ->
        let uu____6502 =
          let uu____6507 = unboxInt t1  in
          let uu____6508 = unboxInt t2  in (uu____6507, uu____6508)  in
        mkGTE uu____6502 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6511; rng = uu____6512;_}::[])
        ->
        let uu____6525 =
          let uu____6530 = unboxInt t1  in
          let uu____6531 = unboxInt t2  in (uu____6530, uu____6531)  in
        mkGT uu____6525 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6534; rng = uu____6535;_}::[])
        ->
        let uu____6548 =
          let uu____6553 = unboxBool t1  in
          let uu____6554 = unboxBool t2  in (uu____6553, uu____6554)  in
        mkAnd uu____6548 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6557; rng = uu____6558;_}::[])
        ->
        let uu____6571 =
          let uu____6576 = unboxBool t1  in
          let uu____6577 = unboxBool t2  in (uu____6576, uu____6577)  in
        mkOr uu____6571 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6579; rng = uu____6580;_}::[])
        -> let uu____6593 = unboxBool t1  in mkNot uu____6593 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6597; rng = uu____6598;_}::[])
        when
        let uu____6611 = getBoxedInteger t0  in FStar_Util.is_some uu____6611
        ->
        let sz =
          let uu____6615 = getBoxedInteger t0  in
          match uu____6615 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6619 -> failwith "impossible"  in
        let uu____6622 =
          let uu____6627 = unboxBitVec sz t1  in
          let uu____6628 = unboxBitVec sz t2  in (uu____6627, uu____6628)  in
        mkBvUlt uu____6622 t.rng
    | App
        (Var
         "Prims.equals",uu____6629::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6633;
                                      rng = uu____6634;_}::uu____6635::[])
        when
        let uu____6648 = getBoxedInteger t0  in FStar_Util.is_some uu____6648
        ->
        let sz =
          let uu____6652 = getBoxedInteger t0  in
          match uu____6652 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6656 -> failwith "impossible"  in
        let uu____6659 =
          let uu____6664 = unboxBitVec sz t1  in
          let uu____6665 = unboxBitVec sz t2  in (uu____6664, uu____6665)  in
        mkBvUlt uu____6659 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___56_6669 = unboxBool t1  in
        {
          tm = (uu___56_6669.tm);
          freevars = (uu___56_6669.freevars);
          rng = (t.rng)
        }
    | uu____6670 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6719 = FStar_Options.unthrottle_inductives ()  in
        if uu____6719
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
      let uu____6830 =
        let uu____6837 = let uu____6840 = mkInteger' i norng  in [uu____6840]
           in
        ("FString_const", uu____6837)  in
      mkApp uu____6830 r
  
let (mk_Precedes : term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6858 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____6858 mk_Valid
  
let (mk_LexCons : term -> term -> FStar_Range.range -> term) =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6886 =
         let uu____6893 =
           let uu____6896 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____6896]  in
         ("SFuel", uu____6893)  in
       mkApp uu____6886 norng)
  
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
            let uu____6936 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____6936
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
      let uu____6997 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6997
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____7016 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____7016
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____7026 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____7026
  