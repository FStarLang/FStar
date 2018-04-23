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
let uu___is_Bool_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____34 -> false
  
let uu___is_Int_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____40 -> false
  
let uu___is_String_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____46 -> false
  
let uu___is_Term_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____52 -> false
  
let uu___is_Fuel_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____58 -> false
  
let uu___is_BitVec_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____65 -> false
  
let __proj__BitVec_sort__item___0 : sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let uu___is_Array : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____83 -> false
  
let __proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0 
let uu___is_Arrow : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____113 -> false
  
let __proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let uu___is_Sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____139 -> false
  
let __proj__Sort__item___0 : sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0 
let rec strSort : sort -> Prims.string =
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
let uu___is_TrueOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____183 -> false
  
let uu___is_FalseOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____189 -> false
  
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____195 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____201 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____207 -> false 
let uu___is_Imp : op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____213 -> false 
let uu___is_Iff : op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____219 -> false 
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____225 -> false 
let uu___is_LT : op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____231 -> false 
let uu___is_LTE : op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____237 -> false 
let uu___is_GT : op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____243 -> false 
let uu___is_GTE : op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____249 -> false 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____255 -> false 
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____261 -> false 
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____267 -> false 
let uu___is_Mul : op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____273 -> false 
let uu___is_Minus : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____279 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____285 -> false 
let uu___is_BvAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____291 -> false
  
let uu___is_BvXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____297 -> false
  
let uu___is_BvOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____303 -> false 
let uu___is_BvAdd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____309 -> false
  
let uu___is_BvSub : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____315 -> false
  
let uu___is_BvShl : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____321 -> false
  
let uu___is_BvShr : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____327 -> false
  
let uu___is_BvUdiv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____333 -> false
  
let uu___is_BvMod : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____339 -> false
  
let uu___is_BvMul : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____345 -> false
  
let uu___is_BvUlt : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____351 -> false
  
let uu___is_BvUext : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____358 -> false
  
let __proj__BvUext__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let uu___is_NatToBv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____372 -> false
  
let __proj__NatToBv__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let uu___is_BvToNat : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____385 -> false
  
let uu___is_ITE : op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____391 -> false 
let uu___is_Var : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____398 -> false
  
let __proj__Var__item___0 : op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists [@@deriving show]
let uu___is_Forall : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____411 -> false
  
let uu___is_Exists : qop -> Prims.bool =
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
let uu___is_Integer : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____552 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____566 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____584 -> false
  
let __proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____616 -> false
  
let __proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____666 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____740 -> false
  
let __proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____778 -> false
  
let __proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____814 -> false
  
let __proj__LblPos__item___0 :
  term' -> (term,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
let __proj__Mkterm__item__tm : term -> term' =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__tm
  
let __proj__Mkterm__item__freevars :
  term ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo
  =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__freevars
  
let __proj__Mkterm__item__rng : term -> FStar_Range.range =
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
let uu___is_Name : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____990 -> false
  
let __proj__Name__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Namespace : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1004 -> false
  
let __proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let uu___is_Tag : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1018 -> false
  
let __proj__Tag__item___0 : fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0 
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list }[@@deriving show]
let __proj__Mkassumption__item__assumption_term : assumption -> term =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_term
  
let __proj__Mkassumption__item__assumption_caption : assumption -> caption =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_caption
  
let __proj__Mkassumption__item__assumption_name : assumption -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_name
  
let __proj__Mkassumption__item__assumption_fact_ids :
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
  | GetReasonUnknown [@@deriving show]
let uu___is_DefPrelude : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1169 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1186 -> false
  
let __proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1242 -> false
  
let __proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1292 -> false
  
let __proj__Assume__item___0 : decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1306 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1320 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1334 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_RetainAssumptions : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1350 -> false
  
let __proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1369 -> false
  
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1375 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1381 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1387 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1398 -> false
  
let __proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_GetStatistics : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1423 -> false
  
let uu___is_GetReasonUnknown : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1429 -> false
  
type decls_t = decl Prims.list[@@deriving show]
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type error_labels = error_label Prims.list[@@deriving show]
let fv_eq : fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____1456 'Auu____1457 .
    ('Auu____1456,'Auu____1457) FStar_Pervasives_Native.tuple2 ->
      'Auu____1457
  = fun x  -> FStar_Pervasives_Native.snd x 
let freevar_eq : term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1491 -> false
  
let freevar_sort : term -> sort =
  fun uu___48_1500  ->
    match uu___48_1500 with
    | { tm = FreeV x; freevars = uu____1502; rng = uu____1503;_} -> fv_sort x
    | uu____1516 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___49_1521  ->
    match uu___49_1521 with
    | { tm = FreeV fv; freevars = uu____1523; rng = uu____1524;_} -> fv
    | uu____1537 -> failwith "impossible"
  
let rec freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
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
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____1629 = FStar_ST.op_Bang t.freevars  in
    match uu____1629 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1699 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1699  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___50_1748  ->
    match uu___50_1748 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___51_1753  ->
    match uu___51_1753 with
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
        let uu____1755 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1755
    | NatToBv n1 ->
        let uu____1757 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1757
    | Var s -> s
  
let weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___52_1765  ->
    match uu___52_1765 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1769 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1769
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1781 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1781
    | FreeV x ->
        let uu____1787 =
          let uu____1788 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1788  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1787
    | App (op,tms) ->
        let uu____1795 =
          let uu____1796 = op_to_string op  in
          let uu____1797 =
            let uu____1798 =
              let uu____1799 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1799 (FStar_String.concat " ")  in
            Prims.strcat uu____1798 ")"  in
          Prims.strcat uu____1796 uu____1797  in
        Prims.strcat "(" uu____1795
    | Labeled (t1,r1,r2) ->
        let uu____1807 = hash_of_term t1  in
        let uu____1808 =
          let uu____1809 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1809  in
        Prims.strcat uu____1807 uu____1808
    | LblPos (t1,r) ->
        let uu____1812 =
          let uu____1813 = hash_of_term t1  in
          Prims.strcat uu____1813
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1812
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1835 =
          let uu____1836 =
            let uu____1837 =
              let uu____1838 =
                let uu____1839 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1839 (FStar_String.concat " ")  in
              let uu____1844 =
                let uu____1845 =
                  let uu____1846 = hash_of_term body  in
                  let uu____1847 =
                    let uu____1848 =
                      let uu____1849 = weightToSmt wopt  in
                      let uu____1850 =
                        let uu____1851 =
                          let uu____1852 =
                            let uu____1853 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1869 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1869
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1853
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1852 "))"  in
                        Prims.strcat " " uu____1851  in
                      Prims.strcat uu____1849 uu____1850  in
                    Prims.strcat " " uu____1848  in
                  Prims.strcat uu____1846 uu____1847  in
                Prims.strcat ")(! " uu____1845  in
              Prims.strcat uu____1838 uu____1844  in
            Prims.strcat " (" uu____1837  in
          Prims.strcat (qop_to_string qop) uu____1836  in
        Prims.strcat "(" uu____1835
    | Let (es,body) ->
        let uu____1882 =
          let uu____1883 =
            let uu____1884 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1884 (FStar_String.concat " ")  in
          let uu____1889 =
            let uu____1890 =
              let uu____1891 = hash_of_term body  in
              Prims.strcat uu____1891 ")"  in
            Prims.strcat ") " uu____1890  in
          Prims.strcat uu____1883 uu____1889  in
        Prims.strcat "(let (" uu____1882

and hash_of_term : term -> Prims.string = fun tm  -> hash_of_term' tm.tm

let mkBoxFunctions :
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  = fun s  -> (s, (Prims.strcat s "_proj_0")) 
let boxIntFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  mkBoxFunctions "BoxInt" 
let boxBoolFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  mkBoxFunctions "BoxBool" 
let boxStringFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  = mkBoxFunctions "BoxString" 
let boxBitVecFun :
  Prims.int -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun sz  ->
    let uu____1923 =
      let uu____1924 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1924  in
    mkBoxFunctions uu____1923
  
let isInjective : Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.lift_native_int (3))
    then
      (let uu____1932 =
         FStar_String.substring s (Prims.lift_native_int (0))
           (Prims.lift_native_int (3))
          in
       uu____1932 = "Box") &&
        (let uu____1934 =
           let uu____1935 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1935  in
         Prims.op_Negation uu____1934)
    else false
  
let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1956 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1956; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____2025 =
        let uu____2026 = FStar_Util.ensure_decimal i  in Integer uu____2026
         in
      mk uu____2025 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____2037 = FStar_Util.string_of_int i  in mkInteger uu____2037 r
  
let mkBoundV : Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r 
let mkFreeV :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun x  -> fun r  -> mk (FreeV x) r 
let mkApp' :
  (op,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun f  -> fun r  -> mk (App f) r 
let mkApp :
  (Prims.string,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2102  ->
    fun r  -> match uu____2102 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2128) -> mkFalse r
      | App (FalseOp ,uu____2133) -> mkTrue r
      | uu____2138 -> mkApp' (Not, [t]) r
  
let mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2153  ->
    fun r  ->
      match uu____2153 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2161),uu____2162) -> t2
           | (uu____2167,App (TrueOp ,uu____2168)) -> t1
           | (App (FalseOp ,uu____2173),uu____2174) -> mkFalse r
           | (uu____2179,App (FalseOp ,uu____2180)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2197,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2206) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2213 -> mkApp' (And, [t1; t2]) r)
  
let mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2232  ->
    fun r  ->
      match uu____2232 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2240),uu____2241) -> mkTrue r
           | (uu____2246,App (TrueOp ,uu____2247)) -> mkTrue r
           | (App (FalseOp ,uu____2252),uu____2253) -> t2
           | (uu____2258,App (FalseOp ,uu____2259)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2276,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2285) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2292 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2311  ->
    fun r  ->
      match uu____2311 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2319,App (TrueOp ,uu____2320)) -> mkTrue r
           | (App (FalseOp ,uu____2325),uu____2326) -> mkTrue r
           | (App (TrueOp ,uu____2331),uu____2332) -> t2
           | (uu____2337,App (Imp ,t1'::t2'::[])) ->
               let uu____2342 =
                 let uu____2349 =
                   let uu____2352 = mkAnd (t1, t1') r  in [uu____2352; t2']
                    in
                 (Imp, uu____2349)  in
               mkApp' uu____2342 r
           | uu____2355 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2379  ->
      fun r  -> match uu____2379 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
let mkMinus : term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r 
let mkNatToBv : Prims.int -> term -> FStar_Range.range -> term =
  fun sz  -> fun t  -> fun r  -> mkApp' ((NatToBv sz), [t]) r 
let mkBvUext : Prims.int -> term -> FStar_Range.range -> term =
  fun sz  -> fun t  -> fun r  -> mkApp' ((BvUext sz), [t]) r 
let mkBvToNat : term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (BvToNat, [t]) r 
let mkBvAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvAnd 
let mkBvXor :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvXor 
let mkBvOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvOr 
let mkBvAdd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvAdd 
let mkBvSub :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvSub 
let mkBvShl :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2524  ->
      fun r  ->
        match uu____2524 with
        | (t1,t2) ->
            let uu____2532 =
              let uu____2539 =
                let uu____2542 =
                  let uu____2545 = mkNatToBv sz t2 r  in [uu____2545]  in
                t1 :: uu____2542  in
              (BvShl, uu____2539)  in
            mkApp' uu____2532 r
  
let mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2565  ->
      fun r  ->
        match uu____2565 with
        | (t1,t2) ->
            let uu____2573 =
              let uu____2580 =
                let uu____2583 =
                  let uu____2586 = mkNatToBv sz t2 r  in [uu____2586]  in
                t1 :: uu____2583  in
              (BvShr, uu____2580)  in
            mkApp' uu____2573 r
  
let mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2606  ->
      fun r  ->
        match uu____2606 with
        | (t1,t2) ->
            let uu____2614 =
              let uu____2621 =
                let uu____2624 =
                  let uu____2627 = mkNatToBv sz t2 r  in [uu____2627]  in
                t1 :: uu____2624  in
              (BvUdiv, uu____2621)  in
            mkApp' uu____2614 r
  
let mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2647  ->
      fun r  ->
        match uu____2647 with
        | (t1,t2) ->
            let uu____2655 =
              let uu____2662 =
                let uu____2665 =
                  let uu____2668 = mkNatToBv sz t2 r  in [uu____2668]  in
                t1 :: uu____2665  in
              (BvMod, uu____2662)  in
            mkApp' uu____2655 r
  
let mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2688  ->
      fun r  ->
        match uu____2688 with
        | (t1,t2) ->
            let uu____2696 =
              let uu____2703 =
                let uu____2706 =
                  let uu____2709 = mkNatToBv sz t2 r  in [uu____2709]  in
                t1 :: uu____2706  in
              (BvMul, uu____2703)  in
            mkApp' uu____2696 r
  
let mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt 
let mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff 
let mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2748  ->
    fun r  ->
      match uu____2748 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2764 -> mk_bin_op Eq (t1, t2) r)
  
let mkLT :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LT 
let mkLTE :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LTE 
let mkGT :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GT 
let mkGTE :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GTE 
let mkAdd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Add 
let mkSub :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Sub 
let mkDiv :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Div 
let mkMul :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mul 
let mkMod :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mod 
let mkITE :
  (term,term,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2891  ->
    fun r  ->
      match uu____2891 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2902) -> t2
           | App (FalseOp ,uu____2907) -> t3
           | uu____2912 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2913),App (TrueOp ,uu____2914)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2923),uu____2924) ->
                    let uu____2929 =
                      let uu____2934 = mkNot t1 t1.rng  in (uu____2934, t3)
                       in
                    mkImp uu____2929 r
                | (uu____2935,App (TrueOp ,uu____2936)) -> mkImp (t1, t2) r
                | (uu____2941,uu____2942) -> mkApp' (ITE, [t1; t2; t3]) r))
  
let mkCases : term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
  
let mkQuant :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2993  ->
    fun r  ->
      match uu____2993 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.lift_native_int (0))
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____3035) -> body
             | uu____3040 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____3063  ->
    fun r  ->
      match uu____3063 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.lift_native_int (0))
          then body
          else mk (Let (es, body)) r
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____3103 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____3103 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.lift_native_int (1))))
         in
      let rec aux ix t1 =
        let uu____3126 = FStar_ST.op_Bang t1.freevars  in
        match uu____3126 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3184 ->
            (match t1.tm with
             | Integer uu____3193 -> t1
             | BoundV uu____3194 -> t1
             | FreeV x ->
                 let uu____3200 = index_of x  in
                 (match uu____3200 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3210 =
                   let uu____3217 = FStar_List.map (aux ix) tms  in
                   (op, uu____3217)  in
                 mkApp' uu____3210 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3225 =
                   let uu____3226 =
                     let uu____3233 = aux ix t2  in (uu____3233, r1, r2)  in
                   Labeled uu____3226  in
                 mk uu____3225 t2.rng
             | LblPos (t2,r) ->
                 let uu____3236 =
                   let uu____3237 =
                     let uu____3242 = aux ix t2  in (uu____3242, r)  in
                   LblPos uu____3237  in
                 mk uu____3236 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3265 =
                   let uu____3284 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3305 = aux (ix + n1) body  in
                   (qop, uu____3284, wopt, vars, uu____3305)  in
                 mkQuant uu____3265 t1.rng
             | Let (es,body) ->
                 let uu____3324 =
                   FStar_List.fold_left
                     (fun uu____3342  ->
                        fun e  ->
                          match uu____3342 with
                          | (ix1,l) ->
                              let uu____3362 =
                                let uu____3365 = aux ix1 e  in uu____3365 ::
                                  l
                                 in
                              ((ix1 + (Prims.lift_native_int (1))),
                                uu____3362)) (ix, []) es
                    in
                 (match uu____3324 with
                  | (ix1,es_rev) ->
                      let uu____3376 =
                        let uu____3383 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3383)  in
                      mkLet uu____3376 t1.rng))
         in
      aux (Prims.lift_native_int (0)) t
  
let inst : term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3415 -> t1
        | FreeV uu____3416 -> t1
        | BoundV i ->
            if
              ((Prims.lift_native_int (0)) <= (i - shift)) &&
                ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3433 =
              let uu____3440 = FStar_List.map (aux shift) tms2  in
              (op, uu____3440)  in
            mkApp' uu____3433 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3448 =
              let uu____3449 =
                let uu____3456 = aux shift t2  in (uu____3456, r1, r2)  in
              Labeled uu____3449  in
            mk uu____3448 t2.rng
        | LblPos (t2,r) ->
            let uu____3459 =
              let uu____3460 =
                let uu____3465 = aux shift t2  in (uu____3465, r)  in
              LblPos uu____3460  in
            mk uu____3459 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3493 =
              let uu____3512 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3529 = aux shift1 body  in
              (qop, uu____3512, wopt, vars, uu____3529)  in
            mkQuant uu____3493 t1.rng
        | Let (es,body) ->
            let uu____3544 =
              FStar_List.fold_left
                (fun uu____3562  ->
                   fun e  ->
                     match uu____3562 with
                     | (ix,es1) ->
                         let uu____3582 =
                           let uu____3585 = aux shift e  in uu____3585 :: es1
                            in
                         ((shift + (Prims.lift_native_int (1))), uu____3582))
                (shift, []) es
               in
            (match uu____3544 with
             | (shift1,es_rev) ->
                 let uu____3596 =
                   let uu____3603 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3603)  in
                 mkLet uu____3596 t1.rng)
         in
      aux (Prims.lift_native_int (0)) t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3621 = abstr [fv] t  in inst [s] uu____3621
  
let mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3647  ->
    match uu____3647 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3690 =
          let uu____3709 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3726 = FStar_List.map fv_sort vars  in
          let uu____3733 = abstr vars body  in
          (qop, uu____3709, wopt, uu____3726, uu____3733)  in
        mkQuant uu____3690
  
let mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3766  ->
    fun r  ->
      match uu____3766 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3834  ->
    fun r  ->
      match uu____3834 with
      | (pats,wopt,vars,body) ->
          let uu____3866 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3866 r
  
let mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3895  ->
    fun r  ->
      match uu____3895 with
      | (pats,vars,body) ->
          let uu____3918 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3918 r
  
let mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3947  ->
    fun r  ->
      match uu____3947 with
      | (pats,vars,body) ->
          let uu____3970 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3970 r
  
let mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3999  ->
    fun r  ->
      match uu____3999 with
      | (bindings,body) ->
          let uu____4025 = FStar_List.split bindings  in
          (match uu____4025 with
           | (vars,es) ->
               let uu____4044 =
                 let uu____4051 = abstr vars body  in (es, uu____4051)  in
               mkLet uu____4044 r)
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____4074  ->
    match uu____4074 with
    | (nm,vars,s,tm,c) ->
        let uu____4108 =
          let uu____4121 = FStar_List.map fv_sort vars  in
          let uu____4128 = abstr vars tm  in
          (nm, uu____4121, s, uu____4128, c)  in
        DefineFun uu____4108
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let uu____4136 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____4136
  
let fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____4149  ->
    fun id1  ->
      match uu____4149 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____4159 =
              let uu____4160 =
                let uu____4165 = mkInteger' id1 norng  in
                let uu____4166 =
                  let uu____4167 =
                    let uu____4174 = constr_id_of_sort sort  in
                    let uu____4175 =
                      let uu____4178 = mkApp (tok_name, []) norng  in
                      [uu____4178]  in
                    (uu____4174, uu____4175)  in
                  mkApp uu____4167 norng  in
                (uu____4165, uu____4166)  in
              mkEq uu____4160 norng  in
            {
              assumption_term = uu____4159;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            }  in
          Assume a
  
let fresh_constructor :
  (Prims.string,sort Prims.list,sort,Prims.int)
    FStar_Pervasives_Native.tuple4 -> decl
  =
  fun uu____4197  ->
    match uu____4197 with
    | (name,arg_sorts,sort,id1) ->
        let id2 = FStar_Util.string_of_int id1  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____4229 =
                      let uu____4234 =
                        let uu____4235 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____4235  in
                      (uu____4234, s)  in
                    mkFreeV uu____4229 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____4243 =
            let uu____4250 = constr_id_of_sort sort  in (uu____4250, [capp])
             in
          mkApp uu____4243 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____4255 =
            let uu____4256 =
              let uu____4267 =
                let uu____4268 =
                  let uu____4273 = mkInteger id2 norng  in
                  (uu____4273, cid_app)  in
                mkEq uu____4268 norng  in
              ([[capp]], bvar_names, uu____4267)  in
            mkForall uu____4256 norng  in
          {
            assumption_term = uu____4255;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          }  in
        Assume a
  
let injective_constructor :
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decls_t
  =
  fun uu____4296  ->
    match uu____4296 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____4319 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____4319  in
        let bvar_index i = n_bvars - (i + (Prims.lift_native_int (1)))  in
        let bvar i s =
          let uu____4346 = let uu____4351 = bvar_name i  in (uu____4351, s)
             in
          mkFreeV uu____4346  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4372  ->
                    match uu____4372 with
                    | (uu____4379,s,uu____4381) ->
                        let uu____4382 = bvar i s  in uu____4382 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____4393 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4421  ->
                    match uu____4421 with
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
                            let uu____4444 =
                              let uu____4445 =
                                let uu____4456 =
                                  let uu____4457 =
                                    let uu____4462 =
                                      let uu____4463 = bvar i s  in
                                      uu____4463 norng  in
                                    (cproj_app, uu____4462)  in
                                  mkEq uu____4457 norng  in
                                ([[capp]], bvar_names, uu____4456)  in
                              mkForall uu____4445 norng  in
                            {
                              assumption_term = uu____4444;
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
        FStar_All.pipe_right uu____4393 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decls_t =
  fun uu____4489  ->
    match uu____4489 with
    | (name,fields,sort,id1,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4517  ->
                  match uu____4517 with
                  | (uu____4524,sort1,uu____4526) -> sort1))
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
            let uu____4544 =
              let uu____4549 =
                let uu____4550 =
                  let uu____4557 = constr_id_of_sort sort  in
                  (uu____4557, [xx])  in
                mkApp uu____4550 norng  in
              let uu____4560 =
                let uu____4561 = FStar_Util.string_of_int id1  in
                mkInteger uu____4561 norng  in
              (uu____4549, uu____4560)  in
            mkEq uu____4544 norng  in
          let uu____4562 =
            let uu____4577 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4627  ->
                        match uu____4627 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4657 = mkApp (proj, [xx]) norng  in
                              (uu____4657, [])
                            else
                              (let fi =
                                 let uu____4676 =
                                   let uu____4677 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4677  in
                                 (uu____4676, s)  in
                               let uu____4678 = mkFreeV fi norng  in
                               (uu____4678, [fi]))))
               in
            FStar_All.pipe_right uu____4577 FStar_List.split  in
          match uu____4562 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4759 =
                  let uu____4764 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4764)  in
                mkEq uu____4759 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4772 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____4813 =
          let uu____4816 =
            let uu____4817 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4817  in
          uu____4816 :: cdecl :: cid :: projs  in
        let uu____4818 =
          let uu____4821 =
            let uu____4824 =
              let uu____4825 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4825  in
            [uu____4824]  in
          FStar_List.append [disc] uu____4821  in
        FStar_List.append uu____4813 uu____4818
  
let name_binders_inner :
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
          let uu____4880 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4935  ->
                    fun s  ->
                      match uu____4935 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4985 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4989 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4989  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____5002 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____5002  in
                          (names2, (b :: binders),
                            (n1 + (Prims.lift_native_int (1)))))
                 (outer_names, [], start))
             in
          match uu____4880 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____5081 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.lift_native_int (0)) sorts
       in
    match uu____5081 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let termToSmt : Prims.bool -> Prims.string -> term -> Prims.string =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref (Prims.lift_native_int (0))  in
          fun depth  ->
            let n1 = FStar_ST.op_Bang ctr  in
            FStar_Util.incr ctr;
            if n1 = (Prims.lift_native_int (0))
            then enclosing_name
            else
              (let uu____5248 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5248)
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
                               "Prims.guard_free",{ tm = BoundV uu____5292;
                                                    freevars = uu____5293;
                                                    rng = uu____5294;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5308 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.lift_native_int (1)))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5370 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5370 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5385 = op_to_string op  in
              let uu____5386 =
                let uu____5387 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5387 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5385 uu____5386
          | Labeled (t2,uu____5393,uu____5394) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5397 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5397 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5420 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5420 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5469 ->
                         let uu____5474 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5490 =
                                     let uu____5491 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5497 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5497) pats2
                                        in
                                     FStar_String.concat " " uu____5491  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5490))
                            in
                         FStar_All.pipe_right uu____5474
                           (FStar_String.concat "\n")
                      in
                   let uu____5500 =
                     let uu____5503 =
                       let uu____5506 =
                         let uu____5509 = aux1 n2 names2 body  in
                         let uu____5510 =
                           let uu____5513 = weightToSmt wopt  in
                           [uu____5513; pats_str; qid]  in
                         uu____5509 :: uu____5510  in
                       binders1 :: uu____5506  in
                     (qop_to_string qop) :: uu____5503  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5500)
          | Let (es,body) ->
              let uu____5520 =
                FStar_List.fold_left
                  (fun uu____5557  ->
                     fun e  ->
                       match uu____5557 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5607 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5607  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5620 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5620  in
                           (names01, (b :: binders),
                             (n0 + (Prims.lift_native_int (1)))))
                  (names1, [], n1) es
                 in
              (match uu____5520 with
               | (names2,binders,n2) ->
                   let uu____5652 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5652)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5660 = FStar_Range.string_of_range t1.rng  in
            let uu____5661 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5660
              uu____5661 s
          else s
         in aux (Prims.lift_native_int (0)) (Prims.lift_native_int (0)) [] t
  
let caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___53_5669  ->
    match uu___53_5669 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c "\n")
  
let rec declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string =
  fun print_ranges  ->
    fun z3options  ->
      fun decl  ->
        let escape s = FStar_Util.replace_char s 39 95  in
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Caption c ->
            let uu____5717 = FStar_Options.log_queries ()  in
            if uu____5717
            then
              let uu____5718 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___54_5722  ->
                     match uu___54_5722 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5718
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____5741 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)"
              (caption_to_string c) f (FStar_String.concat " " l) uu____5741
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____5751 = name_macro_binders arg_sorts  in
            (match uu____5751 with
             | (names1,binders) ->
                 let body1 =
                   let uu____5783 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____5783 body  in
                 let uu____5796 = strSort retsort  in
                 let uu____5797 = termToSmt print_ranges (escape f) body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   (caption_to_string c) f (FStar_String.concat " " binders)
                   uu____5796 uu____5797)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___55_5818  ->
                      match uu___55_5818 with
                      | Name n1 ->
                          let uu____5820 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____5820
                      | Namespace ns ->
                          let uu____5822 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____5822
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____5825 = FStar_Options.log_queries ()  in
              if uu____5825
              then
                let uu____5826 =
                  let uu____5827 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____5827  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5826
              else ""  in
            let n1 = escape a.assumption_name  in
            let uu____5832 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))"
              (caption_to_string a.assumption_caption) fids uu____5832 n1
        | Eval t ->
            let uu____5834 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____5834
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____5836 -> ""
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

and declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  -> fun decl  -> declToSmt' true z3options decl

and declToSmt_no_caps : Prims.string -> decl -> Prims.string =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and mkPrelude : Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
       in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.lift_native_int (0)), true);
      ("Tm_type", [], Term_sort, (Prims.lift_native_int (2)), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.lift_native_int (3)), false);
      ("Tm_unit", [], Term_sort, (Prims.lift_native_int (6)), true);
      ((FStar_Pervasives_Native.fst boxIntFun),
        [((FStar_Pervasives_Native.snd boxIntFun), Int_sort, true)],
        Term_sort, (Prims.lift_native_int (7)), true);
      ((FStar_Pervasives_Native.fst boxBoolFun),
        [((FStar_Pervasives_Native.snd boxBoolFun), Bool_sort, true)],
        Term_sort, (Prims.lift_native_int (8)), true);
      ((FStar_Pervasives_Native.fst boxStringFun),
        [((FStar_Pervasives_Native.snd boxStringFun), String_sort, true)],
        Term_sort, (Prims.lift_native_int (9)), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.lift_native_int (11)), true)]
       in
    let bcons =
      let uu____6165 =
        let uu____6168 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____6168
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____6165 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let mkBvConstructor : Prims.int -> decls_t =
  fun sz  ->
    let uu____6185 =
      let uu____6204 =
        let uu____6205 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6205  in
      let uu____6210 =
        let uu____6219 =
          let uu____6226 =
            let uu____6227 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____6227  in
          (uu____6226, (BitVec_sort sz), true)  in
        [uu____6219]  in
      (uu____6204, uu____6210, Term_sort,
        ((Prims.lift_native_int (12)) + sz), true)
       in
    FStar_All.pipe_right uu____6185 constructor_to_decl
  
let __range_c : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.lift_native_int (0)) 
let mk_Range_const : unit -> term =
  fun uu____6287  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____6313 =
       let uu____6314 = FStar_ST.op_Bang __range_c  in
       uu____6314 + (Prims.lift_native_int (1))  in
     FStar_ST.op_Colon_Equals __range_c uu____6313);
    (let uu____6361 =
       let uu____6368 = let uu____6371 = mkInteger' i norng  in [uu____6371]
          in
       ("Range_const", uu____6368)  in
     mkApp uu____6361 norng)
  
let mk_Term_type : term = mkApp ("Tm_type", []) norng 
let mk_Term_app : term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let mk_Term_uvar : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____6403 =
        let uu____6410 = let uu____6413 = mkInteger' i norng  in [uu____6413]
           in
        ("Tm_uvar", uu____6410)  in
      mkApp uu____6403 r
  
let mk_Term_unit : term = mkApp ("Tm_unit", []) norng 
let elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6442 -> mkApp (u, [t]) t.rng
  
let maybe_elim_box : Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6460 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6460 u v1 t
  
let boxInt : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun)
      (FStar_Pervasives_Native.snd boxIntFun) t
  
let unboxInt : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun)
      (FStar_Pervasives_Native.fst boxIntFun) t
  
let boxBool : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun)
      (FStar_Pervasives_Native.snd boxBoolFun) t
  
let unboxBool : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun)
      (FStar_Pervasives_Native.fst boxBoolFun) t
  
let boxString : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun)
      (FStar_Pervasives_Native.snd boxStringFun) t
  
let unboxString : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun)
      (FStar_Pervasives_Native.fst boxStringFun) t
  
let boxBitVec : Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6501 =
        let uu____6502 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6502  in
      let uu____6507 =
        let uu____6508 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6508  in
      elim_box true uu____6501 uu____6507 t
  
let unboxBitVec : Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6523 =
        let uu____6524 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6524  in
      let uu____6529 =
        let uu____6530 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6530  in
      elim_box true uu____6523 uu____6529 t
  
let boxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6546 -> FStar_Exn.raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6558 -> FStar_Exn.raise FStar_Util.Impos
  
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6580 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____6580
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6592 = op_to_string op  in
        let uu____6593 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____6592 uu____6593
    | Labeled (t1,r1,r2) ->
        let uu____6597 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6597
    | LblPos (t1,s) ->
        let uu____6600 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6600
    | Quant (qop,l,uu____6603,uu____6604,t1) ->
        let uu____6622 = print_smt_term_list_list l  in
        let uu____6623 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6622
          uu____6623
    | Let (es,body) ->
        let uu____6630 = print_smt_term_list es  in
        let uu____6631 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____6630 uu____6631

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let uu____6635 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____6635 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6654 =
             let uu____6655 =
               let uu____6656 = print_smt_term_list l1  in
               Prims.strcat uu____6656 " ] "  in
             Prims.strcat "; [ " uu____6655  in
           Prims.strcat s uu____6654) "" l

let getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6673 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6673
         | uu____6674 -> FStar_Pervasives_Native.None)
    | uu____6675 -> FStar_Pervasives_Native.None
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6688::t1::t2::[]);
                       freevars = uu____6691; rng = uu____6692;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6705::t1::t2::[]);
                       freevars = uu____6708; rng = uu____6709;_}::[])
        -> let uu____6722 = mkEq (t1, t2) norng  in mkNot uu____6722 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6725; rng = uu____6726;_}::[])
        ->
        let uu____6739 =
          let uu____6744 = unboxInt t1  in
          let uu____6745 = unboxInt t2  in (uu____6744, uu____6745)  in
        mkLTE uu____6739 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6748; rng = uu____6749;_}::[])
        ->
        let uu____6762 =
          let uu____6767 = unboxInt t1  in
          let uu____6768 = unboxInt t2  in (uu____6767, uu____6768)  in
        mkLT uu____6762 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6771; rng = uu____6772;_}::[])
        ->
        let uu____6785 =
          let uu____6790 = unboxInt t1  in
          let uu____6791 = unboxInt t2  in (uu____6790, uu____6791)  in
        mkGTE uu____6785 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6794; rng = uu____6795;_}::[])
        ->
        let uu____6808 =
          let uu____6813 = unboxInt t1  in
          let uu____6814 = unboxInt t2  in (uu____6813, uu____6814)  in
        mkGT uu____6808 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6817; rng = uu____6818;_}::[])
        ->
        let uu____6831 =
          let uu____6836 = unboxBool t1  in
          let uu____6837 = unboxBool t2  in (uu____6836, uu____6837)  in
        mkAnd uu____6831 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6840; rng = uu____6841;_}::[])
        ->
        let uu____6854 =
          let uu____6859 = unboxBool t1  in
          let uu____6860 = unboxBool t2  in (uu____6859, uu____6860)  in
        mkOr uu____6854 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6862; rng = uu____6863;_}::[])
        -> let uu____6876 = unboxBool t1  in mkNot uu____6876 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6880; rng = uu____6881;_}::[])
        when
        let uu____6894 = getBoxedInteger t0  in FStar_Util.is_some uu____6894
        ->
        let sz =
          let uu____6898 = getBoxedInteger t0  in
          match uu____6898 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6902 -> failwith "impossible"  in
        let uu____6905 =
          let uu____6910 = unboxBitVec sz t1  in
          let uu____6911 = unboxBitVec sz t2  in (uu____6910, uu____6911)  in
        mkBvUlt uu____6905 t.rng
    | App
        (Var
         "Prims.equals",uu____6912::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6916;
                                      rng = uu____6917;_}::uu____6918::[])
        when
        let uu____6931 = getBoxedInteger t0  in FStar_Util.is_some uu____6931
        ->
        let sz =
          let uu____6935 = getBoxedInteger t0  in
          match uu____6935 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6939 -> failwith "impossible"  in
        let uu____6942 =
          let uu____6947 = unboxBitVec sz t1  in
          let uu____6948 = unboxBitVec sz t2  in (uu____6947, uu____6948)  in
        mkBvUlt uu____6942 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___56_6952 = unboxBool t1  in
        {
          tm = (uu___56_6952.tm);
          freevars = (uu___56_6952.freevars);
          rng = (t.rng)
        }
    | uu____6953 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let mk_IsTyped : term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____7002 = FStar_Options.unthrottle_inductives ()  in
        if uu____7002
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
  
let mk_HasTypeWithFuel :
  term FStar_Pervasives_Native.option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | FStar_Pervasives_Native.None  -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
  
let mk_NoHoist : term -> term -> term =
  fun dummy  -> fun b  -> mkApp ("NoHoist", [dummy; b]) b.rng 
let mk_Destruct : term -> FStar_Range.range -> term =
  fun v1  -> mkApp ("Destruct", [v1]) 
let mk_Rank : term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x]) 
let mk_tester : Prims.string -> term -> term =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng 
let mk_ApplyTF : term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng 
let mk_ApplyTT : term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r 
let kick_partial_app : term -> term =
  fun t  ->
    let uu____7108 =
      let uu____7109 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____7109 t t.rng  in
    FStar_All.pipe_right uu____7108 mk_Valid
  
let mk_String_const : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____7122 =
        let uu____7129 = let uu____7132 = mkInteger' i norng  in [uu____7132]
           in
        ("FString_const", uu____7129)  in
      mkApp uu____7122 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____7150 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____7150 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.lift_native_int (0))
    then mkApp ("ZFuel", []) norng
    else
      (let uu____7178 =
         let uu____7185 =
           let uu____7188 = n_fuel (n1 - (Prims.lift_native_int (1)))  in
           [uu____7188]  in
         ("SFuel", uu____7185)  in
       mkApp uu____7178 norng)
  
let fuel_2 : term = n_fuel (Prims.lift_native_int (2)) 
let fuel_100 : term = n_fuel (Prims.lift_native_int (100)) 
let mk_and_opt :
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
            let uu____7228 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____7228
        | (FStar_Pervasives_Native.Some p,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.None
  
let mk_and_opt_l :
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
  
let mk_and_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____7289 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____7289
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____7308 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____7308
  
let mk_haseq : term -> term =
  fun t  ->
    let uu____7318 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____7318
  