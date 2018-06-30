open Prims
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
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
let (uu___is_Bool_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____41 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____53 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____59 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____65 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____72 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____90 -> false
  
let (__proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____120 -> false
  
let (__proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____146 -> false
  
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
        let uu____160 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____160
    | Array (s1,s2) ->
        let uu____163 = strSort s1  in
        let uu____164 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____163 uu____164
    | Arrow (s1,s2) ->
        let uu____167 = strSort s1  in
        let uu____168 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____167 uu____168
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
  | Var of Prims.string 
let (uu___is_TrueOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____190 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____196 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____202 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____208 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____214 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____220 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____226 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____232 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____238 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____244 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____250 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____256 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____262 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____268 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____274 -> false 
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____280 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____286 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____292 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____298 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____304 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____310 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____316 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____322 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____328 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____334 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____340 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____346 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____352 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____358 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____365 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____379 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____392 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____398 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____405 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____418 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____424 -> false
  
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
  tm: term' ;
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo
    ;
  rng: FStar_Range.range }
let (uu___is_Integer : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____559 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____573 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____591 -> false
  
let (__proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____623 -> false
  
let (__proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____673 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____747 -> false
  
let (__proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____785 -> false
  
let (__proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____821 -> false
  
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
let (uu___is_Name : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____997 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1011 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1025 -> false
  
let (__proj__Tag__item___0 : fact_db_id -> Prims.string) =
  fun projectee  -> match projectee with | Tag _0 -> _0 
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list }
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
  | GetReasonUnknown 
let (uu___is_DefPrelude : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1176 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1193 -> false
  
let (__proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1249 -> false
  
let (__proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1299 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1313 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1327 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1341 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1357 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1376 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1382 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1388 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1394 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1405 -> false
  
let (__proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1430 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1436 -> false
  
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____1463 'Auu____1464 .
    ('Auu____1463,'Auu____1464) FStar_Pervasives_Native.tuple2 ->
      'Auu____1464
  = fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1498 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___114_1507  ->
    match uu___114_1507 with
    | { tm = FreeV x; freevars = uu____1509; rng = uu____1510;_} -> fv_sort x
    | uu____1523 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___115_1528  ->
    match uu___115_1528 with
    | { tm = FreeV fv; freevars = uu____1530; rng = uu____1531;_} -> fv
    | uu____1544 -> failwith "impossible"
  
let rec (freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____1562 -> []
    | BoundV uu____1567 -> []
    | FreeV fv -> [fv]
    | App (uu____1585,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1595,uu____1596,uu____1597,uu____1598,t1) -> freevars t1
    | Labeled (t1,uu____1617,uu____1618) -> freevars t1
    | LblPos (t1,uu____1620) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____1636 = FStar_ST.op_Bang t.freevars  in
    match uu____1636 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1706 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1706  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___116_1763  ->
    match uu___116_1763 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___117_1768  ->
    match uu___117_1768 with
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
        let uu____1770 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1770
    | NatToBv n1 ->
        let uu____1772 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1772
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___118_1780  ->
    match uu___118_1780 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1784 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1784
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1796 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1796
    | FreeV x ->
        let uu____1802 =
          let uu____1803 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1803  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1802
    | App (op,tms) ->
        let uu____1810 =
          let uu____1811 = op_to_string op  in
          let uu____1812 =
            let uu____1813 =
              let uu____1814 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1814 (FStar_String.concat " ")  in
            Prims.strcat uu____1813 ")"  in
          Prims.strcat uu____1811 uu____1812  in
        Prims.strcat "(" uu____1810
    | Labeled (t1,r1,r2) ->
        let uu____1822 = hash_of_term t1  in
        let uu____1823 =
          let uu____1824 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1824  in
        Prims.strcat uu____1822 uu____1823
    | LblPos (t1,r) ->
        let uu____1827 =
          let uu____1828 = hash_of_term t1  in
          Prims.strcat uu____1828
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1827
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1850 =
          let uu____1851 =
            let uu____1852 =
              let uu____1853 =
                let uu____1854 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1854 (FStar_String.concat " ")  in
              let uu____1859 =
                let uu____1860 =
                  let uu____1861 = hash_of_term body  in
                  let uu____1862 =
                    let uu____1863 =
                      let uu____1864 = weightToSmt wopt  in
                      let uu____1865 =
                        let uu____1866 =
                          let uu____1867 =
                            let uu____1868 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1884 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1884
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1868
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1867 "))"  in
                        Prims.strcat " " uu____1866  in
                      Prims.strcat uu____1864 uu____1865  in
                    Prims.strcat " " uu____1863  in
                  Prims.strcat uu____1861 uu____1862  in
                Prims.strcat ")(! " uu____1860  in
              Prims.strcat uu____1853 uu____1859  in
            Prims.strcat " (" uu____1852  in
          Prims.strcat (qop_to_string qop) uu____1851  in
        Prims.strcat "(" uu____1850
    | Let (es,body) ->
        let uu____1897 =
          let uu____1898 =
            let uu____1899 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1899 (FStar_String.concat " ")  in
          let uu____1904 =
            let uu____1905 =
              let uu____1906 = hash_of_term body  in
              Prims.strcat uu____1906 ")"  in
            Prims.strcat ") " uu____1905  in
          Prims.strcat uu____1898 uu____1904  in
        Prims.strcat "(let (" uu____1897

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
    let uu____1938 =
      let uu____1939 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1939  in
    mkBoxFunctions uu____1938
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1947 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1947 = "Box") &&
        (let uu____1949 =
           let uu____1950 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____1950  in
         Prims.op_Negation uu____1949)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____1971 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1971; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2040 =
        let uu____2041 = FStar_Util.ensure_decimal i  in Integer uu____2041
         in
      mk uu____2040 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2052 = FStar_Util.string_of_int i  in mkInteger uu____2052 r
  
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
  fun uu____2117  ->
    fun r  -> match uu____2117 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2143) -> mkFalse r
      | App (FalseOp ,uu____2148) -> mkTrue r
      | uu____2153 -> mkApp' (Not, [t]) r
  
let (mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2168  ->
    fun r  ->
      match uu____2168 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2176),uu____2177) -> t2
           | (uu____2182,App (TrueOp ,uu____2183)) -> t1
           | (App (FalseOp ,uu____2188),uu____2189) -> mkFalse r
           | (uu____2194,App (FalseOp ,uu____2195)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2212,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2221) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2228 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2247  ->
    fun r  ->
      match uu____2247 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2255),uu____2256) -> mkTrue r
           | (uu____2261,App (TrueOp ,uu____2262)) -> mkTrue r
           | (App (FalseOp ,uu____2267),uu____2268) -> t2
           | (uu____2273,App (FalseOp ,uu____2274)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2291,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2300) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2307 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2326  ->
    fun r  ->
      match uu____2326 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2334,App (TrueOp ,uu____2335)) -> mkTrue r
           | (App (FalseOp ,uu____2340),uu____2341) -> mkTrue r
           | (App (TrueOp ,uu____2346),uu____2347) -> t2
           | (uu____2352,App (Imp ,t1'::t2'::[])) ->
               let uu____2357 =
                 let uu____2364 =
                   let uu____2367 = mkAnd (t1, t1') r  in [uu____2367; t2']
                    in
                 (Imp, uu____2364)  in
               mkApp' uu____2357 r
           | uu____2370 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun op  ->
    fun uu____2394  ->
      fun r  -> match uu____2394 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____2539  ->
      fun r  ->
        match uu____2539 with
        | (t1,t2) ->
            let uu____2547 =
              let uu____2554 =
                let uu____2557 =
                  let uu____2560 = mkNatToBv sz t2 r  in [uu____2560]  in
                t1 :: uu____2557  in
              (BvShl, uu____2554)  in
            mkApp' uu____2547 r
  
let (mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2580  ->
      fun r  ->
        match uu____2580 with
        | (t1,t2) ->
            let uu____2588 =
              let uu____2595 =
                let uu____2598 =
                  let uu____2601 = mkNatToBv sz t2 r  in [uu____2601]  in
                t1 :: uu____2598  in
              (BvShr, uu____2595)  in
            mkApp' uu____2588 r
  
let (mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2621  ->
      fun r  ->
        match uu____2621 with
        | (t1,t2) ->
            let uu____2629 =
              let uu____2636 =
                let uu____2639 =
                  let uu____2642 = mkNatToBv sz t2 r  in [uu____2642]  in
                t1 :: uu____2639  in
              (BvUdiv, uu____2636)  in
            mkApp' uu____2629 r
  
let (mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2662  ->
      fun r  ->
        match uu____2662 with
        | (t1,t2) ->
            let uu____2670 =
              let uu____2677 =
                let uu____2680 =
                  let uu____2683 = mkNatToBv sz t2 r  in [uu____2683]  in
                t1 :: uu____2680  in
              (BvMod, uu____2677)  in
            mkApp' uu____2670 r
  
let (mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun sz  ->
    fun uu____2703  ->
      fun r  ->
        match uu____2703 with
        | (t1,t2) ->
            let uu____2711 =
              let uu____2718 =
                let uu____2721 =
                  let uu____2724 = mkNatToBv sz t2 r  in [uu____2724]  in
                t1 :: uu____2721  in
              (BvMul, uu____2718)  in
            mkApp' uu____2711 r
  
let (mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op BvUlt 
let (mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  mk_bin_op Iff 
let (mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term) =
  fun uu____2763  ->
    fun r  ->
      match uu____2763 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2779 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2906  ->
    fun r  ->
      match uu____2906 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2917) -> t2
           | App (FalseOp ,uu____2922) -> t3
           | uu____2927 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2928),App (TrueOp ,uu____2929)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2938),uu____2939) ->
                    let uu____2944 =
                      let uu____2949 = mkNot t1 t1.rng  in (uu____2949, t3)
                       in
                    mkImp uu____2944 r
                | (uu____2950,App (TrueOp ,uu____2951)) -> mkImp (t1, t2) r
                | (uu____2956,uu____2957) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____3010 -> FStar_Pervasives_Native.None
      | BoundV uu____3011 -> FStar_Pervasives_Native.None
      | FreeV uu____3012 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____3030 -> true
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
            | BvUext uu____3031 -> false
            | NatToBv uu____3032 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____3037,uu____3038) -> aux t2
      | Quant uu____3039 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____3058 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____3072 = aux t1  in
          (match uu____3072 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3099 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____3099
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____3111 = op_to_string op  in
        let uu____3112 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____3111 uu____3112
    | Labeled (t1,r1,r2) ->
        let uu____3116 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3116
    | LblPos (t1,s) ->
        let uu____3119 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3119
    | Quant (qop,l,uu____3122,uu____3123,t1) ->
        let uu____3141 = print_smt_term_list_list l  in
        let uu____3142 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3141
          uu____3142
    | Let (es,body) ->
        let uu____3149 = print_smt_term_list es  in
        let uu____3150 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____3149 uu____3150

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____3154 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____3154 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3173 =
             let uu____3174 =
               let uu____3175 = print_smt_term_list l1  in
               Prims.strcat uu____3175 " ] "  in
             Prims.strcat "; [ " uu____3174  in
           Prims.strcat s uu____3173) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop,term Prims.list Prims.list,Prims.int
                                        FStar_Pervasives_Native.option,
        sort Prims.list,term) FStar_Pervasives_Native.tuple5 -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____3208  ->
        match uu____3208 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____3271 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____3271 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____3286 =
                         let uu____3291 =
                           let uu____3292 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____3292
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____3291)
                          in
                       FStar_Errors.log_issue r uu____3286);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____3296) -> body
               | uu____3301 ->
                   let uu____3302 =
                     let uu____3303 =
                       let uu____3322 = all_pats_ok pats  in
                       (qop, uu____3322, wopt, vars, body)  in
                     Quant uu____3303  in
                   mk uu____3302 r)
  
let (mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term)
  =
  fun uu____3349  ->
    fun r  ->
      match uu____3349 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____3389 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____3389 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____3412 = FStar_ST.op_Bang t1.freevars  in
        match uu____3412 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3466 ->
            (match t1.tm with
             | Integer uu____3475 -> t1
             | BoundV uu____3476 -> t1
             | FreeV x ->
                 let uu____3482 = index_of x  in
                 (match uu____3482 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____3492 =
                   let uu____3499 = FStar_List.map (aux ix) tms  in
                   (op, uu____3499)  in
                 mkApp' uu____3492 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____3507 =
                   let uu____3508 =
                     let uu____3515 = aux ix t2  in (uu____3515, r1, r2)  in
                   Labeled uu____3508  in
                 mk uu____3507 t2.rng
             | LblPos (t2,r) ->
                 let uu____3518 =
                   let uu____3519 =
                     let uu____3524 = aux ix t2  in (uu____3524, r)  in
                   LblPos uu____3519  in
                 mk uu____3518 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3547 =
                   let uu____3566 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3587 = aux (ix + n1) body  in
                   (qop, uu____3566, wopt, vars, uu____3587)  in
                 mkQuant t1.rng false uu____3547
             | Let (es,body) ->
                 let uu____3606 =
                   FStar_List.fold_left
                     (fun uu____3624  ->
                        fun e  ->
                          match uu____3624 with
                          | (ix1,l) ->
                              let uu____3644 =
                                let uu____3647 = aux ix1 e  in uu____3647 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3644))
                     (ix, []) es
                    in
                 (match uu____3606 with
                  | (ix1,es_rev) ->
                      let uu____3658 =
                        let uu____3665 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3665)  in
                      mkLet uu____3658 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3697 -> t1
        | FreeV uu____3698 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3715 =
              let uu____3722 = FStar_List.map (aux shift) tms2  in
              (op, uu____3722)  in
            mkApp' uu____3715 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3730 =
              let uu____3731 =
                let uu____3738 = aux shift t2  in (uu____3738, r1, r2)  in
              Labeled uu____3731  in
            mk uu____3730 t2.rng
        | LblPos (t2,r) ->
            let uu____3741 =
              let uu____3742 =
                let uu____3747 = aux shift t2  in (uu____3747, r)  in
              LblPos uu____3742  in
            mk uu____3741 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3775 =
              let uu____3794 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3811 = aux shift1 body  in
              (qop, uu____3794, wopt, vars, uu____3811)  in
            mkQuant t1.rng false uu____3775
        | Let (es,body) ->
            let uu____3826 =
              FStar_List.fold_left
                (fun uu____3844  ->
                   fun e  ->
                     match uu____3844 with
                     | (ix,es1) ->
                         let uu____3864 =
                           let uu____3867 = aux shift e  in uu____3867 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3864))
                (shift, []) es
               in
            (match uu____3826 with
             | (shift1,es_rev) ->
                 let uu____3878 =
                   let uu____3885 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3885)  in
                 mkLet uu____3878 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3903 = abstr [fv] t  in inst [s] uu____3903
  
let (mkQuant' :
  FStar_Range.range ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      fv Prims.list,term) FStar_Pervasives_Native.tuple5 -> term)
  =
  fun r  ->
    fun uu____3931  ->
      match uu____3931 with
      | (qop,pats,wopt,vars,body) ->
          let uu____3971 =
            let uu____3990 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____4007 = FStar_List.map fv_sort vars  in
            let uu____4010 = abstr vars body  in
            (qop, uu____3990, wopt, uu____4007, uu____4010)  in
          mkQuant r true uu____3971
  
let (mkForall :
  FStar_Range.range ->
    (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
      term)
  =
  fun r  ->
    fun uu____4038  ->
      match uu____4038 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple4 -> term)
  =
  fun r  ->
    fun uu____4093  ->
      match uu____4093 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      fvs,term) FStar_Pervasives_Native.tuple4 -> term)
  =
  fun r  ->
    fun uu____4161  ->
      match uu____4161 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range ->
    (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
      term)
  =
  fun r  ->
    fun uu____4219  ->
      match uu____4219 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term)
  =
  fun uu____4267  ->
    fun r  ->
      match uu____4267 with
      | (bindings,body) ->
          let uu____4293 = FStar_List.split bindings  in
          (match uu____4293 with
           | (vars,es) ->
               let uu____4312 =
                 let uu____4319 = abstr vars body  in (es, uu____4319)  in
               mkLet uu____4312 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string,fv Prims.list,sort,term,caption)
    FStar_Pervasives_Native.tuple5 -> decl)
  =
  fun uu____4338  ->
    match uu____4338 with
    | (nm,vars,s,tm,c) ->
        let uu____4360 =
          let uu____4373 = FStar_List.map fv_sort vars  in
          let uu____4376 = abstr vars tm  in
          (nm, uu____4373, s, uu____4376, c)  in
        DefineFun uu____4360
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____4384 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____4384
  
let (fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl) =
  fun uu____4397  ->
    fun id1  ->
      match uu____4397 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____4407 =
              let uu____4408 =
                let uu____4413 = mkInteger' id1 norng  in
                let uu____4414 =
                  let uu____4415 =
                    let uu____4422 = constr_id_of_sort sort  in
                    let uu____4423 =
                      let uu____4426 = mkApp (tok_name, []) norng  in
                      [uu____4426]  in
                    (uu____4422, uu____4423)  in
                  mkApp uu____4415 norng  in
                (uu____4413, uu____4414)  in
              mkEq uu____4408 norng  in
            let uu____4431 = escape a_name  in
            {
              assumption_term = uu____4407;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____4431;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string,sort Prims.list,sort,Prims.int)
      FStar_Pervasives_Native.tuple4 -> decl)
  =
  fun rng  ->
    fun uu____4451  ->
      match uu____4451 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____4483 =
                        let uu____4488 =
                          let uu____4489 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____4489  in
                        (uu____4488, s)  in
                      mkFreeV uu____4483 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____4505 =
              let uu____4512 = constr_id_of_sort sort  in
              (uu____4512, [capp])  in
            mkApp uu____4505 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____4517 =
              let uu____4518 =
                let uu____4529 =
                  let uu____4530 =
                    let uu____4535 = mkInteger id2 norng  in
                    (uu____4535, cid_app)  in
                  mkEq uu____4530 norng  in
                ([[capp]], bvar_names, uu____4529)  in
              mkForall rng uu____4518  in
            let uu____4544 = escape a_name  in
            {
              assumption_term = uu____4517;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Consrtructor distinct");
              assumption_name = uu____4544;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string,constructor_field Prims.list,sort)
      FStar_Pervasives_Native.tuple3 -> decls_t)
  =
  fun rng  ->
    fun uu____4562  ->
      match uu____4562 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____4585 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____4585  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____4612 = let uu____4617 = bvar_name i  in (uu____4617, s)
               in
            mkFreeV uu____4612  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____4644  ->
                      match uu____4644 with
                      | (uu____4651,s,uu____4653) ->
                          let uu____4654 = bvar i s  in uu____4654 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____4673 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____4707  ->
                      match uu____4707 with
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
                              let uu____4728 =
                                let uu____4729 =
                                  let uu____4740 =
                                    let uu____4741 =
                                      let uu____4746 =
                                        let uu____4747 = bvar i s  in
                                        uu____4747 norng  in
                                      (cproj_app, uu____4746)  in
                                    mkEq uu____4741 norng  in
                                  ([[capp]], bvar_names, uu____4740)  in
                                mkForall rng uu____4729  in
                              let uu____4760 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____4728;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____4760;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____4673 FStar_List.flatten
  
let (constructor_to_decl : FStar_Range.range -> constructor_t -> decls_t) =
  fun rng  ->
    fun uu____4775  ->
      match uu____4775 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____4809  ->
                    match uu____4809 with
                    | (uu____4816,sort1,uu____4818) -> sort1))
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
              let uu____4834 =
                let uu____4839 =
                  let uu____4840 =
                    let uu____4847 = constr_id_of_sort sort  in
                    (uu____4847, [xx])  in
                  mkApp uu____4840 norng  in
                let uu____4850 =
                  let uu____4851 = FStar_Util.string_of_int id1  in
                  mkInteger uu____4851 norng  in
                (uu____4839, uu____4850)  in
              mkEq uu____4834 norng  in
            let uu____4852 =
              let uu____4867 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____4923  ->
                          match uu____4923 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____4953 = mkApp (proj, [xx]) norng  in
                                (uu____4953, [])
                              else
                                (let fi =
                                   let uu____4972 =
                                     let uu____4973 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____4973  in
                                   (uu____4972, s)  in
                                 let uu____4974 = mkFreeV fi norng  in
                                 (uu____4974, [fi]))))
                 in
              FStar_All.pipe_right uu____4867 FStar_List.split  in
            match uu____4852 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____5055 =
                    let uu____5060 = mkApp (name, proj_terms) norng  in
                    (xx, uu____5060)  in
                  mkEq uu____5055 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____5068 ->
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
          let uu____5093 =
            let uu____5096 =
              let uu____5097 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____5097  in
            uu____5096 :: cdecl :: cid :: projs  in
          let uu____5098 =
            let uu____5101 =
              let uu____5104 =
                let uu____5105 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____5105  in
              [uu____5104]  in
            FStar_List.append [disc] uu____5101  in
          FStar_List.append uu____5093 uu____5098
  
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
          let uu____5160 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____5215  ->
                    fun s  ->
                      match uu____5215 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____5265 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____5269 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____5269  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____5282 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____5282  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____5160 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun sorts  ->
    let uu____5361 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____5361 with
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
              (let uu____5524 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5524)
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
                               "Prims.guard_free",{ tm = BoundV uu____5568;
                                                    freevars = uu____5569;
                                                    rng = uu____5570;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____5584 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____5646 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____5646 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____5669 = op_to_string op  in
              let uu____5670 =
                let uu____5671 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____5671 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____5669 uu____5670
          | Labeled (t2,uu____5677,uu____5678) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____5681 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5681 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____5704 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____5704 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5753 ->
                         let uu____5758 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____5774 =
                                     let uu____5775 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____5781 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____5781) pats2
                                        in
                                     FStar_String.concat " " uu____5775  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____5774))
                            in
                         FStar_All.pipe_right uu____5758
                           (FStar_String.concat "\n")
                      in
                   let uu____5784 =
                     let uu____5787 =
                       let uu____5790 =
                         let uu____5793 = aux1 n2 names2 body  in
                         let uu____5794 =
                           let uu____5797 = weightToSmt wopt  in
                           [uu____5797; pats_str; qid]  in
                         uu____5793 :: uu____5794  in
                       binders1 :: uu____5790  in
                     (qop_to_string qop) :: uu____5787  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____5784)
          | Let (es,body) ->
              let uu____5804 =
                FStar_List.fold_left
                  (fun uu____5841  ->
                     fun e  ->
                       match uu____5841 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____5891 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____5891  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____5904 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____5904  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____5804 with
               | (names2,binders,n2) ->
                   let uu____5940 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____5940)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____5948 = FStar_Range.string_of_range t1.rng  in
            let uu____5949 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5948
              uu____5949 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___119_5957  ->
    match uu___119_5957 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c "\n")
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_ranges  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Caption c ->
            let uu____5997 = FStar_Options.log_queries ()  in
            if uu____5997
            then
              let uu____5998 =
                FStar_All.pipe_right (FStar_Util.splitlines c)
                  (fun uu___120_6002  ->
                     match uu___120_6002 with | [] -> "" | h::t -> h)
                 in
              FStar_Util.format1 "\n; %s" uu____5998
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____6021 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)"
              (caption_to_string c) f (FStar_String.concat " " l) uu____6021
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____6031 = name_macro_binders arg_sorts  in
            (match uu____6031 with
             | (names1,binders) ->
                 let body1 =
                   let uu____6063 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____6063 body  in
                 let uu____6076 = strSort retsort  in
                 let uu____6077 =
                   let uu____6078 = escape f  in
                   termToSmt print_ranges uu____6078 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   (caption_to_string c) f (FStar_String.concat " " binders)
                   uu____6076 uu____6077)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___121_6099  ->
                      match uu___121_6099 with
                      | Name n1 ->
                          let uu____6101 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____6101
                      | Namespace ns ->
                          let uu____6103 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____6103
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              let uu____6106 = FStar_Options.log_queries ()  in
              if uu____6106
              then
                let uu____6107 =
                  let uu____6108 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____6108  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____6107
              else ""  in
            let n1 = a.assumption_name  in
            let uu____6113 = termToSmt print_ranges n1 a.assumption_term  in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))"
              (caption_to_string a.assumption_caption) fids uu____6113 n1
        | Eval t ->
            let uu____6115 = termToSmt print_ranges "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____6115
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____6117 -> ""
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
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
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
        [("LexCons_0", Term_sort, true);
        ("LexCons_1", Term_sort, true);
        ("LexCons_2", Term_sort, true)], Term_sort, (Prims.parse_int "11"),
        true)]
       in
    let bcons =
      let uu____6146 =
        let uu____6149 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____6149
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____6146 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____6168 =
      let uu____6169 =
        let uu____6170 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6170  in
      let uu____6175 =
        let uu____6178 =
          let uu____6179 =
            let uu____6180 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____6180  in
          (uu____6179, (BitVec_sort sz), true)  in
        [uu____6178]  in
      (uu____6169, uu____6175, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____6168 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____6204  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____6226 =
       let uu____6227 = FStar_ST.op_Bang __range_c  in
       uu____6227 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____6226);
    (let uu____6266 =
       let uu____6273 = let uu____6276 = mkInteger' i norng  in [uu____6276]
          in
       ("Range_const", uu____6273)  in
     mkApp uu____6266 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6308 =
        let uu____6315 = let uu____6318 = mkInteger' i norng  in [uu____6318]
           in
        ("Tm_uvar", uu____6315)  in
      mkApp uu____6308 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____6347 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____6365 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____6365 u v1 t
  
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
      let uu____6406 =
        let uu____6407 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6407  in
      let uu____6412 =
        let uu____6413 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6413  in
      elim_box true uu____6406 uu____6412 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____6428 =
        let uu____6429 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6429  in
      let uu____6434 =
        let uu____6435 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6435  in
      elim_box true uu____6428 uu____6434 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6451 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6463 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6480 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6480
         | uu____6481 -> FStar_Pervasives_Native.None)
    | uu____6482 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6495::t1::t2::[]);
                       freevars = uu____6498; rng = uu____6499;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6512::t1::t2::[]);
                       freevars = uu____6515; rng = uu____6516;_}::[])
        -> let uu____6529 = mkEq (t1, t2) norng  in mkNot uu____6529 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6532; rng = uu____6533;_}::[])
        ->
        let uu____6546 =
          let uu____6551 = unboxInt t1  in
          let uu____6552 = unboxInt t2  in (uu____6551, uu____6552)  in
        mkLTE uu____6546 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6555; rng = uu____6556;_}::[])
        ->
        let uu____6569 =
          let uu____6574 = unboxInt t1  in
          let uu____6575 = unboxInt t2  in (uu____6574, uu____6575)  in
        mkLT uu____6569 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6578; rng = uu____6579;_}::[])
        ->
        let uu____6592 =
          let uu____6597 = unboxInt t1  in
          let uu____6598 = unboxInt t2  in (uu____6597, uu____6598)  in
        mkGTE uu____6592 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6601; rng = uu____6602;_}::[])
        ->
        let uu____6615 =
          let uu____6620 = unboxInt t1  in
          let uu____6621 = unboxInt t2  in (uu____6620, uu____6621)  in
        mkGT uu____6615 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6624; rng = uu____6625;_}::[])
        ->
        let uu____6638 =
          let uu____6643 = unboxBool t1  in
          let uu____6644 = unboxBool t2  in (uu____6643, uu____6644)  in
        mkAnd uu____6638 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6647; rng = uu____6648;_}::[])
        ->
        let uu____6661 =
          let uu____6666 = unboxBool t1  in
          let uu____6667 = unboxBool t2  in (uu____6666, uu____6667)  in
        mkOr uu____6661 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6669; rng = uu____6670;_}::[])
        -> let uu____6683 = unboxBool t1  in mkNot uu____6683 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6687; rng = uu____6688;_}::[])
        when
        let uu____6701 = getBoxedInteger t0  in FStar_Util.is_some uu____6701
        ->
        let sz =
          let uu____6705 = getBoxedInteger t0  in
          match uu____6705 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6709 -> failwith "impossible"  in
        let uu____6712 =
          let uu____6717 = unboxBitVec sz t1  in
          let uu____6718 = unboxBitVec sz t2  in (uu____6717, uu____6718)  in
        mkBvUlt uu____6712 t.rng
    | App
        (Var
         "Prims.equals",uu____6719::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6723;
                                      rng = uu____6724;_}::uu____6725::[])
        when
        let uu____6738 = getBoxedInteger t0  in FStar_Util.is_some uu____6738
        ->
        let sz =
          let uu____6742 = getBoxedInteger t0  in
          match uu____6742 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6746 -> failwith "impossible"  in
        let uu____6749 =
          let uu____6754 = unboxBitVec sz t1  in
          let uu____6755 = unboxBitVec sz t2  in (uu____6754, uu____6755)  in
        mkBvUlt uu____6749 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___122_6759 = unboxBool t1  in
        {
          tm = (uu___122_6759.tm);
          freevars = (uu___122_6759.freevars);
          rng = (t.rng)
        }
    | uu____6760 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6809 = FStar_Options.unthrottle_inductives ()  in
        if uu____6809
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
    let uu____6915 =
      let uu____6916 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____6916 t t.rng  in
    FStar_All.pipe_right uu____6915 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____6929 =
        let uu____6936 = let uu____6939 = mkInteger' i norng  in [uu____6939]
           in
        ("FString_const", uu____6936)  in
      mkApp uu____6929 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____6967 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____6967 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____7000 =
         let uu____7007 =
           let uu____7010 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____7010]  in
         ("SFuel", uu____7007)  in
       mkApp uu____7000 norng)
  
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
            let uu____7050 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____7050
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
      let uu____7111 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____7111
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____7130 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____7130
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____7140 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____7140
  