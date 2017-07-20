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
let uu___is_Bool_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____29 -> false
  
let uu___is_Int_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____34 -> false
  
let uu___is_String_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____39 -> false
  
let uu___is_Ref_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____44 -> false
  
let uu___is_Term_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____49 -> false
  
let uu___is_Fuel_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____54 -> false
  
let uu___is_BitVec_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____60 -> false
  
let __proj__BitVec_sort__item___0 : sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let uu___is_Array : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____78 -> false
  
let __proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0 
let uu___is_Arrow : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____108 -> false
  
let __proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let uu___is_Sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____134 -> false
  
let __proj__Sort__item___0 : sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0 
let rec strSort : sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | BitVec_sort n1 ->
        let uu____148 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____148
    | Array (s1,s2) ->
        let uu____151 = strSort s1  in
        let uu____152 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____151 uu____152
    | Arrow (s1,s2) ->
        let uu____155 = strSort s1  in
        let uu____156 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____155 uu____156
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
let uu___is_TrueOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____174 -> false
  
let uu___is_FalseOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____179 -> false
  
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____184 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____189 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____194 -> false 
let uu___is_Imp : op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____199 -> false 
let uu___is_Iff : op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____204 -> false 
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____209 -> false 
let uu___is_LT : op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____214 -> false 
let uu___is_LTE : op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____219 -> false 
let uu___is_GT : op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____224 -> false 
let uu___is_GTE : op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____229 -> false 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____234 -> false 
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____239 -> false 
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____244 -> false 
let uu___is_Mul : op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____249 -> false 
let uu___is_Minus : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____254 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____259 -> false 
let uu___is_BvAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____264 -> false
  
let uu___is_BvXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____269 -> false
  
let uu___is_BvOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____274 -> false 
let uu___is_BvShl : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____279 -> false
  
let uu___is_BvShr : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____284 -> false
  
let uu___is_BvUdiv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____289 -> false
  
let uu___is_BvMod : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____294 -> false
  
let uu___is_BvMul : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____299 -> false
  
let uu___is_BvUlt : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____304 -> false
  
let uu___is_BvUext : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____310 -> false
  
let __proj__BvUext__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let uu___is_NatToBv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____324 -> false
  
let __proj__NatToBv__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let uu___is_BvToNat : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____337 -> false
  
let uu___is_ITE : op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____342 -> false 
let uu___is_Var : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____348 -> false
  
let __proj__Var__item___0 : op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let uu___is_Forall : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____361 -> false
  
let uu___is_Exists : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____366 -> false
  
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
let uu___is_Integer : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____469 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____483 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____501 -> false
  
let __proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____533 -> false
  
let __proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____583 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____657 -> false
  
let __proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____695 -> false
  
let __proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____731 -> false
  
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
let uu___is_Name : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____871 -> false
  
let __proj__Name__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Namespace : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____885 -> false
  
let __proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let uu___is_Tag : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____899 -> false
  
let __proj__Tag__item___0 : fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0 
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list }
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
  | GetReasonUnknown 
let uu___is_DefPrelude : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1034 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1050 -> false
  
let __proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1106 -> false
  
let __proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1156 -> false
  
let __proj__Assume__item___0 : decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1170 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1184 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1198 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_RetainAssumptions : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1214 -> false
  
let __proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1233 -> false
  
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1238 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1243 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1248 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1258 -> false
  
let __proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_GetStatistics : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1283 -> false
  
let uu___is_GetReasonUnknown : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1288 -> false
  
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq : fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____1313 'Auu____1314 .
    ('Auu____1314,'Auu____1313) FStar_Pervasives_Native.tuple2 ->
      'Auu____1313
  = fun x  -> FStar_Pervasives_Native.snd x 
let freevar_eq : term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1345 -> false
  
let freevar_sort : term -> sort =
  fun uu___87_1353  ->
    match uu___87_1353 with
    | { tm = FreeV x; freevars = uu____1355; rng = uu____1356;_} -> fv_sort x
    | uu____1369 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___88_1373  ->
    match uu___88_1373 with
    | { tm = FreeV fv; freevars = uu____1375; rng = uu____1376;_} -> fv
    | uu____1389 -> failwith "impossible"
  
let rec freevars :
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1406 -> []
    | BoundV uu____1411 -> []
    | FreeV fv -> [fv]
    | App (uu____1429,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1439,uu____1440,uu____1441,uu____1442,t1) -> freevars t1
    | Labeled (t1,uu____1461,uu____1462) -> freevars t1
    | LblPos (t1,uu____1464) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____1479 = FStar_ST.read t.freevars  in
    match uu____1479 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1518 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1518  in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___89_1535  ->
    match uu___89_1535 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___90_1539  ->
    match uu___90_1539 with
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
        let uu____1541 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1541
    | NatToBv n1 ->
        let uu____1543 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1543
    | Var s -> s
  
let weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1550  ->
    match uu___91_1550 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1554 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1554
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1562 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1562
    | FreeV x ->
        let uu____1568 =
          let uu____1569 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1569  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1568
    | App (op,tms) ->
        let uu____1576 =
          let uu____1577 = op_to_string op  in
          let uu____1578 =
            let uu____1579 =
              let uu____1580 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1580 (FStar_String.concat " ")  in
            Prims.strcat uu____1579 ")"  in
          Prims.strcat uu____1577 uu____1578  in
        Prims.strcat "(" uu____1576
    | Labeled (t1,r1,r2) ->
        let uu____1588 = hash_of_term t1  in
        let uu____1589 =
          let uu____1590 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1590  in
        Prims.strcat uu____1588 uu____1589
    | LblPos (t1,r) ->
        let uu____1593 =
          let uu____1594 = hash_of_term t1  in
          Prims.strcat uu____1594
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1593
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1616 =
          let uu____1617 =
            let uu____1618 =
              let uu____1619 =
                let uu____1620 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1620 (FStar_String.concat " ")  in
              let uu____1625 =
                let uu____1626 =
                  let uu____1627 = hash_of_term body  in
                  let uu____1628 =
                    let uu____1629 =
                      let uu____1630 = weightToSmt wopt  in
                      let uu____1631 =
                        let uu____1632 =
                          let uu____1633 =
                            let uu____1634 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1650 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1650
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1634
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1633 "))"  in
                        Prims.strcat " " uu____1632  in
                      Prims.strcat uu____1630 uu____1631  in
                    Prims.strcat " " uu____1629  in
                  Prims.strcat uu____1627 uu____1628  in
                Prims.strcat ")(! " uu____1626  in
              Prims.strcat uu____1619 uu____1625  in
            Prims.strcat " (" uu____1618  in
          Prims.strcat (qop_to_string qop) uu____1617  in
        Prims.strcat "(" uu____1616
    | Let (es,body) ->
        let uu____1663 =
          let uu____1664 =
            let uu____1665 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1665 (FStar_String.concat " ")  in
          let uu____1670 =
            let uu____1671 =
              let uu____1672 = hash_of_term body  in
              Prims.strcat uu____1672 ")"  in
            Prims.strcat ") " uu____1671  in
          Prims.strcat uu____1664 uu____1670  in
        Prims.strcat "(let (" uu____1663

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
let boxRefFun : (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  mkBoxFunctions "BoxRef" 
let boxBitVecFun :
  Prims.int -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun sz  ->
    let uu____1706 =
      let uu____1707 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1707  in
    mkBoxFunctions uu____1706
  
let isInjective : Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1714 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1714 = "Box") &&
        (let uu____1716 =
           let uu____1717 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = '.') uu____1717  in
         Prims.op_Negation uu____1716)
    else false
  
let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1731 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1731; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1776 =
        let uu____1777 = FStar_Util.ensure_decimal i  in Integer uu____1777
         in
      mk uu____1776 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1786 = FStar_Util.string_of_int i  in mkInteger uu____1786 r
  
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
  fun uu____1843  ->
    fun r  -> match uu____1843 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1867) -> mkFalse r
      | App (FalseOp ,uu____1872) -> mkTrue r
      | uu____1877 -> mkApp' (Not, [t]) r
  
let mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1890  ->
    fun r  ->
      match uu____1890 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1898),uu____1899) -> t2
           | (uu____1904,App (TrueOp ,uu____1905)) -> t1
           | (App (FalseOp ,uu____1910),uu____1911) -> mkFalse r
           | (uu____1916,App (FalseOp ,uu____1917)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1934,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1943) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1950 -> mkApp' (And, [t1; t2]) r)
  
let mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1967  ->
    fun r  ->
      match uu____1967 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1975),uu____1976) -> mkTrue r
           | (uu____1981,App (TrueOp ,uu____1982)) -> mkTrue r
           | (App (FalseOp ,uu____1987),uu____1988) -> t2
           | (uu____1993,App (FalseOp ,uu____1994)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2011,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2020) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2027 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2044  ->
    fun r  ->
      match uu____2044 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2052,App (TrueOp ,uu____2053)) -> mkTrue r
           | (App (FalseOp ,uu____2058),uu____2059) -> mkTrue r
           | (App (TrueOp ,uu____2064),uu____2065) -> t2
           | (uu____2070,App (Imp ,t1'::t2'::[])) ->
               let uu____2075 =
                 let uu____2082 =
                   let uu____2085 = mkAnd (t1, t1') r  in [uu____2085; t2']
                    in
                 (Imp, uu____2082)  in
               mkApp' uu____2075 r
           | uu____2088 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2109  ->
      fun r  -> match uu____2109 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
let mkBvShl :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2211  ->
      fun r  ->
        match uu____2211 with
        | (t1,t2) ->
            let uu____2219 =
              let uu____2226 =
                let uu____2229 =
                  let uu____2232 = mkNatToBv sz t2 r  in [uu____2232]  in
                t1 :: uu____2229  in
              (BvShl, uu____2226)  in
            mkApp' uu____2219 r
  
let mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2249  ->
      fun r  ->
        match uu____2249 with
        | (t1,t2) ->
            let uu____2257 =
              let uu____2264 =
                let uu____2267 =
                  let uu____2270 = mkNatToBv sz t2 r  in [uu____2270]  in
                t1 :: uu____2267  in
              (BvShr, uu____2264)  in
            mkApp' uu____2257 r
  
let mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2287  ->
      fun r  ->
        match uu____2287 with
        | (t1,t2) ->
            let uu____2295 =
              let uu____2302 =
                let uu____2305 =
                  let uu____2308 = mkNatToBv sz t2 r  in [uu____2308]  in
                t1 :: uu____2305  in
              (BvUdiv, uu____2302)  in
            mkApp' uu____2295 r
  
let mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2325  ->
      fun r  ->
        match uu____2325 with
        | (t1,t2) ->
            let uu____2333 =
              let uu____2340 =
                let uu____2343 =
                  let uu____2346 = mkNatToBv sz t2 r  in [uu____2346]  in
                t1 :: uu____2343  in
              (BvMod, uu____2340)  in
            mkApp' uu____2333 r
  
let mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2363  ->
      fun r  ->
        match uu____2363 with
        | (t1,t2) ->
            let uu____2371 =
              let uu____2378 =
                let uu____2381 =
                  let uu____2384 = mkNatToBv sz t2 r  in [uu____2384]  in
                t1 :: uu____2381  in
              (BvMul, uu____2378)  in
            mkApp' uu____2371 r
  
let mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt 
let mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff 
let mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2417  ->
    fun r  ->
      match uu____2417 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2433 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2540  ->
    fun r  ->
      match uu____2540 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2551) -> t2
           | App (FalseOp ,uu____2556) -> t3
           | uu____2561 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2562),App (TrueOp ,uu____2563)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2572),uu____2573) ->
                    let uu____2578 =
                      let uu____2583 = mkNot t1 t1.rng  in (uu____2583, t3)
                       in
                    mkImp uu____2578 r
                | (uu____2584,App (TrueOp ,uu____2585)) -> mkImp (t1, t2) r
                | (uu____2590,uu____2591) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
  fun uu____2638  ->
    fun r  ->
      match uu____2638 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2680) -> body
             | uu____2685 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2706  ->
    fun r  ->
      match uu____2706 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____2742 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____2742 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____2761 = FStar_ST.read t1.freevars  in
        match uu____2761 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2788 ->
            (match t1.tm with
             | Integer uu____2797 -> t1
             | BoundV uu____2798 -> t1
             | FreeV x ->
                 let uu____2804 = index_of x  in
                 (match uu____2804 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2814 =
                   let uu____2821 = FStar_List.map (aux ix) tms  in
                   (op, uu____2821)  in
                 mkApp' uu____2814 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2829 =
                   let uu____2830 =
                     let uu____2837 = aux ix t2  in (uu____2837, r1, r2)  in
                   Labeled uu____2830  in
                 mk uu____2829 t2.rng
             | LblPos (t2,r) ->
                 let uu____2840 =
                   let uu____2841 =
                     let uu____2846 = aux ix t2  in (uu____2846, r)  in
                   LblPos uu____2841  in
                 mk uu____2840 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____2869 =
                   let uu____2888 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____2909 = aux (ix + n1) body  in
                   (qop, uu____2888, wopt, vars, uu____2909)  in
                 mkQuant uu____2869 t1.rng
             | Let (es,body) ->
                 let uu____2928 =
                   FStar_List.fold_left
                     (fun uu____2946  ->
                        fun e  ->
                          match uu____2946 with
                          | (ix1,l) ->
                              let uu____2966 =
                                let uu____2969 = aux ix1 e  in uu____2969 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____2966))
                     (ix, []) es
                    in
                 (match uu____2928 with
                  | (ix1,es_rev) ->
                      let uu____2980 =
                        let uu____2987 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____2987)  in
                      mkLet uu____2980 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let inst : term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3013 -> t1
        | FreeV uu____3014 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3031 =
              let uu____3038 = FStar_List.map (aux shift) tms2  in
              (op, uu____3038)  in
            mkApp' uu____3031 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3046 =
              let uu____3047 =
                let uu____3054 = aux shift t2  in (uu____3054, r1, r2)  in
              Labeled uu____3047  in
            mk uu____3046 t2.rng
        | LblPos (t2,r) ->
            let uu____3057 =
              let uu____3058 =
                let uu____3063 = aux shift t2  in (uu____3063, r)  in
              LblPos uu____3058  in
            mk uu____3057 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3091 =
              let uu____3110 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3127 = aux shift1 body  in
              (qop, uu____3110, wopt, vars, uu____3127)  in
            mkQuant uu____3091 t1.rng
        | Let (es,body) ->
            let uu____3142 =
              FStar_List.fold_left
                (fun uu____3160  ->
                   fun e  ->
                     match uu____3160 with
                     | (ix,es1) ->
                         let uu____3180 =
                           let uu____3183 = aux shift e  in uu____3183 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3180))
                (shift, []) es
               in
            (match uu____3142 with
             | (shift1,es_rev) ->
                 let uu____3194 =
                   let uu____3201 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3201)  in
                 mkLet uu____3194 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3216 = abstr [fv] t  in inst [s] uu____3216
  
let mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3240  ->
    match uu____3240 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3282 =
          let uu____3301 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3318 = FStar_List.map fv_sort vars  in
          let uu____3325 = abstr vars body  in
          (qop, uu____3301, wopt, uu____3318, uu____3325)  in
        mkQuant uu____3282
  
let mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3356  ->
    fun r  ->
      match uu____3356 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3422  ->
    fun r  ->
      match uu____3422 with
      | (pats,wopt,vars,body) ->
          let uu____3454 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3454 r
  
let mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3479  ->
    fun r  ->
      match uu____3479 with
      | (pats,vars,body) ->
          let uu____3502 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3502 r
  
let mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3527  ->
    fun r  ->
      match uu____3527 with
      | (pats,vars,body) ->
          let uu____3550 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3550 r
  
let mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3575  ->
    fun r  ->
      match uu____3575 with
      | (bindings,body) ->
          let uu____3601 = FStar_List.split bindings  in
          (match uu____3601 with
           | (vars,es) ->
               let uu____3620 =
                 let uu____3627 = abstr vars body  in (es, uu____3627)  in
               mkLet uu____3620 r)
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3649  ->
    match uu____3649 with
    | (nm,vars,s,tm,c) ->
        let uu____3683 =
          let uu____3696 = FStar_List.map fv_sort vars  in
          let uu____3703 = abstr vars tm  in
          (nm, uu____3696, s, uu____3703, c)  in
        DefineFun uu____3683
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let uu____3710 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____3710
  
let fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3721  ->
    fun id  ->
      match uu____3721 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____3731 =
              let uu____3732 =
                let uu____3737 = mkInteger' id norng  in
                let uu____3738 =
                  let uu____3739 =
                    let uu____3746 = constr_id_of_sort sort  in
                    let uu____3747 =
                      let uu____3750 = mkApp (tok_name, []) norng  in
                      [uu____3750]  in
                    (uu____3746, uu____3747)  in
                  mkApp uu____3739 norng  in
                (uu____3737, uu____3738)  in
              mkEq uu____3732 norng  in
            {
              assumption_term = uu____3731;
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
  fun uu____3768  ->
    match uu____3768 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3800 =
                      let uu____3805 =
                        let uu____3806 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____3806  in
                      (uu____3805, s)  in
                    mkFreeV uu____3800 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____3814 =
            let uu____3821 = constr_id_of_sort sort  in (uu____3821, [capp])
             in
          mkApp uu____3814 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____3826 =
            let uu____3827 =
              let uu____3838 =
                let uu____3839 =
                  let uu____3844 = mkInteger id1 norng  in
                  (uu____3844, cid_app)  in
                mkEq uu____3839 norng  in
              ([[capp]], bvar_names, uu____3838)  in
            mkForall uu____3827 norng  in
          {
            assumption_term = uu____3826;
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
  fun uu____3866  ->
    match uu____3866 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____3887 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____3887  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____3907 = let uu____3912 = bvar_name i  in (uu____3912, s)
             in
          mkFreeV uu____3907  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3933  ->
                    match uu____3933 with
                    | (uu____3940,s,uu____3942) ->
                        let uu____3943 = bvar i s  in uu____3943 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____3952 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3980  ->
                    match uu____3980 with
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
                            let uu____4003 =
                              let uu____4004 =
                                let uu____4015 =
                                  let uu____4016 =
                                    let uu____4021 =
                                      let uu____4022 = bvar i s  in
                                      uu____4022 norng  in
                                    (cproj_app, uu____4021)  in
                                  mkEq uu____4016 norng  in
                                ([[capp]], bvar_names, uu____4015)  in
                              mkForall uu____4004 norng  in
                            {
                              assumption_term = uu____4003;
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
        FStar_All.pipe_right uu____3952 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decls_t =
  fun uu____4045  ->
    match uu____4045 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4073  ->
                  match uu____4073 with
                  | (uu____4080,sort1,uu____4082) -> sort1))
           in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor"))
           in
        let cid = fresh_constructor (name, field_sorts, sort, id)  in
        let disc =
          let disc_name = Prims.strcat "is-" name  in
          let xfv = ("x", sort)  in
          let xx = mkFreeV xfv norng  in
          let disc_eq =
            let uu____4100 =
              let uu____4105 =
                let uu____4106 =
                  let uu____4113 = constr_id_of_sort sort  in
                  (uu____4113, [xx])  in
                mkApp uu____4106 norng  in
              let uu____4116 =
                let uu____4117 = FStar_Util.string_of_int id  in
                mkInteger uu____4117 norng  in
              (uu____4105, uu____4116)  in
            mkEq uu____4100 norng  in
          let uu____4118 =
            let uu____4133 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4183  ->
                        match uu____4183 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4213 = mkApp (proj, [xx]) norng  in
                              (uu____4213, [])
                            else
                              (let fi =
                                 let uu____4232 =
                                   let uu____4233 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4233  in
                                 (uu____4232, s)  in
                               let uu____4234 = mkFreeV fi norng  in
                               (uu____4234, [fi]))))
               in
            FStar_All.pipe_right uu____4133 FStar_List.split  in
          match uu____4118 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4315 =
                  let uu____4320 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4320)  in
                mkEq uu____4315 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4328 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____4369 =
          let uu____4372 =
            let uu____4373 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4373  in
          uu____4372 :: cdecl :: cid :: projs  in
        let uu____4374 =
          let uu____4377 =
            let uu____4380 =
              let uu____4381 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4381  in
            [uu____4380]  in
          FStar_List.append [disc] uu____4377  in
        FStar_List.append uu____4369 uu____4374
  
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
          let uu____4432 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4487  ->
                    fun s  ->
                      match uu____4487 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4537 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4541 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4541  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____4554 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____4554  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4432 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4632 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____4632 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let termToSmt : Prims.string -> term -> Prims.string =
  fun enclosing_name  ->
    fun t  ->
      let next_qid =
        let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
        fun depth  ->
          let n1 = FStar_ST.read ctr  in
          FStar_Util.incr ctr;
          if n1 = (Prims.parse_int "0")
          then enclosing_name
          else
            (let uu____4717 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "%s.%s" enclosing_name uu____4717)
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
                             "Prims.guard_free",{ tm = BoundV uu____4759;
                                                  freevars = uu____4760;
                                                  rng = uu____4761;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____4775 -> tm))))
         in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1"))  in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____4815 = FStar_List.nth names1 i  in
            FStar_All.pipe_right uu____4815 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____4830 = op_to_string op  in
            let uu____4831 =
              let uu____4832 = FStar_List.map (aux1 n1 names1) tms  in
              FStar_All.pipe_right uu____4832 (FStar_String.concat "\n")  in
            FStar_Util.format2 "(%s %s)" uu____4830 uu____4831
        | Labeled (t2,uu____4838,uu____4839) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____4842 = aux1 n1 names1 t2  in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____4842 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid ()  in
            let uu____4865 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts
               in
            (match uu____4865 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ")  in
                 let pats1 = remove_guard_free pats  in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____4914 ->
                       let uu____4919 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____4935 =
                                   let uu____4936 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____4942 = aux1 n2 names2 p
                                             in
                                          FStar_Util.format1 "%s" uu____4942)
                                       pats2
                                      in
                                   FStar_String.concat " " uu____4936  in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____4935))
                          in
                       FStar_All.pipe_right uu____4919
                         (FStar_String.concat "\n")
                    in
                 let uu____4945 =
                   let uu____4948 =
                     let uu____4951 =
                       let uu____4954 = aux1 n2 names2 body  in
                       let uu____4955 =
                         let uu____4958 = weightToSmt wopt  in
                         [uu____4958; pats_str; qid]  in
                       uu____4954 :: uu____4955  in
                     binders1 :: uu____4951  in
                   (qop_to_string qop) :: uu____4948  in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____4945)
        | Let (es,body) ->
            let uu____4965 =
              FStar_List.fold_left
                (fun uu____5002  ->
                   fun e  ->
                     match uu____5002 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____5052 = FStar_Util.string_of_int n0  in
                           Prims.strcat "@lb" uu____5052  in
                         let names01 = (nm, Term_sort) :: names0  in
                         let b =
                           let uu____5065 = aux1 n1 names1 e  in
                           FStar_Util.format2 "(%s %s)" nm uu____5065  in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es
               in
            (match uu____4965 with
             | (names2,binders,n2) ->
                 let uu____5097 = aux1 n2 names2 body  in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____5097)
      
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1  in
        if t1.rng <> norng
        then
          let uu____5105 = FStar_Range.string_of_range t1.rng  in
          let uu____5106 = FStar_Range.string_of_use_range t1.rng  in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5105
            uu____5106 s
        else s
       in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_5113  ->
    match uu___92_5113 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5117 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5132 -> (hd1, "...")  in
        (match uu____5117 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
  
let rec declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_'  in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____5150 = FStar_Options.log_queries ()  in
          if uu____5150
          then
            let uu____5151 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_5155  ->
                   match uu___93_5155 with | [] -> "" | h::t -> h)
               in
            FStar_Util.format1 "\n; %s" uu____5151
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts  in
          let uu____5174 = caption_to_string c  in
          let uu____5175 = strSort retsort  in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5174 f
            (FStar_String.concat " " l) uu____5175
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____5185 = name_macro_binders arg_sorts  in
          (match uu____5185 with
           | (names1,binders) ->
               let body1 =
                 let uu____5217 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                 inst uu____5217 body  in
               let uu____5230 = caption_to_string c  in
               let uu____5231 = strSort retsort  in
               let uu____5232 = termToSmt (escape f) body1  in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5230
                 f (FStar_String.concat " " binders) uu____5231 uu____5232)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_5250  ->
                    match uu___94_5250 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t))
             in
          let fids =
            let uu____5255 = FStar_Options.log_queries ()  in
            if uu____5255
            then
              let uu____5256 =
                let uu____5257 = fact_ids_to_string a.assumption_fact_ids  in
                FStar_String.concat "; " uu____5257  in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5256
            else ""  in
          let n1 = escape a.assumption_name  in
          let uu____5262 = caption_to_string a.assumption_caption  in
          let uu____5263 = termToSmt n1 a.assumption_term  in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5262 fids
            uu____5263 n1
      | Eval t ->
          let uu____5265 = termToSmt "eval" t  in
          FStar_Util.format1 "(eval %s)" uu____5265
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____5267 -> ""
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

and mkPrelude : Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
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
      ((FStar_Pervasives_Native.fst boxRefFun),
        [((FStar_Pervasives_Native.snd boxRefFun), Ref_sort, true)],
        Term_sort, (Prims.parse_int "10"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)]
       in
    let bcons =
      let uu____5630 =
        let uu____5633 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____5633
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____5630 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let mkBvConstructor : Prims.int -> decls_t =
  fun sz  ->
    let uu____5649 =
      let uu____5668 =
        let uu____5669 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5669  in
      let uu____5674 =
        let uu____5683 =
          let uu____5690 =
            let uu____5691 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____5691  in
          (uu____5690, (BitVec_sort sz), true)  in
        [uu____5683]  in
      (uu____5668, uu____5674, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____5649 constructor_to_decl
  
let mk_Range_const : term = mkApp ("Range_const", []) norng 
let mk_Term_type : term = mkApp ("Tm_type", []) norng 
let mk_Term_app : term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let mk_Term_uvar : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____5760 =
        let uu____5767 = let uu____5770 = mkInteger' i norng  in [uu____5770]
           in
        ("Tm_uvar", uu____5767)  in
      mkApp uu____5760 r
  
let mk_Term_unit : term = mkApp ("Tm_unit", []) norng 
let elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____5795 -> mkApp (u, [t]) t.rng
  
let maybe_elim_box : Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____5810 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____5810 u v1 t
  
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
  
let boxRef : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxRefFun)
      (FStar_Pervasives_Native.snd boxRefFun) t
  
let unboxRef : term -> term =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxRefFun)
      (FStar_Pervasives_Native.fst boxRefFun) t
  
let boxBitVec : Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____5851 =
        let uu____5852 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5852  in
      let uu____5857 =
        let uu____5858 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____5858  in
      elim_box true uu____5851 uu____5857 t
  
let unboxBitVec : Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____5871 =
        let uu____5872 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____5872  in
      let uu____5877 =
        let uu____5878 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5878  in
      elim_box true uu____5871 uu____5877 t
  
let boxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____5892 -> raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____5902 -> raise FStar_Util.Impos
  
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____5918 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____5918
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____5930 = op_to_string op  in
        let uu____5931 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____5930 uu____5931
    | Labeled (t1,r1,r2) ->
        let uu____5935 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____5935
    | LblPos (t1,s) ->
        let uu____5938 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____5938
    | Quant (qop,l,uu____5941,uu____5942,t1) ->
        let uu____5960 = print_smt_term_list_list l  in
        let uu____5961 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____5960
          uu____5961
    | Let (es,body) ->
        let uu____5968 = print_smt_term_list es  in
        let uu____5969 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____5968 uu____5969

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let uu____5973 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____5973 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____5992 =
             let uu____5993 =
               let uu____5994 = print_smt_term_list l1  in
               Prims.strcat uu____5994 " ] "  in
             Prims.strcat "; [ " uu____5993  in
           Prims.strcat s uu____5992) "" l

let getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6010 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6010
         | uu____6011 -> FStar_Pervasives_Native.None)
    | uu____6012 -> FStar_Pervasives_Native.None
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6023::t1::t2::[]);
                       freevars = uu____6026; rng = uu____6027;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6040::t1::t2::[]);
                       freevars = uu____6043; rng = uu____6044;_}::[])
        -> let uu____6057 = mkEq (t1, t2) norng  in mkNot uu____6057 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6060; rng = uu____6061;_}::[])
        ->
        let uu____6074 =
          let uu____6079 = unboxInt t1  in
          let uu____6080 = unboxInt t2  in (uu____6079, uu____6080)  in
        mkLTE uu____6074 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6083; rng = uu____6084;_}::[])
        ->
        let uu____6097 =
          let uu____6102 = unboxInt t1  in
          let uu____6103 = unboxInt t2  in (uu____6102, uu____6103)  in
        mkLT uu____6097 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6106; rng = uu____6107;_}::[])
        ->
        let uu____6120 =
          let uu____6125 = unboxInt t1  in
          let uu____6126 = unboxInt t2  in (uu____6125, uu____6126)  in
        mkGTE uu____6120 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6129; rng = uu____6130;_}::[])
        ->
        let uu____6143 =
          let uu____6148 = unboxInt t1  in
          let uu____6149 = unboxInt t2  in (uu____6148, uu____6149)  in
        mkGT uu____6143 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6152; rng = uu____6153;_}::[])
        ->
        let uu____6166 =
          let uu____6171 = unboxBool t1  in
          let uu____6172 = unboxBool t2  in (uu____6171, uu____6172)  in
        mkAnd uu____6166 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6175; rng = uu____6176;_}::[])
        ->
        let uu____6189 =
          let uu____6194 = unboxBool t1  in
          let uu____6195 = unboxBool t2  in (uu____6194, uu____6195)  in
        mkOr uu____6189 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6197; rng = uu____6198;_}::[])
        -> let uu____6211 = unboxBool t1  in mkNot uu____6211 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6215; rng = uu____6216;_}::[])
        when
        let uu____6229 = getBoxedInteger t0  in FStar_Util.is_some uu____6229
        ->
        let sz =
          let uu____6233 = getBoxedInteger t0  in
          match uu____6233 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6237 -> failwith "impossible"  in
        let uu____6240 =
          let uu____6245 = unboxBitVec sz t1  in
          let uu____6246 = unboxBitVec sz t2  in (uu____6245, uu____6246)  in
        mkBvUlt uu____6240 t.rng
    | App
        (Var
         "Prims.equals",uu____6247::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6251;
                                      rng = uu____6252;_}::uu____6253::[])
        when
        let uu____6266 = getBoxedInteger t0  in FStar_Util.is_some uu____6266
        ->
        let sz =
          let uu____6270 = getBoxedInteger t0  in
          match uu____6270 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6274 -> failwith "impossible"  in
        let uu____6277 =
          let uu____6282 = unboxBitVec sz t1  in
          let uu____6283 = unboxBitVec sz t2  in (uu____6282, uu____6283)  in
        mkBvUlt uu____6277 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_6287 = unboxBool t1  in
        {
          tm = (uu___95_6287.tm);
          freevars = (uu___95_6287.freevars);
          rng = (t.rng)
        }
    | uu____6288 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let mk_IsTyped : term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6329 = FStar_Options.unthrottle_inductives ()  in
        if uu____6329
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
let mk_String_const : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____6420 =
        let uu____6427 = let uu____6430 = mkInteger' i norng  in [uu____6430]
           in
        ("FString_const", uu____6427)  in
      mkApp uu____6420 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6445 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____6445 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6469 =
         let uu____6476 =
           let uu____6479 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____6479]  in
         ("SFuel", uu____6476)  in
       mkApp uu____6469 norng)
  
let fuel_2 : term = n_fuel (Prims.parse_int "2") 
let fuel_100 : term = n_fuel (Prims.parse_int "100") 
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
            let uu____6516 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____6516
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
      let uu____6573 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6573
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6590 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6590
  
let mk_haseq : term -> term =
  fun t  ->
    let uu____6599 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____6599
  