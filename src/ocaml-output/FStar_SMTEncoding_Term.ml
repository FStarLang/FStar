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
  
let uu___is_Term_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____44 -> false
  
let uu___is_Fuel_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____49 -> false
  
let uu___is_BitVec_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____55 -> false
  
let __proj__BitVec_sort__item___0 : sort -> Prims.int =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let uu___is_Array : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____73 -> false
  
let __proj__Array__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0 
let uu___is_Arrow : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____103 -> false
  
let __proj__Arrow__item___0 :
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let uu___is_Sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____129 -> false
  
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
        let uu____143 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____143
    | Array (s1,s2) ->
        let uu____146 = strSort s1  in
        let uu____147 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____146 uu____147
    | Arrow (s1,s2) ->
        let uu____150 = strSort s1  in
        let uu____151 = strSort s2  in
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
  | Var of Prims.string 
let uu___is_TrueOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____169 -> false
  
let uu___is_FalseOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____174 -> false
  
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____179 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____184 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____189 -> false 
let uu___is_Imp : op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____194 -> false 
let uu___is_Iff : op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____199 -> false 
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____204 -> false 
let uu___is_LT : op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____209 -> false 
let uu___is_LTE : op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____214 -> false 
let uu___is_GT : op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____219 -> false 
let uu___is_GTE : op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____224 -> false 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____229 -> false 
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____234 -> false 
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____239 -> false 
let uu___is_Mul : op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____244 -> false 
let uu___is_Minus : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____249 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____254 -> false 
let uu___is_BvAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____259 -> false
  
let uu___is_BvXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____264 -> false
  
let uu___is_BvOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BvOr  -> true | uu____269 -> false 
let uu___is_BvAdd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____274 -> false
  
let uu___is_BvSub : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____279 -> false
  
let uu___is_BvShl : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____284 -> false
  
let uu___is_BvShr : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____289 -> false
  
let uu___is_BvUdiv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____294 -> false
  
let uu___is_BvMod : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____299 -> false
  
let uu___is_BvMul : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____304 -> false
  
let uu___is_BvUlt : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____309 -> false
  
let uu___is_BvUext : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____315 -> false
  
let __proj__BvUext__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let uu___is_NatToBv : op -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____329 -> false
  
let __proj__NatToBv__item___0 : op -> Prims.int =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let uu___is_BvToNat : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____342 -> false
  
let uu___is_ITE : op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____347 -> false 
let uu___is_Var : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____353 -> false
  
let __proj__Var__item___0 : op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let uu___is_Forall : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____366 -> false
  
let uu___is_Exists : qop -> Prims.bool =
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
    match projectee with | Integer _0 -> true | uu____486 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____500 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____518 -> false
  
let __proj__FreeV__item___0 :
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____550 -> false
  
let __proj__App__item___0 :
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____600 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____674 -> false
  
let __proj__Let__item___0 :
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____712 -> false
  
let __proj__Labeled__item___0 :
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____748 -> false
  
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
    match projectee with | Name _0 -> true | uu____906 -> false
  
let __proj__Name__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Namespace : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____920 -> false
  
let __proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let uu___is_Tag : fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____934 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1069 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1085 -> false
  
let __proj__DeclFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1141 -> false
  
let __proj__DefineFun__item___0 :
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1191 -> false
  
let __proj__Assume__item___0 : decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1205 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1219 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1233 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_RetainAssumptions : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1249 -> false
  
let __proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1268 -> false
  
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1273 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1278 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1283 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1293 -> false
  
let __proj__SetOption__item___0 :
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_GetStatistics : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1318 -> false
  
let uu___is_GetReasonUnknown : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1323 -> false
  
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq : fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____1348 'Auu____1349 .
    ('Auu____1349,'Auu____1348) FStar_Pervasives_Native.tuple2 ->
      'Auu____1348
  = fun x  -> FStar_Pervasives_Native.snd x 
let freevar_eq : term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____1380 -> false
  
let freevar_sort : term -> sort =
  fun uu___87_1388  ->
    match uu___87_1388 with
    | { tm = FreeV x; freevars = uu____1390; rng = uu____1391;_} -> fv_sort x
    | uu____1404 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___88_1408  ->
    match uu___88_1408 with
    | { tm = FreeV fv; freevars = uu____1410; rng = uu____1411;_} -> fv
    | uu____1424 -> failwith "impossible"
  
let rec freevars :
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
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____1514 = FStar_ST.op_Bang t.freevars  in
    match uu____1514 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1587 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____1587  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___89_1638  ->
    match uu___89_1638 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___90_1642  ->
    match uu___90_1642 with
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
        let uu____1644 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____1644
    | NatToBv n1 ->
        let uu____1646 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____1646
    | Var s -> s
  
let weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1653  ->
    match uu___91_1653 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1657 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____1657
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1665 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____1665
    | FreeV x ->
        let uu____1671 =
          let uu____1672 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____1672  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1671
    | App (op,tms) ->
        let uu____1679 =
          let uu____1680 = op_to_string op  in
          let uu____1681 =
            let uu____1682 =
              let uu____1683 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____1683 (FStar_String.concat " ")  in
            Prims.strcat uu____1682 ")"  in
          Prims.strcat uu____1680 uu____1681  in
        Prims.strcat "(" uu____1679
    | Labeled (t1,r1,r2) ->
        let uu____1691 = hash_of_term t1  in
        let uu____1692 =
          let uu____1693 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____1693  in
        Prims.strcat uu____1691 uu____1692
    | LblPos (t1,r) ->
        let uu____1696 =
          let uu____1697 = hash_of_term t1  in
          Prims.strcat uu____1697
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____1696
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1719 =
          let uu____1720 =
            let uu____1721 =
              let uu____1722 =
                let uu____1723 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____1723 (FStar_String.concat " ")  in
              let uu____1728 =
                let uu____1729 =
                  let uu____1730 = hash_of_term body  in
                  let uu____1731 =
                    let uu____1732 =
                      let uu____1733 = weightToSmt wopt  in
                      let uu____1734 =
                        let uu____1735 =
                          let uu____1736 =
                            let uu____1737 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1753 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____1753
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____1737
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____1736 "))"  in
                        Prims.strcat " " uu____1735  in
                      Prims.strcat uu____1733 uu____1734  in
                    Prims.strcat " " uu____1732  in
                  Prims.strcat uu____1730 uu____1731  in
                Prims.strcat ")(! " uu____1729  in
              Prims.strcat uu____1722 uu____1728  in
            Prims.strcat " (" uu____1721  in
          Prims.strcat (qop_to_string qop) uu____1720  in
        Prims.strcat "(" uu____1719
    | Let (es,body) ->
        let uu____1766 =
          let uu____1767 =
            let uu____1768 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____1768 (FStar_String.concat " ")  in
          let uu____1773 =
            let uu____1774 =
              let uu____1775 = hash_of_term body  in
              Prims.strcat uu____1775 ")"  in
            Prims.strcat ") " uu____1774  in
          Prims.strcat uu____1767 uu____1773  in
        Prims.strcat "(let (" uu____1766

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
    let uu____1805 =
      let uu____1806 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____1806  in
    mkBoxFunctions uu____1805
  
let isInjective : Prims.string -> Prims.bool =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____1813 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____1813 = "Box") &&
        (let uu____1815 =
           let uu____1816 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = '.') uu____1816  in
         Prims.op_Negation uu____1815)
    else false
  
let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1830 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____1830; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1887 =
        let uu____1888 = FStar_Util.ensure_decimal i  in Integer uu____1888
         in
      mk uu____1887 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1897 = FStar_Util.string_of_int i  in mkInteger uu____1897 r
  
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
  fun uu____1954  ->
    fun r  -> match uu____1954 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1978) -> mkFalse r
      | App (FalseOp ,uu____1983) -> mkTrue r
      | uu____1988 -> mkApp' (Not, [t]) r
  
let mkAnd :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2001  ->
    fun r  ->
      match uu____2001 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2009),uu____2010) -> t2
           | (uu____2015,App (TrueOp ,uu____2016)) -> t1
           | (App (FalseOp ,uu____2021),uu____2022) -> mkFalse r
           | (uu____2027,App (FalseOp ,uu____2028)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2045,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____2054) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2061 -> mkApp' (And, [t1; t2]) r)
  
let mkOr :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2078  ->
    fun r  ->
      match uu____2078 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____2086),uu____2087) -> mkTrue r
           | (uu____2092,App (TrueOp ,uu____2093)) -> mkTrue r
           | (App (FalseOp ,uu____2098),uu____2099) -> t2
           | (uu____2104,App (FalseOp ,uu____2105)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2122,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____2131) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2138 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2155  ->
    fun r  ->
      match uu____2155 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2163,App (TrueOp ,uu____2164)) -> mkTrue r
           | (App (FalseOp ,uu____2169),uu____2170) -> mkTrue r
           | (App (TrueOp ,uu____2175),uu____2176) -> t2
           | (uu____2181,App (Imp ,t1'::t2'::[])) ->
               let uu____2186 =
                 let uu____2193 =
                   let uu____2196 = mkAnd (t1, t1') r  in [uu____2196; t2']
                    in
                 (Imp, uu____2193)  in
               mkApp' uu____2186 r
           | uu____2199 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op :
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____2220  ->
      fun r  -> match uu____2220 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____2342  ->
      fun r  ->
        match uu____2342 with
        | (t1,t2) ->
            let uu____2350 =
              let uu____2357 =
                let uu____2360 =
                  let uu____2363 = mkNatToBv sz t2 r  in [uu____2363]  in
                t1 :: uu____2360  in
              (BvShl, uu____2357)  in
            mkApp' uu____2350 r
  
let mkBvShr :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2380  ->
      fun r  ->
        match uu____2380 with
        | (t1,t2) ->
            let uu____2388 =
              let uu____2395 =
                let uu____2398 =
                  let uu____2401 = mkNatToBv sz t2 r  in [uu____2401]  in
                t1 :: uu____2398  in
              (BvShr, uu____2395)  in
            mkApp' uu____2388 r
  
let mkBvUdiv :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2418  ->
      fun r  ->
        match uu____2418 with
        | (t1,t2) ->
            let uu____2426 =
              let uu____2433 =
                let uu____2436 =
                  let uu____2439 = mkNatToBv sz t2 r  in [uu____2439]  in
                t1 :: uu____2436  in
              (BvUdiv, uu____2433)  in
            mkApp' uu____2426 r
  
let mkBvMod :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2456  ->
      fun r  ->
        match uu____2456 with
        | (t1,t2) ->
            let uu____2464 =
              let uu____2471 =
                let uu____2474 =
                  let uu____2477 = mkNatToBv sz t2 r  in [uu____2477]  in
                t1 :: uu____2474  in
              (BvMod, uu____2471)  in
            mkApp' uu____2464 r
  
let mkBvMul :
  Prims.int ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun sz  ->
    fun uu____2494  ->
      fun r  ->
        match uu____2494 with
        | (t1,t2) ->
            let uu____2502 =
              let uu____2509 =
                let uu____2512 =
                  let uu____2515 = mkNatToBv sz t2 r  in [uu____2515]  in
                t1 :: uu____2512  in
              (BvMul, uu____2509)  in
            mkApp' uu____2502 r
  
let mkBvUlt :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op BvUlt 
let mkIff :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff 
let mkEq :
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____2548  ->
    fun r  ->
      match uu____2548 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____2564 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____2671  ->
    fun r  ->
      match uu____2671 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____2682) -> t2
           | App (FalseOp ,uu____2687) -> t3
           | uu____2692 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____2693),App (TrueOp ,uu____2694)) ->
                    mkTrue r
                | (App (TrueOp ,uu____2703),uu____2704) ->
                    let uu____2709 =
                      let uu____2714 = mkNot t1 t1.rng  in (uu____2714, t3)
                       in
                    mkImp uu____2709 r
                | (uu____2715,App (TrueOp ,uu____2716)) -> mkImp (t1, t2) r
                | (uu____2721,uu____2722) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
  fun uu____2769  ->
    fun r  ->
      match uu____2769 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2811) -> body
             | uu____2816 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let mkLet :
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2837  ->
    fun r  ->
      match uu____2837 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____2873 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____2873 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____2892 = FStar_ST.op_Bang t1.freevars  in
        match uu____2892 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2953 ->
            (match t1.tm with
             | Integer uu____2962 -> t1
             | BoundV uu____2963 -> t1
             | FreeV x ->
                 let uu____2969 = index_of x  in
                 (match uu____2969 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2979 =
                   let uu____2986 = FStar_List.map (aux ix) tms  in
                   (op, uu____2986)  in
                 mkApp' uu____2979 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2994 =
                   let uu____2995 =
                     let uu____3002 = aux ix t2  in (uu____3002, r1, r2)  in
                   Labeled uu____2995  in
                 mk uu____2994 t2.rng
             | LblPos (t2,r) ->
                 let uu____3005 =
                   let uu____3006 =
                     let uu____3011 = aux ix t2  in (uu____3011, r)  in
                   LblPos uu____3006  in
                 mk uu____3005 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____3034 =
                   let uu____3053 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____3074 = aux (ix + n1) body  in
                   (qop, uu____3053, wopt, vars, uu____3074)  in
                 mkQuant uu____3034 t1.rng
             | Let (es,body) ->
                 let uu____3093 =
                   FStar_List.fold_left
                     (fun uu____3111  ->
                        fun e  ->
                          match uu____3111 with
                          | (ix1,l) ->
                              let uu____3131 =
                                let uu____3134 = aux ix1 e  in uu____3134 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____3131))
                     (ix, []) es
                    in
                 (match uu____3093 with
                  | (ix1,es_rev) ->
                      let uu____3145 =
                        let uu____3152 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____3152)  in
                      mkLet uu____3145 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let inst : term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____3178 -> t1
        | FreeV uu____3179 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____3196 =
              let uu____3203 = FStar_List.map (aux shift) tms2  in
              (op, uu____3203)  in
            mkApp' uu____3196 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____3211 =
              let uu____3212 =
                let uu____3219 = aux shift t2  in (uu____3219, r1, r2)  in
              Labeled uu____3212  in
            mk uu____3211 t2.rng
        | LblPos (t2,r) ->
            let uu____3222 =
              let uu____3223 =
                let uu____3228 = aux shift t2  in (uu____3228, r)  in
              LblPos uu____3223  in
            mk uu____3222 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____3256 =
              let uu____3275 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____3292 = aux shift1 body  in
              (qop, uu____3275, wopt, vars, uu____3292)  in
            mkQuant uu____3256 t1.rng
        | Let (es,body) ->
            let uu____3307 =
              FStar_List.fold_left
                (fun uu____3325  ->
                   fun e  ->
                     match uu____3325 with
                     | (ix,es1) ->
                         let uu____3345 =
                           let uu____3348 = aux shift e  in uu____3348 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____3345))
                (shift, []) es
               in
            (match uu____3307 with
             | (shift1,es_rev) ->
                 let uu____3359 =
                   let uu____3366 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____3366)  in
                 mkLet uu____3359 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____3381 = abstr [fv] t  in inst [s] uu____3381
  
let mkQuant' :
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____3405  ->
    match uu____3405 with
    | (qop,pats,wopt,vars,body) ->
        let uu____3447 =
          let uu____3466 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____3483 = FStar_List.map fv_sort vars  in
          let uu____3490 = abstr vars body  in
          (qop, uu____3466, wopt, uu____3483, uu____3490)  in
        mkQuant uu____3447
  
let mkForall'' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____3521  ->
    fun r  ->
      match uu____3521 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____3587  ->
    fun r  ->
      match uu____3587 with
      | (pats,wopt,vars,body) ->
          let uu____3619 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____3619 r
  
let mkForall :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3644  ->
    fun r  ->
      match uu____3644 with
      | (pats,vars,body) ->
          let uu____3667 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3667 r
  
let mkExists :
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____3692  ->
    fun r  ->
      match uu____3692 with
      | (pats,vars,body) ->
          let uu____3715 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body)
             in
          uu____3715 r
  
let mkLet' :
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____3740  ->
    fun r  ->
      match uu____3740 with
      | (bindings,body) ->
          let uu____3766 = FStar_List.split bindings  in
          (match uu____3766 with
           | (vars,es) ->
               let uu____3785 =
                 let uu____3792 = abstr vars body  in (es, uu____3792)  in
               mkLet uu____3785 r)
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____3814  ->
    match uu____3814 with
    | (nm,vars,s,tm,c) ->
        let uu____3848 =
          let uu____3861 = FStar_List.map fv_sort vars  in
          let uu____3868 = abstr vars tm  in
          (nm, uu____3861, s, uu____3868, c)  in
        DefineFun uu____3848
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let uu____3875 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____3875
  
let fresh_token :
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3886  ->
    fun id  ->
      match uu____3886 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____3896 =
              let uu____3897 =
                let uu____3902 = mkInteger' id norng  in
                let uu____3903 =
                  let uu____3904 =
                    let uu____3911 = constr_id_of_sort sort  in
                    let uu____3912 =
                      let uu____3915 = mkApp (tok_name, []) norng  in
                      [uu____3915]  in
                    (uu____3911, uu____3912)  in
                  mkApp uu____3904 norng  in
                (uu____3902, uu____3903)  in
              mkEq uu____3897 norng  in
            {
              assumption_term = uu____3896;
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
  fun uu____3933  ->
    match uu____3933 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3965 =
                      let uu____3970 =
                        let uu____3971 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____3971  in
                      (uu____3970, s)  in
                    mkFreeV uu____3965 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____3979 =
            let uu____3986 = constr_id_of_sort sort  in (uu____3986, [capp])
             in
          mkApp uu____3979 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let a =
          let uu____3991 =
            let uu____3992 =
              let uu____4003 =
                let uu____4004 =
                  let uu____4009 = mkInteger id1 norng  in
                  (uu____4009, cid_app)  in
                mkEq uu____4004 norng  in
              ([[capp]], bvar_names, uu____4003)  in
            mkForall uu____3992 norng  in
          {
            assumption_term = uu____3991;
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
  fun uu____4031  ->
    match uu____4031 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____4052 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____4052  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____4072 = let uu____4077 = bvar_name i  in (uu____4077, s)
             in
          mkFreeV uu____4072  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4098  ->
                    match uu____4098 with
                    | (uu____4105,s,uu____4107) ->
                        let uu____4108 = bvar i s  in uu____4108 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____4117 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____4145  ->
                    match uu____4145 with
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
                            let uu____4168 =
                              let uu____4169 =
                                let uu____4180 =
                                  let uu____4181 =
                                    let uu____4186 =
                                      let uu____4187 = bvar i s  in
                                      uu____4187 norng  in
                                    (cproj_app, uu____4186)  in
                                  mkEq uu____4181 norng  in
                                ([[capp]], bvar_names, uu____4180)  in
                              mkForall uu____4169 norng  in
                            {
                              assumption_term = uu____4168;
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
        FStar_All.pipe_right uu____4117 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decls_t =
  fun uu____4210  ->
    match uu____4210 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____4238  ->
                  match uu____4238 with
                  | (uu____4245,sort1,uu____4247) -> sort1))
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
            let uu____4265 =
              let uu____4270 =
                let uu____4271 =
                  let uu____4278 = constr_id_of_sort sort  in
                  (uu____4278, [xx])  in
                mkApp uu____4271 norng  in
              let uu____4281 =
                let uu____4282 = FStar_Util.string_of_int id  in
                mkInteger uu____4282 norng  in
              (uu____4270, uu____4281)  in
            mkEq uu____4265 norng  in
          let uu____4283 =
            let uu____4298 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____4348  ->
                        match uu____4348 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____4378 = mkApp (proj, [xx]) norng  in
                              (uu____4378, [])
                            else
                              (let fi =
                                 let uu____4397 =
                                   let uu____4398 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____4398  in
                                 (uu____4397, s)  in
                               let uu____4399 = mkFreeV fi norng  in
                               (uu____4399, [fi]))))
               in
            FStar_All.pipe_right uu____4298 FStar_List.split  in
          match uu____4283 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____4480 =
                  let uu____4485 = mkApp (name, proj_terms) norng  in
                  (xx, uu____4485)  in
                mkEq uu____4480 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____4493 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____4534 =
          let uu____4537 =
            let uu____4538 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____4538  in
          uu____4537 :: cdecl :: cid :: projs  in
        let uu____4539 =
          let uu____4542 =
            let uu____4545 =
              let uu____4546 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____4546  in
            [uu____4545]  in
          FStar_List.append [disc] uu____4542  in
        FStar_List.append uu____4534 uu____4539
  
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
          let uu____4597 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____4652  ->
                    fun s  ->
                      match uu____4652 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____4702 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____4706 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____4706  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____4719 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____4719  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____4597 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____4797 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____4797 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let termToSmt : Prims.string -> term -> Prims.string =
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
            (let uu____4922 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "%s.%s" enclosing_name uu____4922)
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
                             "Prims.guard_free",{ tm = BoundV uu____4964;
                                                  freevars = uu____4965;
                                                  rng = uu____4966;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____4980 -> tm))))
         in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1"))  in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____5020 = FStar_List.nth names1 i  in
            FStar_All.pipe_right uu____5020 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____5035 = op_to_string op  in
            let uu____5036 =
              let uu____5037 = FStar_List.map (aux1 n1 names1) tms  in
              FStar_All.pipe_right uu____5037 (FStar_String.concat "\n")  in
            FStar_Util.format2 "(%s %s)" uu____5035 uu____5036
        | Labeled (t2,uu____5043,uu____5044) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____5047 = aux1 n1 names1 t2  in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____5047 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid ()  in
            let uu____5070 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts
               in
            (match uu____5070 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ")  in
                 let pats1 = remove_guard_free pats  in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____5119 ->
                       let uu____5124 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____5140 =
                                   let uu____5141 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____5147 = aux1 n2 names2 p
                                             in
                                          FStar_Util.format1 "%s" uu____5147)
                                       pats2
                                      in
                                   FStar_String.concat " " uu____5141  in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____5140))
                          in
                       FStar_All.pipe_right uu____5124
                         (FStar_String.concat "\n")
                    in
                 let uu____5150 =
                   let uu____5153 =
                     let uu____5156 =
                       let uu____5159 = aux1 n2 names2 body  in
                       let uu____5160 =
                         let uu____5163 = weightToSmt wopt  in
                         [uu____5163; pats_str; qid]  in
                       uu____5159 :: uu____5160  in
                     binders1 :: uu____5156  in
                   (qop_to_string qop) :: uu____5153  in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____5150)
        | Let (es,body) ->
            let uu____5170 =
              FStar_List.fold_left
                (fun uu____5207  ->
                   fun e  ->
                     match uu____5207 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____5257 = FStar_Util.string_of_int n0  in
                           Prims.strcat "@lb" uu____5257  in
                         let names01 = (nm, Term_sort) :: names0  in
                         let b =
                           let uu____5270 = aux1 n1 names1 e  in
                           FStar_Util.format2 "(%s %s)" nm uu____5270  in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es
               in
            (match uu____5170 with
             | (names2,binders,n2) ->
                 let uu____5302 = aux1 n2 names2 body  in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____5302)
      
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1  in
        if t1.rng <> norng
        then
          let uu____5310 = FStar_Range.string_of_range t1.rng  in
          let uu____5311 = FStar_Range.string_of_use_range t1.rng  in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____5310
            uu____5311 s
        else s
       in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let caption_to_string :
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_5318  ->
    match uu___92_5318 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____5322 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____5337 -> (hd1, "...")  in
        (match uu____5322 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
  
let rec declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_'  in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____5355 = FStar_Options.log_queries ()  in
          if uu____5355
          then
            let uu____5356 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_5360  ->
                   match uu___93_5360 with | [] -> "" | h::t -> h)
               in
            FStar_Util.format1 "\n; %s" uu____5356
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts  in
          let uu____5379 = caption_to_string c  in
          let uu____5380 = strSort retsort  in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____5379 f
            (FStar_String.concat " " l) uu____5380
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____5390 = name_macro_binders arg_sorts  in
          (match uu____5390 with
           | (names1,binders) ->
               let body1 =
                 let uu____5422 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                 inst uu____5422 body  in
               let uu____5435 = caption_to_string c  in
               let uu____5436 = strSort retsort  in
               let uu____5437 = termToSmt (escape f) body1  in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____5435
                 f (FStar_String.concat " " binders) uu____5436 uu____5437)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_5455  ->
                    match uu___94_5455 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t))
             in
          let fids =
            let uu____5460 = FStar_Options.log_queries ()  in
            if uu____5460
            then
              let uu____5461 =
                let uu____5462 = fact_ids_to_string a.assumption_fact_ids  in
                FStar_String.concat "; " uu____5462  in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____5461
            else ""  in
          let n1 = escape a.assumption_name  in
          let uu____5467 = caption_to_string a.assumption_caption  in
          let uu____5468 = termToSmt n1 a.assumption_term  in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____5467 fids
            uu____5468 n1
      | Eval t ->
          let uu____5470 = termToSmt "eval" t  in
          FStar_Util.format1 "(eval %s)" uu____5470
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____5472 -> ""
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
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
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
      let uu____5797 =
        let uu____5800 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____5800
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____5797 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let mkBvConstructor : Prims.int -> decls_t =
  fun sz  ->
    let uu____5816 =
      let uu____5835 =
        let uu____5836 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____5836  in
      let uu____5841 =
        let uu____5850 =
          let uu____5857 =
            let uu____5858 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____5858  in
          (uu____5857, (BitVec_sort sz), true)  in
        [uu____5850]  in
      (uu____5835, uu____5841, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____5816 constructor_to_decl
  
let mk_Range_const : term = mkApp ("Range_const", []) norng 
let mk_Term_type : term = mkApp ("Tm_type", []) norng 
let mk_Term_app : term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let mk_Term_uvar : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____5927 =
        let uu____5934 = let uu____5937 = mkInteger' i norng  in [uu____5937]
           in
        ("Tm_uvar", uu____5934)  in
      mkApp uu____5927 r
  
let mk_Term_unit : term = mkApp ("Tm_unit", []) norng 
let elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____5962 -> mkApp (u, [t]) t.rng
  
let maybe_elim_box : Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____5977 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____5977 u v1 t
  
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
      let uu____6010 =
        let uu____6011 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6011  in
      let uu____6016 =
        let uu____6017 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6017  in
      elim_box true uu____6010 uu____6016 t
  
let unboxBitVec : Prims.int -> term -> term =
  fun sz  ->
    fun t  ->
      let uu____6030 =
        let uu____6031 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____6031  in
      let uu____6036 =
        let uu____6037 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____6037  in
      elim_box true uu____6030 uu____6036 t
  
let boxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____6051 -> FStar_Exn.raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____6061 -> FStar_Exn.raise FStar_Util.Impos
  
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____6077 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____6077
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____6089 = op_to_string op  in
        let uu____6090 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____6089 uu____6090
    | Labeled (t1,r1,r2) ->
        let uu____6094 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____6094
    | LblPos (t1,s) ->
        let uu____6097 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____6097
    | Quant (qop,l,uu____6100,uu____6101,t1) ->
        let uu____6119 = print_smt_term_list_list l  in
        let uu____6120 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____6119
          uu____6120
    | Let (es,body) ->
        let uu____6127 = print_smt_term_list es  in
        let uu____6128 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____6127 uu____6128

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let uu____6132 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____6132 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____6151 =
             let uu____6152 =
               let uu____6153 = print_smt_term_list l1  in
               Prims.strcat uu____6153 " ] "  in
             Prims.strcat "; [ " uu____6152  in
           Prims.strcat s uu____6151) "" l

let getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____6169 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____6169
         | uu____6170 -> FStar_Pervasives_Native.None)
    | uu____6171 -> FStar_Pervasives_Native.None
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____6182::t1::t2::[]);
                       freevars = uu____6185; rng = uu____6186;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____6199::t1::t2::[]);
                       freevars = uu____6202; rng = uu____6203;_}::[])
        -> let uu____6216 = mkEq (t1, t2) norng  in mkNot uu____6216 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____6219; rng = uu____6220;_}::[])
        ->
        let uu____6233 =
          let uu____6238 = unboxInt t1  in
          let uu____6239 = unboxInt t2  in (uu____6238, uu____6239)  in
        mkLTE uu____6233 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____6242; rng = uu____6243;_}::[])
        ->
        let uu____6256 =
          let uu____6261 = unboxInt t1  in
          let uu____6262 = unboxInt t2  in (uu____6261, uu____6262)  in
        mkLT uu____6256 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____6265; rng = uu____6266;_}::[])
        ->
        let uu____6279 =
          let uu____6284 = unboxInt t1  in
          let uu____6285 = unboxInt t2  in (uu____6284, uu____6285)  in
        mkGTE uu____6279 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____6288; rng = uu____6289;_}::[])
        ->
        let uu____6302 =
          let uu____6307 = unboxInt t1  in
          let uu____6308 = unboxInt t2  in (uu____6307, uu____6308)  in
        mkGT uu____6302 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____6311; rng = uu____6312;_}::[])
        ->
        let uu____6325 =
          let uu____6330 = unboxBool t1  in
          let uu____6331 = unboxBool t2  in (uu____6330, uu____6331)  in
        mkAnd uu____6325 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____6334; rng = uu____6335;_}::[])
        ->
        let uu____6348 =
          let uu____6353 = unboxBool t1  in
          let uu____6354 = unboxBool t2  in (uu____6353, uu____6354)  in
        mkOr uu____6348 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____6356; rng = uu____6357;_}::[])
        -> let uu____6370 = unboxBool t1  in mkNot uu____6370 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____6374; rng = uu____6375;_}::[])
        when
        let uu____6388 = getBoxedInteger t0  in FStar_Util.is_some uu____6388
        ->
        let sz =
          let uu____6392 = getBoxedInteger t0  in
          match uu____6392 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6396 -> failwith "impossible"  in
        let uu____6399 =
          let uu____6404 = unboxBitVec sz t1  in
          let uu____6405 = unboxBitVec sz t2  in (uu____6404, uu____6405)  in
        mkBvUlt uu____6399 t.rng
    | App
        (Var
         "Prims.equals",uu____6406::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____6410;
                                      rng = uu____6411;_}::uu____6412::[])
        when
        let uu____6425 = getBoxedInteger t0  in FStar_Util.is_some uu____6425
        ->
        let sz =
          let uu____6429 = getBoxedInteger t0  in
          match uu____6429 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6433 -> failwith "impossible"  in
        let uu____6436 =
          let uu____6441 = unboxBitVec sz t1  in
          let uu____6442 = unboxBitVec sz t2  in (uu____6441, uu____6442)  in
        mkBvUlt uu____6436 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_6446 = unboxBool t1  in
        {
          tm = (uu___95_6446.tm);
          freevars = (uu___95_6446.freevars);
          rng = (t.rng)
        }
    | uu____6447 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let mk_IsTyped : term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____6488 = FStar_Options.unthrottle_inductives ()  in
        if uu____6488
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
      let uu____6579 =
        let uu____6586 = let uu____6589 = mkInteger' i norng  in [uu____6589]
           in
        ("FString_const", uu____6586)  in
      mkApp uu____6579 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____6604 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____6604 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____6628 =
         let uu____6635 =
           let uu____6638 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____6638]  in
         ("SFuel", uu____6635)  in
       mkApp uu____6628 norng)
  
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
            let uu____6675 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____6675
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
      let uu____6732 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____6732
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____6749 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____6749
  
let mk_haseq : term -> term =
  fun t  ->
    let uu____6758 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____6758
  