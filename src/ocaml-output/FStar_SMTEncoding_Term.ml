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
  | Array of (sort * sort) 
  | Arrow of (sort * sort) 
  | Sort of Prims.string 
let (uu___is_Bool_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____50 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____61 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____72 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____83 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____94 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____107 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____134 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____170 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____203 -> false
  
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
        let uu____231 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____231
    | Array (s1,s2) ->
        let uu____236 = strSort s1  in
        let uu____238 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____236 uu____238
    | Arrow (s1,s2) ->
        let uu____243 = strSort s1  in
        let uu____245 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____243 uu____245
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
  | RealDiv 
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
    match projectee with | TrueOp  -> true | uu____277 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____288 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____299 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____310 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____321 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____332 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____343 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____354 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____365 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____376 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____387 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____398 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____409 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____420 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____431 -> false 
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____442 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____453 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____464 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____475 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____486 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____497 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____508 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____519 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____530 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____541 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____552 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____563 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____574 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____585 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____596 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____609 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____633 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____655 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____666 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____679 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____701 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____712 -> false
  
type term' =
  | Integer of Prims.string 
  | Real of Prims.string 
  | BoundV of Prims.int 
  | FreeV of (Prims.string * sort * Prims.bool) 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int
  FStar_Pervasives_Native.option * sort Prims.list * term) 
  | Let of (term Prims.list * term) 
  | Labeled of (term * Prims.string * FStar_Range.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars:
    (Prims.string * sort * Prims.bool) Prims.list FStar_Syntax_Syntax.memo ;
  rng: FStar_Range.range }
let (uu___is_Integer : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____872 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____896 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____920 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____951 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1001 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____1058 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1141 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1186 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1232 -> false
  
let (__proj__LblPos__item___0 : term' -> (term * Prims.string)) =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> tm 
let (__proj__Mkterm__item__freevars :
  term ->
    (Prims.string * sort * Prims.bool) Prims.list FStar_Syntax_Syntax.memo)
  =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> freevars 
let (__proj__Mkterm__item__rng : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> rng 
type pat = term
type fv = (Prims.string * sort * Prims.bool)
type fvs = (Prims.string * sort * Prims.bool) Prims.list
type caption = Prims.string FStar_Pervasives_Native.option
type binders = (Prims.string * sort) Prims.list
type constructor_field = (Prims.string * sort * Prims.bool)
type constructor_t =
  (Prims.string * constructor_field Prims.list * sort * Prims.int *
    Prims.bool)
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid 
  | Namespace of FStar_Ident.lid 
  | Tag of Prims.string 
let (uu___is_Name : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1456 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1476 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1497 -> false
  
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
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_term
  
let (__proj__Mkassumption__item__assumption_caption : assumption -> caption)
  =
  fun projectee  ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_caption
  
let (__proj__Mkassumption__item__assumption_name :
  assumption -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_name
  
let (__proj__Mkassumption__item__assumption_fact_ids :
  assumption -> fact_db_id Prims.list) =
  fun projectee  ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_fact_ids
  
type decl =
  | DefPrelude 
  | DeclFun of (Prims.string * sort Prims.list * sort * caption) 
  | DefineFun of (Prims.string * sort Prims.list * sort * term * caption) 
  | Assume of assumption 
  | Caption of Prims.string 
  | Module of (Prims.string * decl Prims.list) 
  | Eval of term 
  | Echo of Prims.string 
  | RetainAssumptions of Prims.string Prims.list 
  | Push 
  | Pop 
  | CheckSat 
  | GetUnsatCore 
  | SetOption of (Prims.string * Prims.string) 
  | GetStatistics 
  | GetReasonUnknown 
let (uu___is_DefPrelude : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____1687 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1710 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1776 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1835 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1856 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1886 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1927 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1948 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1974 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____2002 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____2013 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____2024 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____2035 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____2053 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2090 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2101 -> false
  
type decls_t = decl Prims.list
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2124  -> match uu____2124 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____2144 = x  in
    match uu____2144 with | (nm,uu____2147,uu____2148) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____2159 = x  in
    match uu____2159 with | (uu____2160,sort,uu____2162) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____2174 = x  in
    match uu____2174 with | (uu____2176,uu____2177,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____2195 = fv_name x  in
      let uu____2197 = fv_name y  in uu____2195 = uu____2197
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2231 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___120_2242  ->
    match uu___120_2242 with
    | { tm = FreeV x; freevars = uu____2244; rng = uu____2245;_} -> fv_sort x
    | uu____2266 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___121_2273  ->
    match uu___121_2273 with
    | { tm = FreeV fv; freevars = uu____2275; rng = uu____2276;_} -> fv
    | uu____2297 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2325 -> []
    | Real uu____2335 -> []
    | BoundV uu____2345 -> []
    | FreeV fv -> [fv]
    | App (uu____2380,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2394,uu____2395,uu____2396,uu____2397,t1) -> freevars t1
    | Labeled (t1,uu____2418,uu____2419) -> freevars t1
    | LblPos (t1,uu____2423) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2446 = FStar_ST.op_Bang t.freevars  in
    match uu____2446 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2544 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2544  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___122_2623  ->
    match uu___122_2623 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___123_2633  ->
    match uu___123_2633 with
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
    | RealDiv  -> "/"
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
        let uu____2669 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2669
    | NatToBv n1 ->
        let uu____2674 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2674
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___124_2688  ->
    match uu___124_2688 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2698 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2698
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____2720 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2720
    | FreeV x ->
        let uu____2732 = fv_name x  in
        let uu____2734 =
          let uu____2736 = let uu____2738 = fv_sort x  in strSort uu____2738
             in
          Prims.strcat ":" uu____2736  in
        Prims.strcat uu____2732 uu____2734
    | App (op,tms) ->
        let uu____2746 =
          let uu____2748 = op_to_string op  in
          let uu____2750 =
            let uu____2752 =
              let uu____2754 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2754 (FStar_String.concat " ")  in
            Prims.strcat uu____2752 ")"  in
          Prims.strcat uu____2748 uu____2750  in
        Prims.strcat "(" uu____2746
    | Labeled (t1,r1,r2) ->
        let uu____2771 = hash_of_term t1  in
        let uu____2773 =
          let uu____2775 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2775  in
        Prims.strcat uu____2771 uu____2773
    | LblPos (t1,r) ->
        let uu____2781 =
          let uu____2783 = hash_of_term t1  in
          Prims.strcat uu____2783
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2781
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2811 =
          let uu____2813 =
            let uu____2815 =
              let uu____2817 =
                let uu____2819 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2819 (FStar_String.concat " ")  in
              let uu____2829 =
                let uu____2831 =
                  let uu____2833 = hash_of_term body  in
                  let uu____2835 =
                    let uu____2837 =
                      let uu____2839 = weightToSmt wopt  in
                      let uu____2841 =
                        let uu____2843 =
                          let uu____2845 =
                            let uu____2847 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2866 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2866
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2847
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2845 "))"  in
                        Prims.strcat " " uu____2843  in
                      Prims.strcat uu____2839 uu____2841  in
                    Prims.strcat " " uu____2837  in
                  Prims.strcat uu____2833 uu____2835  in
                Prims.strcat ")(! " uu____2831  in
              Prims.strcat uu____2817 uu____2829  in
            Prims.strcat " (" uu____2815  in
          Prims.strcat (qop_to_string qop) uu____2813  in
        Prims.strcat "(" uu____2811
    | Let (es,body) ->
        let uu____2893 =
          let uu____2895 =
            let uu____2897 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2897 (FStar_String.concat " ")  in
          let uu____2907 =
            let uu____2909 =
              let uu____2911 = hash_of_term body  in
              Prims.strcat uu____2911 ")"  in
            Prims.strcat ") " uu____2909  in
          Prims.strcat uu____2895 uu____2907  in
        Prims.strcat "(let (" uu____2893

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____2972 =
      let uu____2974 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____2974  in
    mkBoxFunctions uu____2972
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____2999 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____2999 = "Box") &&
        (let uu____3006 =
           let uu____3008 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3008  in
         Prims.op_Negation uu____3006)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3032 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3032; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3118 =
        let uu____3119 = FStar_Util.ensure_decimal i  in Integer uu____3119
         in
      mk uu____3118 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3134 = FStar_Util.string_of_int i  in mkInteger uu____3134 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3212  ->
    fun r  -> match uu____3212 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3242) -> mkFalse r
      | App (FalseOp ,uu____3247) -> mkTrue r
      | uu____3252 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3268  ->
    fun r  ->
      match uu____3268 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3276),uu____3277) -> t2
           | (uu____3282,App (TrueOp ,uu____3283)) -> t1
           | (App (FalseOp ,uu____3288),uu____3289) -> mkFalse r
           | (uu____3294,App (FalseOp ,uu____3295)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3312,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3321) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3328 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3348  ->
    fun r  ->
      match uu____3348 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3356),uu____3357) -> mkTrue r
           | (uu____3362,App (TrueOp ,uu____3363)) -> mkTrue r
           | (App (FalseOp ,uu____3368),uu____3369) -> t2
           | (uu____3374,App (FalseOp ,uu____3375)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3392,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3401) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3408 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3428  ->
    fun r  ->
      match uu____3428 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3436,App (TrueOp ,uu____3437)) -> mkTrue r
           | (App (FalseOp ,uu____3442),uu____3443) -> mkTrue r
           | (App (TrueOp ,uu____3448),uu____3449) -> t2
           | (uu____3454,App (Imp ,t1'::t2'::[])) ->
               let uu____3459 =
                 let uu____3466 =
                   let uu____3469 = mkAnd (t1, t1') r  in [uu____3469; t2']
                    in
                 (Imp, uu____3466)  in
               mkApp' uu____3459 r
           | uu____3472 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3497  ->
      fun r  -> match uu____3497 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
let (mkMinus : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r 
let (mkNatToBv : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz  -> fun t  -> fun r  -> mkApp' ((NatToBv sz), [t]) r 
let (mkBvUext : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz  -> fun t  -> fun r  -> mkApp' ((BvUext sz), [t]) r 
let (mkBvToNat : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp' (BvToNat, [t]) r 
let (mkBvAnd : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvAnd 
let (mkBvXor : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvXor 
let (mkBvOr : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvOr 
let (mkBvAdd : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvAdd 
let (mkBvSub : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvSub 
let (mkBvShl : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3657  ->
      fun r  ->
        match uu____3657 with
        | (t1,t2) ->
            let uu____3666 =
              let uu____3673 =
                let uu____3676 =
                  let uu____3679 = mkNatToBv sz t2 r  in [uu____3679]  in
                t1 :: uu____3676  in
              (BvShl, uu____3673)  in
            mkApp' uu____3666 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3701  ->
      fun r  ->
        match uu____3701 with
        | (t1,t2) ->
            let uu____3710 =
              let uu____3717 =
                let uu____3720 =
                  let uu____3723 = mkNatToBv sz t2 r  in [uu____3723]  in
                t1 :: uu____3720  in
              (BvShr, uu____3717)  in
            mkApp' uu____3710 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3745  ->
      fun r  ->
        match uu____3745 with
        | (t1,t2) ->
            let uu____3754 =
              let uu____3761 =
                let uu____3764 =
                  let uu____3767 = mkNatToBv sz t2 r  in [uu____3767]  in
                t1 :: uu____3764  in
              (BvUdiv, uu____3761)  in
            mkApp' uu____3754 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3789  ->
      fun r  ->
        match uu____3789 with
        | (t1,t2) ->
            let uu____3798 =
              let uu____3805 =
                let uu____3808 =
                  let uu____3811 = mkNatToBv sz t2 r  in [uu____3811]  in
                t1 :: uu____3808  in
              (BvMod, uu____3805)  in
            mkApp' uu____3798 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3833  ->
      fun r  ->
        match uu____3833 with
        | (t1,t2) ->
            let uu____3842 =
              let uu____3849 =
                let uu____3852 =
                  let uu____3855 = mkNatToBv sz t2 r  in [uu____3855]  in
                t1 :: uu____3852  in
              (BvMul, uu____3849)  in
            mkApp' uu____3842 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3897  ->
    fun r  ->
      match uu____3897 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3916 -> mk_bin_op Eq (t1, t2) r)
  
let (mkLT : (term * term) -> FStar_Range.range -> term) = mk_bin_op LT 
let (mkLTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op LTE 
let (mkGT : (term * term) -> FStar_Range.range -> term) = mk_bin_op GT 
let (mkGTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op GTE 
let (mkAdd : (term * term) -> FStar_Range.range -> term) = mk_bin_op Add 
let (mkSub : (term * term) -> FStar_Range.range -> term) = mk_bin_op Sub 
let (mkDiv : (term * term) -> FStar_Range.range -> term) = mk_bin_op Div 
let (mkRealDiv : (term * term) -> FStar_Range.range -> term) =
  mk_bin_op RealDiv 
let (mkMul : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mul 
let (mkMod : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mod 
let (mkRealOfInt : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp ("to_real", [t]) r 
let (mkITE : (term * term * term) -> FStar_Range.range -> term) =
  fun uu____4081  ->
    fun r  ->
      match uu____4081 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4092) -> t2
           | App (FalseOp ,uu____4097) -> t3
           | uu____4102 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4103),App (TrueOp ,uu____4104)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4113),uu____4114) ->
                    let uu____4119 =
                      let uu____4124 = mkNot t1 t1.rng  in (uu____4124, t3)
                       in
                    mkImp uu____4119 r
                | (uu____4125,App (TrueOp ,uu____4126)) -> mkImp (t1, t2) r
                | (uu____4131,uu____4132) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4188 -> FStar_Pervasives_Native.None
      | Real uu____4190 -> FStar_Pervasives_Native.None
      | BoundV uu____4192 -> FStar_Pervasives_Native.None
      | FreeV uu____4194 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4218 -> true
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
            | RealDiv  -> true
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
            | BvUext uu____4251 -> false
            | NatToBv uu____4254 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4265,uu____4266) -> aux t2
      | Quant uu____4269 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4289 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4304 = aux t1  in
          (match uu____4304 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | Real r -> FStar_Util.format1 "(Real %s)" r
    | BoundV n1 ->
        let uu____4342 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4342
    | FreeV fv ->
        let uu____4354 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4354
    | App (op,l) ->
        let uu____4363 = op_to_string op  in
        let uu____4365 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4363 uu____4365
    | Labeled (t1,r1,r2) ->
        let uu____4373 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4373
    | LblPos (t1,s) ->
        let uu____4380 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4380
    | Quant (qop,l,uu____4385,uu____4386,t1) ->
        let uu____4406 = print_smt_term_list_list l  in
        let uu____4408 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4406
          uu____4408
    | Let (es,body) ->
        let uu____4417 = print_smt_term_list es  in
        let uu____4419 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4417 uu____4419

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4426 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4426 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4453 =
             let uu____4455 =
               let uu____4457 = print_smt_term_list l1  in
               Prims.strcat uu____4457 " ] "  in
             Prims.strcat "; [ " uu____4455  in
           Prims.strcat s uu____4453) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4497  ->
        match uu____4497 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4566 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4566 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4581 =
                         let uu____4587 =
                           let uu____4589 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4589
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4587)
                          in
                       FStar_Errors.log_issue r uu____4581);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4600) -> body
               | uu____4605 ->
                   let uu____4606 =
                     let uu____4607 =
                       let uu____4627 = all_pats_ok pats  in
                       (qop, uu____4627, wopt, vars, body)  in
                     Quant uu____4607  in
                   mk uu____4606 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4656  ->
    fun r  ->
      match uu____4656 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4702 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4702 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4735 = FStar_ST.op_Bang t1.freevars  in
        match uu____4735 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4809 ->
            (match t1.tm with
             | Integer uu____4822 -> t1
             | Real uu____4824 -> t1
             | BoundV uu____4826 -> t1
             | FreeV x ->
                 let uu____4837 = index_of1 x  in
                 (match uu____4837 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4851 =
                   let uu____4858 = FStar_List.map (aux ix) tms  in
                   (op, uu____4858)  in
                 mkApp' uu____4851 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4868 =
                   let uu____4869 =
                     let uu____4877 = aux ix t2  in (uu____4877, r1, r2)  in
                   Labeled uu____4869  in
                 mk uu____4868 t2.rng
             | LblPos (t2,r) ->
                 let uu____4883 =
                   let uu____4884 =
                     let uu____4890 = aux ix t2  in (uu____4890, r)  in
                   LblPos uu____4884  in
                 mk uu____4883 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4916 =
                   let uu____4936 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4957 = aux (ix + n1) body  in
                   (qop, uu____4936, wopt, vars, uu____4957)  in
                 mkQuant t1.rng false uu____4916
             | Let (es,body) ->
                 let uu____4978 =
                   FStar_List.fold_left
                     (fun uu____4998  ->
                        fun e  ->
                          match uu____4998 with
                          | (ix1,l) ->
                              let uu____5022 =
                                let uu____5025 = aux ix1 e  in uu____5025 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5022))
                     (ix, []) es
                    in
                 (match uu____4978 with
                  | (ix1,es_rev) ->
                      let uu____5041 =
                        let uu____5048 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5048)  in
                      mkLet uu____5041 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5084 -> t1
        | Real uu____5086 -> t1
        | FreeV uu____5088 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5113 =
              let uu____5120 = FStar_List.map (aux shift) tms2  in
              (op, uu____5120)  in
            mkApp' uu____5113 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5130 =
              let uu____5131 =
                let uu____5139 = aux shift t2  in (uu____5139, r1, r2)  in
              Labeled uu____5131  in
            mk uu____5130 t2.rng
        | LblPos (t2,r) ->
            let uu____5145 =
              let uu____5146 =
                let uu____5152 = aux shift t2  in (uu____5152, r)  in
              LblPos uu____5146  in
            mk uu____5145 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5184 =
              let uu____5204 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5221 = aux shift1 body  in
              (qop, uu____5204, wopt, vars, uu____5221)  in
            mkQuant t1.rng false uu____5184
        | Let (es,body) ->
            let uu____5238 =
              FStar_List.fold_left
                (fun uu____5258  ->
                   fun e  ->
                     match uu____5258 with
                     | (ix,es1) ->
                         let uu____5282 =
                           let uu____5285 = aux shift e  in uu____5285 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5282))
                (shift, []) es
               in
            (match uu____5238 with
             | (shift1,es_rev) ->
                 let uu____5301 =
                   let uu____5308 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5308)  in
                 mkLet uu____5301 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5328 = abstr [fv] t  in inst [s] uu____5328
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5358  ->
      match uu____5358 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5401 =
            let uu____5421 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5438 = FStar_List.map fv_sort vars  in
            let uu____5441 = abstr vars body  in
            (qop, uu____5421, wopt, uu____5438, uu____5441)  in
          mkQuant r true uu____5401
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5472  ->
      match uu____5472 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5531  ->
      match uu____5531 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5606  ->
      match uu____5606 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5669  ->
      match uu____5669 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5720  ->
    fun r  ->
      match uu____5720 with
      | (bindings,body) ->
          let uu____5746 = FStar_List.split bindings  in
          (match uu____5746 with
           | (vars,es) ->
               let uu____5765 =
                 let uu____5772 = abstr vars body  in (es, uu____5772)  in
               mkLet uu____5765 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5794  ->
    match uu____5794 with
    | (nm,vars,s,tm,c) ->
        let uu____5819 =
          let uu____5833 = FStar_List.map fv_sort vars  in
          let uu____5836 = abstr vars tm  in
          (nm, uu____5833, s, uu____5836, c)  in
        DefineFun uu____5819
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5847 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5847
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5865  ->
    fun id1  ->
      match uu____5865 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5881 =
              let uu____5882 =
                let uu____5887 = mkInteger' id1 norng  in
                let uu____5888 =
                  let uu____5889 =
                    let uu____5897 = constr_id_of_sort sort  in
                    let uu____5899 =
                      let uu____5902 = mkApp (tok_name, []) norng  in
                      [uu____5902]  in
                    (uu____5897, uu____5899)  in
                  mkApp uu____5889 norng  in
                (uu____5887, uu____5888)  in
              mkEq uu____5882 norng  in
            let uu____5909 = escape a_name  in
            {
              assumption_term = uu____5881;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5909;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5935  ->
      match uu____5935 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5975 =
                        let uu____5976 =
                          let uu____5982 =
                            let uu____5984 = FStar_Util.string_of_int i  in
                            Prims.strcat "x_" uu____5984  in
                          (uu____5982, s)  in
                        mk_fv uu____5976  in
                      mkFreeV uu____5975 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6012 =
              let uu____6020 = constr_id_of_sort sort  in
              (uu____6020, [capp])  in
            mkApp uu____6012 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____6029 =
              let uu____6030 =
                let uu____6041 =
                  let uu____6042 =
                    let uu____6047 = mkInteger id2 norng  in
                    (uu____6047, cid_app)  in
                  mkEq uu____6042 norng  in
                ([[capp]], bvar_names, uu____6041)  in
              mkForall rng uu____6030  in
            let uu____6056 = escape a_name  in
            {
              assumption_term = uu____6029;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6056;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decls_t)
  =
  fun rng  ->
    fun uu____6079  ->
      match uu____6079 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6108 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6108  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6143 =
              let uu____6144 =
                let uu____6150 = bvar_name i  in (uu____6150, s)  in
              mk_fv uu____6144  in
            FStar_All.pipe_left mkFreeV uu____6143  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6186  ->
                      match uu____6186 with
                      | (uu____6196,s,uu____6198) ->
                          let uu____6203 = bvar i s  in uu____6203 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6231 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6269  ->
                      match uu____6269 with
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
                              let uu____6302 =
                                let uu____6303 =
                                  let uu____6314 =
                                    let uu____6315 =
                                      let uu____6320 =
                                        let uu____6321 = bvar i s  in
                                        uu____6321 norng  in
                                      (cproj_app, uu____6320)  in
                                    mkEq uu____6315 norng  in
                                  ([[capp]], bvar_names, uu____6314)  in
                                mkForall rng uu____6303  in
                              let uu____6334 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6302;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6334;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6231 FStar_List.flatten
  
let (constructor_to_decl : FStar_Range.range -> constructor_t -> decls_t) =
  fun rng  ->
    fun uu____6355  ->
      match uu____6355 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6401  ->
                    match uu____6401 with
                    | (uu____6410,sort1,uu____6412) -> sort1))
             in
          let cdecl =
            DeclFun
              (name, field_sorts, sort,
                (FStar_Pervasives_Native.Some "Constructor"))
             in
          let cid = fresh_constructor rng (name, field_sorts, sort, id1)  in
          let disc =
            let disc_name = Prims.strcat "is-" name  in
            let xfv = mk_fv ("x", sort)  in
            let xx = mkFreeV xfv norng  in
            let disc_eq =
              let uu____6437 =
                let uu____6442 =
                  let uu____6443 =
                    let uu____6451 = constr_id_of_sort sort  in
                    (uu____6451, [xx])  in
                  mkApp uu____6443 norng  in
                let uu____6456 =
                  let uu____6457 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6457 norng  in
                (uu____6442, uu____6456)  in
              mkEq uu____6437 norng  in
            let uu____6459 =
              let uu____6478 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6542  ->
                          match uu____6542 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6572 = mkApp (proj, [xx]) norng  in
                                (uu____6572, [])
                              else
                                (let fi =
                                   let uu____6581 =
                                     let uu____6587 =
                                       let uu____6589 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "f_" uu____6589  in
                                     (uu____6587, s)  in
                                   mk_fv uu____6581  in
                                 let uu____6593 = mkFreeV fi norng  in
                                 (uu____6593, [fi]))))
                 in
              FStar_All.pipe_right uu____6478 FStar_List.split  in
            match uu____6459 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6690 =
                    let uu____6695 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6695)  in
                  mkEq uu____6690 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6708 ->
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
          let uu____6743 =
            let uu____6746 =
              let uu____6747 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6747  in
            uu____6746 :: cdecl :: cid :: projs  in
          let uu____6750 =
            let uu____6753 =
              let uu____6756 =
                let uu____6757 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6757  in
              [uu____6756]  in
            FStar_List.append [disc] uu____6753  in
          FStar_List.append uu____6743 uu____6750
  
let (name_binders_inner :
  Prims.string FStar_Pervasives_Native.option ->
    fv Prims.list ->
      Prims.int ->
        sort Prims.list ->
          (fv Prims.list * Prims.string Prims.list * Prims.int))
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____6809 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6858  ->
                    fun s  ->
                      match uu____6858 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6903 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6914 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6914  in
                          let names2 =
                            let uu____6919 = mk_fv (nm, s)  in uu____6919 ::
                              names1
                             in
                          let b =
                            let uu____6923 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6923  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6809 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____6994 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____6994 with
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
              (let uu____7158 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7158)
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
                               "Prims.guard_free",{ tm = BoundV uu____7204;
                                                    freevars = uu____7205;
                                                    rng = uu____7206;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7227 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7305 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7305 fv_name
          | FreeV x when fv_force x ->
              let uu____7316 =
                let uu____7318 = fv_name x  in
                Prims.strcat uu____7318 " Dummy_value)"  in
              Prims.strcat "(" uu____7316
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7340 = op_to_string op  in
              let uu____7342 =
                let uu____7344 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7344 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7340 uu____7342
          | Labeled (t2,uu____7356,uu____7357) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7364 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7364 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7392 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7392 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7445 ->
                         let uu____7450 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7469 =
                                     let uu____7471 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7479 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7479) pats2
                                        in
                                     FStar_String.concat " " uu____7471  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7469))
                            in
                         FStar_All.pipe_right uu____7450
                           (FStar_String.concat "\n")
                      in
                   let uu____7489 =
                     let uu____7493 =
                       let uu____7497 =
                         let uu____7501 = aux1 n2 names2 body  in
                         let uu____7503 =
                           let uu____7507 = weightToSmt wopt  in
                           [uu____7507; pats_str; qid]  in
                         uu____7501 :: uu____7503  in
                       binders1 :: uu____7497  in
                     (qop_to_string qop) :: uu____7493  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7489)
          | Let (es,body) ->
              let uu____7523 =
                FStar_List.fold_left
                  (fun uu____7556  ->
                     fun e  ->
                       match uu____7556 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7599 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7599  in
                           let names01 =
                             let uu____7605 = mk_fv (nm, Term_sort)  in
                             uu____7605 :: names0  in
                           let b =
                             let uu____7609 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7609  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7523 with
               | (names2,binders,n2) ->
                   let uu____7643 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7643)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7659 = FStar_Range.string_of_range t1.rng  in
            let uu____7661 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7659
              uu____7661 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___125_7683  ->
      match uu___125_7683 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7694 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7694 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7716 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7791 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7791 (FStar_String.concat "\n")  in
            let uu____7801 = FStar_Options.keep_query_captions ()  in
            if uu____7801
            then
              let uu____7805 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7807 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7805 uu____7807
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7816 =
                let uu____7818 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7818 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7816
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____7859 = caption_to_string print_captions c  in
            let uu____7861 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____7859 f
              (FStar_String.concat " " l) uu____7861
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____7876 = name_macro_binders arg_sorts  in
            (match uu____7876 with
             | (names1,binders) ->
                 let body1 =
                   let uu____7900 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____7900 body  in
                 let uu____7905 = caption_to_string print_captions c  in
                 let uu____7907 = strSort retsort  in
                 let uu____7909 =
                   let uu____7911 = escape f  in
                   termToSmt print_captions uu____7911 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____7905 f (FStar_String.concat " " binders) uu____7907
                   uu____7909)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___126_7938  ->
                      match uu___126_7938 with
                      | Name n1 ->
                          let uu____7941 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____7941
                      | Namespace ns ->
                          let uu____7945 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____7945
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____7955 =
                  let uu____7957 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____7957  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____7955
              else ""  in
            let n1 = a.assumption_name  in
            let uu____7968 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____7970 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____7968
              fids uu____7970 n1
        | Eval t ->
            let uu____7974 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____7974
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____7981 -> ""
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
  fun z3options  ->
    fun decl  ->
      let uu____8002 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8002 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8013 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8013 (FStar_String.concat "\n")

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))"
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
      ((FStar_Pervasives_Native.fst boxRealFun),
        [((FStar_Pervasives_Native.snd boxRealFun), (Sort "Real"), true)],
        Term_sort, (Prims.parse_int "10"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true);
        ("LexCons_1", Term_sort, true);
        ("LexCons_2", Term_sort, true)], Term_sort, (Prims.parse_int "11"),
        true)]
       in
    let bcons =
      let uu____8148 =
        let uu____8152 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8152
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8148 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____8181 =
      let uu____8182 =
        let uu____8184 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8184  in
      let uu____8193 =
        let uu____8196 =
          let uu____8197 =
            let uu____8199 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8199  in
          (uu____8197, (BitVec_sort sz), true)  in
        [uu____8196]  in
      (uu____8182, uu____8193, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8181 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8240  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8265 =
       let uu____8267 = FStar_ST.op_Bang __range_c  in
       uu____8267 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8265);
    (let uu____8312 =
       let uu____8320 = let uu____8323 = mkInteger' i norng  in [uu____8323]
          in
       ("Range_const", uu____8320)  in
     mkApp uu____8312 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8366 =
        let uu____8374 = let uu____8377 = mkInteger' i norng  in [uu____8377]
           in
        ("Tm_uvar", uu____8374)  in
      mkApp uu____8366 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8420 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8444 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8444 u v1 t
  
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
  
let (boxReal : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxRealFun)
      (FStar_Pervasives_Native.snd boxRealFun) t
  
let (unboxReal : term -> term) =
  fun t  ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxRealFun)
      (FStar_Pervasives_Native.fst boxRealFun) t
  
let (boxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8539 =
        let uu____8541 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8541  in
      let uu____8550 =
        let uu____8552 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8552  in
      elim_box true uu____8539 uu____8550 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8575 =
        let uu____8577 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8577  in
      let uu____8586 =
        let uu____8588 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8588  in
      elim_box true uu____8575 uu____8586 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8612 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8627 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8653 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8653
         | uu____8656 -> FStar_Pervasives_Native.None)
    | uu____8658 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8676::t1::t2::[]);
                       freevars = uu____8679; rng = uu____8680;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8699::t1::t2::[]);
                       freevars = uu____8702; rng = uu____8703;_}::[])
        -> let uu____8722 = mkEq (t1, t2) norng  in mkNot uu____8722 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8725; rng = uu____8726;_}::[])
        ->
        let uu____8745 =
          let uu____8750 = unboxInt t1  in
          let uu____8751 = unboxInt t2  in (uu____8750, uu____8751)  in
        mkLTE uu____8745 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8754; rng = uu____8755;_}::[])
        ->
        let uu____8774 =
          let uu____8779 = unboxInt t1  in
          let uu____8780 = unboxInt t2  in (uu____8779, uu____8780)  in
        mkLT uu____8774 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8783; rng = uu____8784;_}::[])
        ->
        let uu____8803 =
          let uu____8808 = unboxInt t1  in
          let uu____8809 = unboxInt t2  in (uu____8808, uu____8809)  in
        mkGTE uu____8803 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8812; rng = uu____8813;_}::[])
        ->
        let uu____8832 =
          let uu____8837 = unboxInt t1  in
          let uu____8838 = unboxInt t2  in (uu____8837, uu____8838)  in
        mkGT uu____8832 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8841; rng = uu____8842;_}::[])
        ->
        let uu____8861 =
          let uu____8866 = unboxBool t1  in
          let uu____8867 = unboxBool t2  in (uu____8866, uu____8867)  in
        mkAnd uu____8861 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____8870; rng = uu____8871;_}::[])
        ->
        let uu____8890 =
          let uu____8895 = unboxBool t1  in
          let uu____8896 = unboxBool t2  in (uu____8895, uu____8896)  in
        mkOr uu____8890 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____8898; rng = uu____8899;_}::[])
        -> let uu____8918 = unboxBool t1  in mkNot uu____8918 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____8922; rng = uu____8923;_}::[])
        when
        let uu____8942 = getBoxedInteger t0  in FStar_Util.is_some uu____8942
        ->
        let sz =
          let uu____8949 = getBoxedInteger t0  in
          match uu____8949 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____8957 -> failwith "impossible"  in
        let uu____8963 =
          let uu____8968 = unboxBitVec sz t1  in
          let uu____8969 = unboxBitVec sz t2  in (uu____8968, uu____8969)  in
        mkBvUlt uu____8963 t.rng
    | App
        (Var
         "Prims.equals",uu____8970::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____8974;
                                      rng = uu____8975;_}::uu____8976::[])
        when
        let uu____8995 = getBoxedInteger t0  in FStar_Util.is_some uu____8995
        ->
        let sz =
          let uu____9002 = getBoxedInteger t0  in
          match uu____9002 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9010 -> failwith "impossible"  in
        let uu____9016 =
          let uu____9021 = unboxBitVec sz t1  in
          let uu____9022 = unboxBitVec sz t2  in (uu____9021, uu____9022)  in
        mkBvUlt uu____9016 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___127_9027 = unboxBool t1  in
        {
          tm = (uu___127_9027.tm);
          freevars = (uu___127_9027.freevars);
          rng = (t.rng)
        }
    | uu____9028 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9089 = FStar_Options.unthrottle_inductives ()  in
        if uu____9089
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
    let uu____9222 =
      let uu____9223 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9223 t t.rng  in
    FStar_All.pipe_right uu____9222 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9241 =
        let uu____9249 = let uu____9252 = mkInteger' i norng  in [uu____9252]
           in
        ("FString_const", uu____9249)  in
      mkApp uu____9241 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9283 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9283 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9330 =
         let uu____9338 =
           let uu____9341 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9341]  in
         ("SFuel", uu____9338)  in
       mkApp uu____9330 norng)
  
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
            let uu____9389 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9389
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
      let uu____9452 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9452
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9472 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9472
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9483 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9483
  
let (dummy_sort : sort) = Sort "Dummy_sort" 