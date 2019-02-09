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
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____442 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____453 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____464 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____475 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____486 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____497 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____508 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____519 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____530 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____541 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____552 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____563 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____574 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____585 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____598 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____622 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____644 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____655 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____668 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____690 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____701 -> false
  
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
    match projectee with | Integer _0 -> true | uu____861 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____885 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____909 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____940 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____990 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____1047 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1130 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1175 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1221 -> false
  
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
    match projectee with | Name _0 -> true | uu____1445 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1465 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1486 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1676 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1699 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1765 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1824 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1845 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1875 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1916 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1937 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1963 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1991 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____2002 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____2013 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____2024 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____2042 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2079 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2090 -> false
  
type decls_t = decl Prims.list
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2113  -> match uu____2113 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____2133 = x  in
    match uu____2133 with | (nm,uu____2136,uu____2137) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____2148 = x  in
    match uu____2148 with | (uu____2149,sort,uu____2151) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____2163 = x  in
    match uu____2163 with | (uu____2165,uu____2166,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____2184 = fv_name x  in
      let uu____2186 = fv_name y  in uu____2184 = uu____2186
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2220 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___119_2231  ->
    match uu___119_2231 with
    | { tm = FreeV x; freevars = uu____2233; rng = uu____2234;_} -> fv_sort x
    | uu____2255 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___120_2262  ->
    match uu___120_2262 with
    | { tm = FreeV fv; freevars = uu____2264; rng = uu____2265;_} -> fv
    | uu____2286 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2314 -> []
    | Real uu____2324 -> []
    | BoundV uu____2334 -> []
    | FreeV fv -> [fv]
    | App (uu____2369,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2383,uu____2384,uu____2385,uu____2386,t1) -> freevars t1
    | Labeled (t1,uu____2407,uu____2408) -> freevars t1
    | LblPos (t1,uu____2412) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2435 = FStar_ST.op_Bang t.freevars  in
    match uu____2435 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2533 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2533  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___121_2612  ->
    match uu___121_2612 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___122_2622  ->
    match uu___122_2622 with
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
        let uu____2657 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2657
    | NatToBv n1 ->
        let uu____2662 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2662
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___123_2676  ->
    match uu___123_2676 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2686 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2686
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____2708 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2708
    | FreeV x ->
        let uu____2720 = fv_name x  in
        let uu____2722 =
          let uu____2724 = let uu____2726 = fv_sort x  in strSort uu____2726
             in
          Prims.strcat ":" uu____2724  in
        Prims.strcat uu____2720 uu____2722
    | App (op,tms) ->
        let uu____2734 =
          let uu____2736 = op_to_string op  in
          let uu____2738 =
            let uu____2740 =
              let uu____2742 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2742 (FStar_String.concat " ")  in
            Prims.strcat uu____2740 ")"  in
          Prims.strcat uu____2736 uu____2738  in
        Prims.strcat "(" uu____2734
    | Labeled (t1,r1,r2) ->
        let uu____2759 = hash_of_term t1  in
        let uu____2761 =
          let uu____2763 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2763  in
        Prims.strcat uu____2759 uu____2761
    | LblPos (t1,r) ->
        let uu____2769 =
          let uu____2771 = hash_of_term t1  in
          Prims.strcat uu____2771
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2769
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2799 =
          let uu____2801 =
            let uu____2803 =
              let uu____2805 =
                let uu____2807 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2807 (FStar_String.concat " ")  in
              let uu____2817 =
                let uu____2819 =
                  let uu____2821 = hash_of_term body  in
                  let uu____2823 =
                    let uu____2825 =
                      let uu____2827 = weightToSmt wopt  in
                      let uu____2829 =
                        let uu____2831 =
                          let uu____2833 =
                            let uu____2835 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2854 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2854
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2835
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2833 "))"  in
                        Prims.strcat " " uu____2831  in
                      Prims.strcat uu____2827 uu____2829  in
                    Prims.strcat " " uu____2825  in
                  Prims.strcat uu____2821 uu____2823  in
                Prims.strcat ")(! " uu____2819  in
              Prims.strcat uu____2805 uu____2817  in
            Prims.strcat " (" uu____2803  in
          Prims.strcat (qop_to_string qop) uu____2801  in
        Prims.strcat "(" uu____2799
    | Let (es,body) ->
        let uu____2881 =
          let uu____2883 =
            let uu____2885 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2885 (FStar_String.concat " ")  in
          let uu____2895 =
            let uu____2897 =
              let uu____2899 = hash_of_term body  in
              Prims.strcat uu____2899 ")"  in
            Prims.strcat ") " uu____2897  in
          Prims.strcat uu____2883 uu____2895  in
        Prims.strcat "(let (" uu____2881

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____2960 =
      let uu____2962 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____2962  in
    mkBoxFunctions uu____2960
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____2987 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____2987 = "Box") &&
        (let uu____2994 =
           let uu____2996 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____2996  in
         Prims.op_Negation uu____2994)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3020 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3020; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3106 =
        let uu____3107 = FStar_Util.ensure_decimal i  in Integer uu____3107
         in
      mk uu____3106 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3122 = FStar_Util.string_of_int i  in mkInteger uu____3122 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3200  ->
    fun r  -> match uu____3200 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3230) -> mkFalse r
      | App (FalseOp ,uu____3235) -> mkTrue r
      | uu____3240 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3256  ->
    fun r  ->
      match uu____3256 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3264),uu____3265) -> t2
           | (uu____3270,App (TrueOp ,uu____3271)) -> t1
           | (App (FalseOp ,uu____3276),uu____3277) -> mkFalse r
           | (uu____3282,App (FalseOp ,uu____3283)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3300,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3309) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3316 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3336  ->
    fun r  ->
      match uu____3336 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3344),uu____3345) -> mkTrue r
           | (uu____3350,App (TrueOp ,uu____3351)) -> mkTrue r
           | (App (FalseOp ,uu____3356),uu____3357) -> t2
           | (uu____3362,App (FalseOp ,uu____3363)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3380,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3389) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3396 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3416  ->
    fun r  ->
      match uu____3416 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3424,App (TrueOp ,uu____3425)) -> mkTrue r
           | (App (FalseOp ,uu____3430),uu____3431) -> mkTrue r
           | (App (TrueOp ,uu____3436),uu____3437) -> t2
           | (uu____3442,App (Imp ,t1'::t2'::[])) ->
               let uu____3447 =
                 let uu____3454 =
                   let uu____3457 = mkAnd (t1, t1') r  in [uu____3457; t2']
                    in
                 (Imp, uu____3454)  in
               mkApp' uu____3447 r
           | uu____3460 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3485  ->
      fun r  -> match uu____3485 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3645  ->
      fun r  ->
        match uu____3645 with
        | (t1,t2) ->
            let uu____3654 =
              let uu____3661 =
                let uu____3664 =
                  let uu____3667 = mkNatToBv sz t2 r  in [uu____3667]  in
                t1 :: uu____3664  in
              (BvShl, uu____3661)  in
            mkApp' uu____3654 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3689  ->
      fun r  ->
        match uu____3689 with
        | (t1,t2) ->
            let uu____3698 =
              let uu____3705 =
                let uu____3708 =
                  let uu____3711 = mkNatToBv sz t2 r  in [uu____3711]  in
                t1 :: uu____3708  in
              (BvShr, uu____3705)  in
            mkApp' uu____3698 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3733  ->
      fun r  ->
        match uu____3733 with
        | (t1,t2) ->
            let uu____3742 =
              let uu____3749 =
                let uu____3752 =
                  let uu____3755 = mkNatToBv sz t2 r  in [uu____3755]  in
                t1 :: uu____3752  in
              (BvUdiv, uu____3749)  in
            mkApp' uu____3742 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3777  ->
      fun r  ->
        match uu____3777 with
        | (t1,t2) ->
            let uu____3786 =
              let uu____3793 =
                let uu____3796 =
                  let uu____3799 = mkNatToBv sz t2 r  in [uu____3799]  in
                t1 :: uu____3796  in
              (BvMod, uu____3793)  in
            mkApp' uu____3786 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3821  ->
      fun r  ->
        match uu____3821 with
        | (t1,t2) ->
            let uu____3830 =
              let uu____3837 =
                let uu____3840 =
                  let uu____3843 = mkNatToBv sz t2 r  in [uu____3843]  in
                t1 :: uu____3840  in
              (BvMul, uu____3837)  in
            mkApp' uu____3830 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3885  ->
    fun r  ->
      match uu____3885 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3904 -> mk_bin_op Eq (t1, t2) r)
  
let (mkLT : (term * term) -> FStar_Range.range -> term) = mk_bin_op LT 
let (mkLTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op LTE 
let (mkGT : (term * term) -> FStar_Range.range -> term) = mk_bin_op GT 
let (mkGTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op GTE 
let (mkAdd : (term * term) -> FStar_Range.range -> term) = mk_bin_op Add 
let (mkSub : (term * term) -> FStar_Range.range -> term) = mk_bin_op Sub 
let (mkDiv : (term * term) -> FStar_Range.range -> term) = mk_bin_op Div 
let (mkMul : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mul 
let (mkMod : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mod 
let (mkRealOfInt : term -> FStar_Range.range -> term) =
  fun t  -> fun r  -> mkApp ("to_real", [t]) r 
let (mkITE : (term * term * term) -> FStar_Range.range -> term) =
  fun uu____4056  ->
    fun r  ->
      match uu____4056 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4067) -> t2
           | App (FalseOp ,uu____4072) -> t3
           | uu____4077 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4078),App (TrueOp ,uu____4079)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4088),uu____4089) ->
                    let uu____4094 =
                      let uu____4099 = mkNot t1 t1.rng  in (uu____4099, t3)
                       in
                    mkImp uu____4094 r
                | (uu____4100,App (TrueOp ,uu____4101)) -> mkImp (t1, t2) r
                | (uu____4106,uu____4107) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4163 -> FStar_Pervasives_Native.None
      | Real uu____4165 -> FStar_Pervasives_Native.None
      | BoundV uu____4167 -> FStar_Pervasives_Native.None
      | FreeV uu____4169 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4193 -> true
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
            | BvUext uu____4225 -> false
            | NatToBv uu____4228 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4239,uu____4240) -> aux t2
      | Quant uu____4243 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4263 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4278 = aux t1  in
          (match uu____4278 with
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
        let uu____4316 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4316
    | FreeV fv ->
        let uu____4328 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4328
    | App (op,l) ->
        let uu____4337 = op_to_string op  in
        let uu____4339 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4337 uu____4339
    | Labeled (t1,r1,r2) ->
        let uu____4347 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4347
    | LblPos (t1,s) ->
        let uu____4354 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4354
    | Quant (qop,l,uu____4359,uu____4360,t1) ->
        let uu____4380 = print_smt_term_list_list l  in
        let uu____4382 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4380
          uu____4382
    | Let (es,body) ->
        let uu____4391 = print_smt_term_list es  in
        let uu____4393 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4391 uu____4393

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4400 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4400 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4427 =
             let uu____4429 =
               let uu____4431 = print_smt_term_list l1  in
               Prims.strcat uu____4431 " ] "  in
             Prims.strcat "; [ " uu____4429  in
           Prims.strcat s uu____4427) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4471  ->
        match uu____4471 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4540 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4540 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4555 =
                         let uu____4561 =
                           let uu____4563 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4563
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4561)
                          in
                       FStar_Errors.log_issue r uu____4555);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4574) -> body
               | uu____4579 ->
                   let uu____4580 =
                     let uu____4581 =
                       let uu____4601 = all_pats_ok pats  in
                       (qop, uu____4601, wopt, vars, body)  in
                     Quant uu____4581  in
                   mk uu____4580 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4630  ->
    fun r  ->
      match uu____4630 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4676 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4676 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4709 = FStar_ST.op_Bang t1.freevars  in
        match uu____4709 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4783 ->
            (match t1.tm with
             | Integer uu____4796 -> t1
             | Real uu____4798 -> t1
             | BoundV uu____4800 -> t1
             | FreeV x ->
                 let uu____4811 = index_of1 x  in
                 (match uu____4811 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4825 =
                   let uu____4832 = FStar_List.map (aux ix) tms  in
                   (op, uu____4832)  in
                 mkApp' uu____4825 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4842 =
                   let uu____4843 =
                     let uu____4851 = aux ix t2  in (uu____4851, r1, r2)  in
                   Labeled uu____4843  in
                 mk uu____4842 t2.rng
             | LblPos (t2,r) ->
                 let uu____4857 =
                   let uu____4858 =
                     let uu____4864 = aux ix t2  in (uu____4864, r)  in
                   LblPos uu____4858  in
                 mk uu____4857 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4890 =
                   let uu____4910 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4931 = aux (ix + n1) body  in
                   (qop, uu____4910, wopt, vars, uu____4931)  in
                 mkQuant t1.rng false uu____4890
             | Let (es,body) ->
                 let uu____4952 =
                   FStar_List.fold_left
                     (fun uu____4972  ->
                        fun e  ->
                          match uu____4972 with
                          | (ix1,l) ->
                              let uu____4996 =
                                let uu____4999 = aux ix1 e  in uu____4999 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____4996))
                     (ix, []) es
                    in
                 (match uu____4952 with
                  | (ix1,es_rev) ->
                      let uu____5015 =
                        let uu____5022 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5022)  in
                      mkLet uu____5015 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5058 -> t1
        | Real uu____5060 -> t1
        | FreeV uu____5062 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5087 =
              let uu____5094 = FStar_List.map (aux shift) tms2  in
              (op, uu____5094)  in
            mkApp' uu____5087 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5104 =
              let uu____5105 =
                let uu____5113 = aux shift t2  in (uu____5113, r1, r2)  in
              Labeled uu____5105  in
            mk uu____5104 t2.rng
        | LblPos (t2,r) ->
            let uu____5119 =
              let uu____5120 =
                let uu____5126 = aux shift t2  in (uu____5126, r)  in
              LblPos uu____5120  in
            mk uu____5119 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5158 =
              let uu____5178 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5195 = aux shift1 body  in
              (qop, uu____5178, wopt, vars, uu____5195)  in
            mkQuant t1.rng false uu____5158
        | Let (es,body) ->
            let uu____5212 =
              FStar_List.fold_left
                (fun uu____5232  ->
                   fun e  ->
                     match uu____5232 with
                     | (ix,es1) ->
                         let uu____5256 =
                           let uu____5259 = aux shift e  in uu____5259 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5256))
                (shift, []) es
               in
            (match uu____5212 with
             | (shift1,es_rev) ->
                 let uu____5275 =
                   let uu____5282 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5282)  in
                 mkLet uu____5275 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5302 = abstr [fv] t  in inst [s] uu____5302
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5332  ->
      match uu____5332 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5375 =
            let uu____5395 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5412 = FStar_List.map fv_sort vars  in
            let uu____5415 = abstr vars body  in
            (qop, uu____5395, wopt, uu____5412, uu____5415)  in
          mkQuant r true uu____5375
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5446  ->
      match uu____5446 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5505  ->
      match uu____5505 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5580  ->
      match uu____5580 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5643  ->
      match uu____5643 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5694  ->
    fun r  ->
      match uu____5694 with
      | (bindings,body) ->
          let uu____5720 = FStar_List.split bindings  in
          (match uu____5720 with
           | (vars,es) ->
               let uu____5739 =
                 let uu____5746 = abstr vars body  in (es, uu____5746)  in
               mkLet uu____5739 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5768  ->
    match uu____5768 with
    | (nm,vars,s,tm,c) ->
        let uu____5793 =
          let uu____5807 = FStar_List.map fv_sort vars  in
          let uu____5810 = abstr vars tm  in
          (nm, uu____5807, s, uu____5810, c)  in
        DefineFun uu____5793
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5821 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5821
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5839  ->
    fun id1  ->
      match uu____5839 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5855 =
              let uu____5856 =
                let uu____5861 = mkInteger' id1 norng  in
                let uu____5862 =
                  let uu____5863 =
                    let uu____5871 = constr_id_of_sort sort  in
                    let uu____5873 =
                      let uu____5876 = mkApp (tok_name, []) norng  in
                      [uu____5876]  in
                    (uu____5871, uu____5873)  in
                  mkApp uu____5863 norng  in
                (uu____5861, uu____5862)  in
              mkEq uu____5856 norng  in
            let uu____5883 = escape a_name  in
            {
              assumption_term = uu____5855;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5883;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5909  ->
      match uu____5909 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5949 =
                        let uu____5950 =
                          let uu____5956 =
                            let uu____5958 = FStar_Util.string_of_int i  in
                            Prims.strcat "x_" uu____5958  in
                          (uu____5956, s)  in
                        mk_fv uu____5950  in
                      mkFreeV uu____5949 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____5986 =
              let uu____5994 = constr_id_of_sort sort  in
              (uu____5994, [capp])  in
            mkApp uu____5986 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____6003 =
              let uu____6004 =
                let uu____6015 =
                  let uu____6016 =
                    let uu____6021 = mkInteger id2 norng  in
                    (uu____6021, cid_app)  in
                  mkEq uu____6016 norng  in
                ([[capp]], bvar_names, uu____6015)  in
              mkForall rng uu____6004  in
            let uu____6030 = escape a_name  in
            {
              assumption_term = uu____6003;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6030;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decls_t)
  =
  fun rng  ->
    fun uu____6053  ->
      match uu____6053 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6082 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6082  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6117 =
              let uu____6118 =
                let uu____6124 = bvar_name i  in (uu____6124, s)  in
              mk_fv uu____6118  in
            FStar_All.pipe_left mkFreeV uu____6117  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6160  ->
                      match uu____6160 with
                      | (uu____6170,s,uu____6172) ->
                          let uu____6177 = bvar i s  in uu____6177 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6205 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6243  ->
                      match uu____6243 with
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
                              let uu____6276 =
                                let uu____6277 =
                                  let uu____6288 =
                                    let uu____6289 =
                                      let uu____6294 =
                                        let uu____6295 = bvar i s  in
                                        uu____6295 norng  in
                                      (cproj_app, uu____6294)  in
                                    mkEq uu____6289 norng  in
                                  ([[capp]], bvar_names, uu____6288)  in
                                mkForall rng uu____6277  in
                              let uu____6308 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6276;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6308;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6205 FStar_List.flatten
  
let (constructor_to_decl : FStar_Range.range -> constructor_t -> decls_t) =
  fun rng  ->
    fun uu____6329  ->
      match uu____6329 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6375  ->
                    match uu____6375 with
                    | (uu____6384,sort1,uu____6386) -> sort1))
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
              let uu____6411 =
                let uu____6416 =
                  let uu____6417 =
                    let uu____6425 = constr_id_of_sort sort  in
                    (uu____6425, [xx])  in
                  mkApp uu____6417 norng  in
                let uu____6430 =
                  let uu____6431 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6431 norng  in
                (uu____6416, uu____6430)  in
              mkEq uu____6411 norng  in
            let uu____6433 =
              let uu____6452 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6516  ->
                          match uu____6516 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6546 = mkApp (proj, [xx]) norng  in
                                (uu____6546, [])
                              else
                                (let fi =
                                   let uu____6555 =
                                     let uu____6561 =
                                       let uu____6563 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "f_" uu____6563  in
                                     (uu____6561, s)  in
                                   mk_fv uu____6555  in
                                 let uu____6567 = mkFreeV fi norng  in
                                 (uu____6567, [fi]))))
                 in
              FStar_All.pipe_right uu____6452 FStar_List.split  in
            match uu____6433 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6664 =
                    let uu____6669 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6669)  in
                  mkEq uu____6664 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6682 ->
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
          let uu____6717 =
            let uu____6720 =
              let uu____6721 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6721  in
            uu____6720 :: cdecl :: cid :: projs  in
          let uu____6724 =
            let uu____6727 =
              let uu____6730 =
                let uu____6731 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6731  in
              [uu____6730]  in
            FStar_List.append [disc] uu____6727  in
          FStar_List.append uu____6717 uu____6724
  
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
          let uu____6783 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6832  ->
                    fun s  ->
                      match uu____6832 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6877 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6888 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6888  in
                          let names2 =
                            let uu____6893 = mk_fv (nm, s)  in uu____6893 ::
                              names1
                             in
                          let b =
                            let uu____6897 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6897  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6783 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____6968 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____6968 with
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
              (let uu____7132 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7132)
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
                               "Prims.guard_free",{ tm = BoundV uu____7178;
                                                    freevars = uu____7179;
                                                    rng = uu____7180;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7201 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7279 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7279 fv_name
          | FreeV x when fv_force x ->
              let uu____7290 =
                let uu____7292 = fv_name x  in
                Prims.strcat uu____7292 " Dummy_value)"  in
              Prims.strcat "(" uu____7290
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7314 = op_to_string op  in
              let uu____7316 =
                let uu____7318 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7318 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7314 uu____7316
          | Labeled (t2,uu____7330,uu____7331) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7338 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7338 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7366 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7366 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7419 ->
                         let uu____7424 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7443 =
                                     let uu____7445 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7453 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7453) pats2
                                        in
                                     FStar_String.concat " " uu____7445  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7443))
                            in
                         FStar_All.pipe_right uu____7424
                           (FStar_String.concat "\n")
                      in
                   let uu____7463 =
                     let uu____7467 =
                       let uu____7471 =
                         let uu____7475 = aux1 n2 names2 body  in
                         let uu____7477 =
                           let uu____7481 = weightToSmt wopt  in
                           [uu____7481; pats_str; qid]  in
                         uu____7475 :: uu____7477  in
                       binders1 :: uu____7471  in
                     (qop_to_string qop) :: uu____7467  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7463)
          | Let (es,body) ->
              let uu____7497 =
                FStar_List.fold_left
                  (fun uu____7530  ->
                     fun e  ->
                       match uu____7530 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7573 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7573  in
                           let names01 =
                             let uu____7579 = mk_fv (nm, Term_sort)  in
                             uu____7579 :: names0  in
                           let b =
                             let uu____7583 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7583  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7497 with
               | (names2,binders,n2) ->
                   let uu____7617 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7617)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7633 = FStar_Range.string_of_range t1.rng  in
            let uu____7635 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7633
              uu____7635 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___124_7657  ->
      match uu___124_7657 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7668 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7668 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7690 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7765 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7765 (FStar_String.concat "\n")  in
            let uu____7775 = FStar_Options.keep_query_captions ()  in
            if uu____7775
            then
              let uu____7779 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7781 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7779 uu____7781
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7790 =
                let uu____7792 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7792 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7790
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____7833 = caption_to_string print_captions c  in
            let uu____7835 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____7833 f
              (FStar_String.concat " " l) uu____7835
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____7850 = name_macro_binders arg_sorts  in
            (match uu____7850 with
             | (names1,binders) ->
                 let body1 =
                   let uu____7874 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____7874 body  in
                 let uu____7879 = caption_to_string print_captions c  in
                 let uu____7881 = strSort retsort  in
                 let uu____7883 =
                   let uu____7885 = escape f  in
                   termToSmt print_captions uu____7885 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____7879 f (FStar_String.concat " " binders) uu____7881
                   uu____7883)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___125_7912  ->
                      match uu___125_7912 with
                      | Name n1 ->
                          let uu____7915 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____7915
                      | Namespace ns ->
                          let uu____7919 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____7919
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____7929 =
                  let uu____7931 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____7931  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____7929
              else ""  in
            let n1 = a.assumption_name  in
            let uu____7942 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____7944 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____7942
              fids uu____7944 n1
        | Eval t ->
            let uu____7948 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____7948
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____7955 -> ""
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
      let uu____7976 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____7976 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____7987 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____7987 (FStar_String.concat "\n")

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))"
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
      let uu____8122 =
        let uu____8126 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8126
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8122 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____8155 =
      let uu____8156 =
        let uu____8158 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8158  in
      let uu____8167 =
        let uu____8170 =
          let uu____8171 =
            let uu____8173 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8173  in
          (uu____8171, (BitVec_sort sz), true)  in
        [uu____8170]  in
      (uu____8156, uu____8167, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8155 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8214  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8239 =
       let uu____8241 = FStar_ST.op_Bang __range_c  in
       uu____8241 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8239);
    (let uu____8286 =
       let uu____8294 = let uu____8297 = mkInteger' i norng  in [uu____8297]
          in
       ("Range_const", uu____8294)  in
     mkApp uu____8286 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8340 =
        let uu____8348 = let uu____8351 = mkInteger' i norng  in [uu____8351]
           in
        ("Tm_uvar", uu____8348)  in
      mkApp uu____8340 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8394 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8418 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8418 u v1 t
  
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
      let uu____8513 =
        let uu____8515 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8515  in
      let uu____8524 =
        let uu____8526 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8526  in
      elim_box true uu____8513 uu____8524 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8549 =
        let uu____8551 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8551  in
      let uu____8560 =
        let uu____8562 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8562  in
      elim_box true uu____8549 uu____8560 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8586 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8601 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8627 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8627
         | uu____8630 -> FStar_Pervasives_Native.None)
    | uu____8632 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8650::t1::t2::[]);
                       freevars = uu____8653; rng = uu____8654;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8673::t1::t2::[]);
                       freevars = uu____8676; rng = uu____8677;_}::[])
        -> let uu____8696 = mkEq (t1, t2) norng  in mkNot uu____8696 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8699; rng = uu____8700;_}::[])
        ->
        let uu____8719 =
          let uu____8724 = unboxInt t1  in
          let uu____8725 = unboxInt t2  in (uu____8724, uu____8725)  in
        mkLTE uu____8719 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8728; rng = uu____8729;_}::[])
        ->
        let uu____8748 =
          let uu____8753 = unboxInt t1  in
          let uu____8754 = unboxInt t2  in (uu____8753, uu____8754)  in
        mkLT uu____8748 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8757; rng = uu____8758;_}::[])
        ->
        let uu____8777 =
          let uu____8782 = unboxInt t1  in
          let uu____8783 = unboxInt t2  in (uu____8782, uu____8783)  in
        mkGTE uu____8777 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8786; rng = uu____8787;_}::[])
        ->
        let uu____8806 =
          let uu____8811 = unboxInt t1  in
          let uu____8812 = unboxInt t2  in (uu____8811, uu____8812)  in
        mkGT uu____8806 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8815; rng = uu____8816;_}::[])
        ->
        let uu____8835 =
          let uu____8840 = unboxBool t1  in
          let uu____8841 = unboxBool t2  in (uu____8840, uu____8841)  in
        mkAnd uu____8835 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____8844; rng = uu____8845;_}::[])
        ->
        let uu____8864 =
          let uu____8869 = unboxBool t1  in
          let uu____8870 = unboxBool t2  in (uu____8869, uu____8870)  in
        mkOr uu____8864 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____8872; rng = uu____8873;_}::[])
        -> let uu____8892 = unboxBool t1  in mkNot uu____8892 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____8896; rng = uu____8897;_}::[])
        when
        let uu____8916 = getBoxedInteger t0  in FStar_Util.is_some uu____8916
        ->
        let sz =
          let uu____8923 = getBoxedInteger t0  in
          match uu____8923 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____8931 -> failwith "impossible"  in
        let uu____8937 =
          let uu____8942 = unboxBitVec sz t1  in
          let uu____8943 = unboxBitVec sz t2  in (uu____8942, uu____8943)  in
        mkBvUlt uu____8937 t.rng
    | App
        (Var
         "Prims.equals",uu____8944::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____8948;
                                      rng = uu____8949;_}::uu____8950::[])
        when
        let uu____8969 = getBoxedInteger t0  in FStar_Util.is_some uu____8969
        ->
        let sz =
          let uu____8976 = getBoxedInteger t0  in
          match uu____8976 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____8984 -> failwith "impossible"  in
        let uu____8990 =
          let uu____8995 = unboxBitVec sz t1  in
          let uu____8996 = unboxBitVec sz t2  in (uu____8995, uu____8996)  in
        mkBvUlt uu____8990 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___126_9001 = unboxBool t1  in
        {
          tm = (uu___126_9001.tm);
          freevars = (uu___126_9001.freevars);
          rng = (t.rng)
        }
    | uu____9002 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9063 = FStar_Options.unthrottle_inductives ()  in
        if uu____9063
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
    let uu____9196 =
      let uu____9197 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9197 t t.rng  in
    FStar_All.pipe_right uu____9196 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9215 =
        let uu____9223 = let uu____9226 = mkInteger' i norng  in [uu____9226]
           in
        ("FString_const", uu____9223)  in
      mkApp uu____9215 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9257 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9257 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9304 =
         let uu____9312 =
           let uu____9315 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9315]  in
         ("SFuel", uu____9312)  in
       mkApp uu____9304 norng)
  
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
            let uu____9363 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9363
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
      let uu____9426 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9426
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9446 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9446
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9457 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9457
  
let (dummy_sort : sort) = Sort "Dummy_sort" 