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
  | BoundV of Prims.int 
  | FreeV of (Prims.string * sort) 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int
  FStar_Pervasives_Native.option * sort Prims.list * term) 
  | Let of (term Prims.list * term) 
  | Labeled of (term * Prims.string * FStar_Range.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars: (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo ;
  rng: FStar_Range.range }
let (uu___is_Integer : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____849 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____873 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____901 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____942 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____999 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1082 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1127 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1173 -> false
  
let (__proj__LblPos__item___0 : term' -> (term * Prims.string)) =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> tm 
let (__proj__Mkterm__item__freevars :
  term -> (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> freevars 
let (__proj__Mkterm__item__rng : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; freevars; rng;_} -> rng 
type pat = term
type fv = (Prims.string * sort)
type fvs = (Prims.string * sort) Prims.list
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
    match projectee with | Name _0 -> true | uu____1376 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1396 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1417 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1607 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1630 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1696 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1755 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1776 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1806 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1847 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1868 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1894 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1922 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1933 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1944 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1955 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1973 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2010 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2021 -> false
  
type decls_t = decl Prims.list
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____2056 'Auu____2057 . ('Auu____2056 * 'Auu____2057) -> 'Auu____2057 =
  fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2096 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___149_2107  ->
    match uu___149_2107 with
    | { tm = FreeV x; freevars = uu____2109; rng = uu____2110;_} -> fv_sort x
    | uu____2126 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___150_2133  ->
    match uu___150_2133 with
    | { tm = FreeV fv; freevars = uu____2135; rng = uu____2136;_} -> fv
    | uu____2151 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2173 -> []
    | BoundV uu____2180 -> []
    | FreeV fv -> [fv]
    | App (uu____2203,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2214,uu____2215,uu____2216,uu____2217,t1) -> freevars t1
    | Labeled (t1,uu____2238,uu____2239) -> freevars t1
    | LblPos (t1,uu____2243) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2263 = FStar_ST.op_Bang t.freevars  in
    match uu____2263 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2340 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2340  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___151_2404  ->
    match uu___151_2404 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___152_2414  ->
    match uu___152_2414 with
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
        let uu____2449 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2449
    | NatToBv n1 ->
        let uu____2454 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2454
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___153_2468  ->
    match uu___153_2468 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2478 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2478
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____2498 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2498
    | FreeV x ->
        let uu____2507 =
          let uu____2509 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____2509  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____2507
    | App (op,tms) ->
        let uu____2520 =
          let uu____2522 = op_to_string op  in
          let uu____2524 =
            let uu____2526 =
              let uu____2528 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2528 (FStar_String.concat " ")  in
            Prims.strcat uu____2526 ")"  in
          Prims.strcat uu____2522 uu____2524  in
        Prims.strcat "(" uu____2520
    | Labeled (t1,r1,r2) ->
        let uu____2545 = hash_of_term t1  in
        let uu____2547 =
          let uu____2549 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2549  in
        Prims.strcat uu____2545 uu____2547
    | LblPos (t1,r) ->
        let uu____2555 =
          let uu____2557 = hash_of_term t1  in
          Prims.strcat uu____2557
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2555
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2585 =
          let uu____2587 =
            let uu____2589 =
              let uu____2591 =
                let uu____2593 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2593 (FStar_String.concat " ")  in
              let uu____2603 =
                let uu____2605 =
                  let uu____2607 = hash_of_term body  in
                  let uu____2609 =
                    let uu____2611 =
                      let uu____2613 = weightToSmt wopt  in
                      let uu____2615 =
                        let uu____2617 =
                          let uu____2619 =
                            let uu____2621 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2640 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2640
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2621
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2619 "))"  in
                        Prims.strcat " " uu____2617  in
                      Prims.strcat uu____2613 uu____2615  in
                    Prims.strcat " " uu____2611  in
                  Prims.strcat uu____2607 uu____2609  in
                Prims.strcat ")(! " uu____2605  in
              Prims.strcat uu____2591 uu____2603  in
            Prims.strcat " (" uu____2589  in
          Prims.strcat (qop_to_string qop) uu____2587  in
        Prims.strcat "(" uu____2585
    | Let (es,body) ->
        let uu____2667 =
          let uu____2669 =
            let uu____2671 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2671 (FStar_String.concat " ")  in
          let uu____2681 =
            let uu____2683 =
              let uu____2685 = hash_of_term body  in
              Prims.strcat uu____2685 ")"  in
            Prims.strcat ") " uu____2683  in
          Prims.strcat uu____2669 uu____2681  in
        Prims.strcat "(let (" uu____2667

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____2746 =
      let uu____2748 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____2748  in
    mkBoxFunctions uu____2746
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____2765 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____2765 = "Box") &&
        (let uu____2772 =
           let uu____2774 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____2774  in
         Prims.op_Negation uu____2772)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____2798 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____2798; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2875 =
        let uu____2876 = FStar_Util.ensure_decimal i  in Integer uu____2876
         in
      mk uu____2875 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____2891 = FStar_Util.string_of_int i  in mkInteger uu____2891 r
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____2966  ->
    fun r  -> match uu____2966 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____2996) -> mkFalse r
      | App (FalseOp ,uu____3001) -> mkTrue r
      | uu____3006 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3022  ->
    fun r  ->
      match uu____3022 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3030),uu____3031) -> t2
           | (uu____3036,App (TrueOp ,uu____3037)) -> t1
           | (App (FalseOp ,uu____3042),uu____3043) -> mkFalse r
           | (uu____3048,App (FalseOp ,uu____3049)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3066,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3075) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3082 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3102  ->
    fun r  ->
      match uu____3102 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3110),uu____3111) -> mkTrue r
           | (uu____3116,App (TrueOp ,uu____3117)) -> mkTrue r
           | (App (FalseOp ,uu____3122),uu____3123) -> t2
           | (uu____3128,App (FalseOp ,uu____3129)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3146,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3155) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3162 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3182  ->
    fun r  ->
      match uu____3182 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3190,App (TrueOp ,uu____3191)) -> mkTrue r
           | (App (FalseOp ,uu____3196),uu____3197) -> mkTrue r
           | (App (TrueOp ,uu____3202),uu____3203) -> t2
           | (uu____3208,App (Imp ,t1'::t2'::[])) ->
               let uu____3213 =
                 let uu____3220 =
                   let uu____3223 = mkAnd (t1, t1') r  in [uu____3223; t2']
                    in
                 (Imp, uu____3220)  in
               mkApp' uu____3213 r
           | uu____3226 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3251  ->
      fun r  -> match uu____3251 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3411  ->
      fun r  ->
        match uu____3411 with
        | (t1,t2) ->
            let uu____3420 =
              let uu____3427 =
                let uu____3430 =
                  let uu____3433 = mkNatToBv sz t2 r  in [uu____3433]  in
                t1 :: uu____3430  in
              (BvShl, uu____3427)  in
            mkApp' uu____3420 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3455  ->
      fun r  ->
        match uu____3455 with
        | (t1,t2) ->
            let uu____3464 =
              let uu____3471 =
                let uu____3474 =
                  let uu____3477 = mkNatToBv sz t2 r  in [uu____3477]  in
                t1 :: uu____3474  in
              (BvShr, uu____3471)  in
            mkApp' uu____3464 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3499  ->
      fun r  ->
        match uu____3499 with
        | (t1,t2) ->
            let uu____3508 =
              let uu____3515 =
                let uu____3518 =
                  let uu____3521 = mkNatToBv sz t2 r  in [uu____3521]  in
                t1 :: uu____3518  in
              (BvUdiv, uu____3515)  in
            mkApp' uu____3508 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3543  ->
      fun r  ->
        match uu____3543 with
        | (t1,t2) ->
            let uu____3552 =
              let uu____3559 =
                let uu____3562 =
                  let uu____3565 = mkNatToBv sz t2 r  in [uu____3565]  in
                t1 :: uu____3562  in
              (BvMod, uu____3559)  in
            mkApp' uu____3552 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3587  ->
      fun r  ->
        match uu____3587 with
        | (t1,t2) ->
            let uu____3596 =
              let uu____3603 =
                let uu____3606 =
                  let uu____3609 = mkNatToBv sz t2 r  in [uu____3609]  in
                t1 :: uu____3606  in
              (BvMul, uu____3603)  in
            mkApp' uu____3596 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3651  ->
    fun r  ->
      match uu____3651 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3670 -> mk_bin_op Eq (t1, t2) r)
  
let (mkLT : (term * term) -> FStar_Range.range -> term) = mk_bin_op LT 
let (mkLTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op LTE 
let (mkGT : (term * term) -> FStar_Range.range -> term) = mk_bin_op GT 
let (mkGTE : (term * term) -> FStar_Range.range -> term) = mk_bin_op GTE 
let (mkAdd : (term * term) -> FStar_Range.range -> term) = mk_bin_op Add 
let (mkSub : (term * term) -> FStar_Range.range -> term) = mk_bin_op Sub 
let (mkDiv : (term * term) -> FStar_Range.range -> term) = mk_bin_op Div 
let (mkMul : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mul 
let (mkMod : (term * term) -> FStar_Range.range -> term) = mk_bin_op Mod 
let (mkITE : (term * term * term) -> FStar_Range.range -> term) =
  fun uu____3807  ->
    fun r  ->
      match uu____3807 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____3818) -> t2
           | App (FalseOp ,uu____3823) -> t3
           | uu____3828 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____3829),App (TrueOp ,uu____3830)) ->
                    mkTrue r
                | (App (TrueOp ,uu____3839),uu____3840) ->
                    let uu____3845 =
                      let uu____3850 = mkNot t1 t1.rng  in (uu____3850, t3)
                       in
                    mkImp uu____3845 r
                | (uu____3851,App (TrueOp ,uu____3852)) -> mkImp (t1, t2) r
                | (uu____3857,uu____3858) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____3914 -> FStar_Pervasives_Native.None
      | BoundV uu____3916 -> FStar_Pervasives_Native.None
      | FreeV uu____3918 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____3939 -> true
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
            | BvUext uu____3971 -> false
            | NatToBv uu____3974 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____3985,uu____3986) -> aux t2
      | Quant uu____3989 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4009 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4024 = aux t1  in
          (match uu____4024 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4059 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4059
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4076 = op_to_string op  in
        let uu____4078 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4076 uu____4078
    | Labeled (t1,r1,r2) ->
        let uu____4086 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4086
    | LblPos (t1,s) ->
        let uu____4093 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4093
    | Quant (qop,l,uu____4098,uu____4099,t1) ->
        let uu____4119 = print_smt_term_list_list l  in
        let uu____4121 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4119
          uu____4121
    | Let (es,body) ->
        let uu____4130 = print_smt_term_list es  in
        let uu____4132 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4130 uu____4132

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4139 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4139 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4166 =
             let uu____4168 =
               let uu____4170 = print_smt_term_list l1  in
               Prims.strcat uu____4170 " ] "  in
             Prims.strcat "; [ " uu____4168  in
           Prims.strcat s uu____4166) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4210  ->
        match uu____4210 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4279 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4279 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4294 =
                         let uu____4300 =
                           let uu____4302 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4302
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4300)
                          in
                       FStar_Errors.log_issue r uu____4294);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4313) -> body
               | uu____4318 ->
                   let uu____4319 =
                     let uu____4320 =
                       let uu____4340 = all_pats_ok pats  in
                       (qop, uu____4340, wopt, vars, body)  in
                     Quant uu____4320  in
                   mk uu____4319 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4369  ->
    fun r  ->
      match uu____4369 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4415 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4415 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4448 = FStar_ST.op_Bang t1.freevars  in
        match uu____4448 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4507 ->
            (match t1.tm with
             | Integer uu____4517 -> t1
             | BoundV uu____4519 -> t1
             | FreeV x ->
                 let uu____4527 = index_of1 x  in
                 (match uu____4527 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4541 =
                   let uu____4548 = FStar_List.map (aux ix) tms  in
                   (op, uu____4548)  in
                 mkApp' uu____4541 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4558 =
                   let uu____4559 =
                     let uu____4567 = aux ix t2  in (uu____4567, r1, r2)  in
                   Labeled uu____4559  in
                 mk uu____4558 t2.rng
             | LblPos (t2,r) ->
                 let uu____4573 =
                   let uu____4574 =
                     let uu____4580 = aux ix t2  in (uu____4580, r)  in
                   LblPos uu____4574  in
                 mk uu____4573 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4606 =
                   let uu____4626 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4647 = aux (ix + n1) body  in
                   (qop, uu____4626, wopt, vars, uu____4647)  in
                 mkQuant t1.rng false uu____4606
             | Let (es,body) ->
                 let uu____4668 =
                   FStar_List.fold_left
                     (fun uu____4688  ->
                        fun e  ->
                          match uu____4688 with
                          | (ix1,l) ->
                              let uu____4712 =
                                let uu____4715 = aux ix1 e  in uu____4715 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____4712))
                     (ix, []) es
                    in
                 (match uu____4668 with
                  | (ix1,es_rev) ->
                      let uu____4731 =
                        let uu____4738 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____4738)  in
                      mkLet uu____4731 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____4774 -> t1
        | FreeV uu____4776 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____4798 =
              let uu____4805 = FStar_List.map (aux shift) tms2  in
              (op, uu____4805)  in
            mkApp' uu____4798 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____4815 =
              let uu____4816 =
                let uu____4824 = aux shift t2  in (uu____4824, r1, r2)  in
              Labeled uu____4816  in
            mk uu____4815 t2.rng
        | LblPos (t2,r) ->
            let uu____4830 =
              let uu____4831 =
                let uu____4837 = aux shift t2  in (uu____4837, r)  in
              LblPos uu____4831  in
            mk uu____4830 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____4869 =
              let uu____4889 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____4906 = aux shift1 body  in
              (qop, uu____4889, wopt, vars, uu____4906)  in
            mkQuant t1.rng false uu____4869
        | Let (es,body) ->
            let uu____4923 =
              FStar_List.fold_left
                (fun uu____4943  ->
                   fun e  ->
                     match uu____4943 with
                     | (ix,es1) ->
                         let uu____4967 =
                           let uu____4970 = aux shift e  in uu____4970 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____4967))
                (shift, []) es
               in
            (match uu____4923 with
             | (shift1,es_rev) ->
                 let uu____4986 =
                   let uu____4993 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____4993)  in
                 mkLet uu____4986 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5013 = abstr [fv] t  in inst [s] uu____5013
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5043  ->
      match uu____5043 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5086 =
            let uu____5106 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5123 = FStar_List.map fv_sort vars  in
            let uu____5127 = abstr vars body  in
            (qop, uu____5106, wopt, uu____5123, uu____5127)  in
          mkQuant r true uu____5086
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5158  ->
      match uu____5158 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5217  ->
      match uu____5217 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5292  ->
      match uu____5292 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5355  ->
      match uu____5355 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5406  ->
    fun r  ->
      match uu____5406 with
      | (bindings,body) ->
          let uu____5432 = FStar_List.split bindings  in
          (match uu____5432 with
           | (vars,es) ->
               let uu____5451 =
                 let uu____5458 = abstr vars body  in (es, uu____5458)  in
               mkLet uu____5451 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5480  ->
    match uu____5480 with
    | (nm,vars,s,tm,c) ->
        let uu____5505 =
          let uu____5519 = FStar_List.map fv_sort vars  in
          let uu____5523 = abstr vars tm  in
          (nm, uu____5519, s, uu____5523, c)  in
        DefineFun uu____5505
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5534 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5534
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5552  ->
    fun id1  ->
      match uu____5552 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5568 =
              let uu____5569 =
                let uu____5574 = mkInteger' id1 norng  in
                let uu____5575 =
                  let uu____5576 =
                    let uu____5584 = constr_id_of_sort sort  in
                    let uu____5586 =
                      let uu____5589 = mkApp (tok_name, []) norng  in
                      [uu____5589]  in
                    (uu____5584, uu____5586)  in
                  mkApp uu____5576 norng  in
                (uu____5574, uu____5575)  in
              mkEq uu____5569 norng  in
            let uu____5596 = escape a_name  in
            {
              assumption_term = uu____5568;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5596;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5622  ->
      match uu____5622 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5662 =
                        let uu____5668 =
                          let uu____5670 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____5670  in
                        (uu____5668, s)  in
                      mkFreeV uu____5662 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____5692 =
              let uu____5700 = constr_id_of_sort sort  in
              (uu____5700, [capp])  in
            mkApp uu____5692 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____5709 =
              let uu____5710 =
                let uu____5721 =
                  let uu____5722 =
                    let uu____5727 = mkInteger id2 norng  in
                    (uu____5727, cid_app)  in
                  mkEq uu____5722 norng  in
                ([[capp]], bvar_names, uu____5721)  in
              mkForall rng uu____5710  in
            let uu____5736 = escape a_name  in
            {
              assumption_term = uu____5709;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____5736;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decls_t)
  =
  fun rng  ->
    fun uu____5759  ->
      match uu____5759 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____5788 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____5788  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____5823 = let uu____5829 = bvar_name i  in (uu____5829, s)
               in
            mkFreeV uu____5823  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____5862  ->
                      match uu____5862 with
                      | (uu____5872,s,uu____5874) ->
                          let uu____5879 = bvar i s  in uu____5879 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____5901 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____5939  ->
                      match uu____5939 with
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
                              let uu____5972 =
                                let uu____5973 =
                                  let uu____5984 =
                                    let uu____5985 =
                                      let uu____5990 =
                                        let uu____5991 = bvar i s  in
                                        uu____5991 norng  in
                                      (cproj_app, uu____5990)  in
                                    mkEq uu____5985 norng  in
                                  ([[capp]], bvar_names, uu____5984)  in
                                mkForall rng uu____5973  in
                              let uu____6004 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____5972;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6004;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____5901 FStar_List.flatten
  
let (constructor_to_decl : FStar_Range.range -> constructor_t -> decls_t) =
  fun rng  ->
    fun uu____6025  ->
      match uu____6025 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6071  ->
                    match uu____6071 with
                    | (uu____6080,sort1,uu____6082) -> sort1))
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
              let uu____6112 =
                let uu____6117 =
                  let uu____6118 =
                    let uu____6126 = constr_id_of_sort sort  in
                    (uu____6126, [xx])  in
                  mkApp uu____6118 norng  in
                let uu____6131 =
                  let uu____6132 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6132 norng  in
                (uu____6117, uu____6131)  in
              mkEq uu____6112 norng  in
            let uu____6134 =
              let uu____6150 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6213  ->
                          match uu____6213 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6253 = mkApp (proj, [xx]) norng  in
                                (uu____6253, [])
                              else
                                (let fi =
                                   let uu____6277 =
                                     let uu____6279 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____6279  in
                                   (uu____6277, s)  in
                                 let uu____6283 = mkFreeV fi norng  in
                                 (uu____6283, [fi]))))
                 in
              FStar_All.pipe_right uu____6150 FStar_List.split  in
            match uu____6134 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6374 =
                    let uu____6379 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6379)  in
                  mkEq uu____6374 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6389 ->
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
          let uu____6421 =
            let uu____6424 =
              let uu____6425 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6425  in
            uu____6424 :: cdecl :: cid :: projs  in
          let uu____6428 =
            let uu____6431 =
              let uu____6434 =
                let uu____6435 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6435  in
              [uu____6434]  in
            FStar_List.append [disc] uu____6431  in
          FStar_List.append uu____6421 uu____6428
  
let (name_binders_inner :
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string * sort) Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string * sort) Prims.list * Prims.string Prims.list *
            Prims.int))
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____6502 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6566  ->
                    fun s  ->
                      match uu____6566 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6631 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6642 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6642  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____6660 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6660  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6502 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list))
  =
  fun sorts  ->
    let uu____6766 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____6766 with
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
              (let uu____6965 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____6965)
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
                               "Prims.guard_free",{ tm = BoundV uu____7011;
                                                    freevars = uu____7012;
                                                    rng = uu____7013;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7031 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____7107 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7107 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7136 = op_to_string op  in
              let uu____7138 =
                let uu____7140 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7140 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7136 uu____7138
          | Labeled (t2,uu____7152,uu____7153) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7160 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7160 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7188 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7188 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7256 ->
                         let uu____7261 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7280 =
                                     let uu____7282 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7290 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7290) pats2
                                        in
                                     FStar_String.concat " " uu____7282  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7280))
                            in
                         FStar_All.pipe_right uu____7261
                           (FStar_String.concat "\n")
                      in
                   let uu____7300 =
                     let uu____7304 =
                       let uu____7308 =
                         let uu____7312 = aux1 n2 names2 body  in
                         let uu____7314 =
                           let uu____7318 = weightToSmt wopt  in
                           [uu____7318; pats_str; qid]  in
                         uu____7312 :: uu____7314  in
                       binders1 :: uu____7308  in
                     (qop_to_string qop) :: uu____7304  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7300)
          | Let (es,body) ->
              let uu____7334 =
                FStar_List.fold_left
                  (fun uu____7377  ->
                     fun e  ->
                       match uu____7377 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7440 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7440  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____7459 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7459  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7334 with
               | (names2,binders,n2) ->
                   let uu____7513 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7513)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7529 = FStar_Range.string_of_range t1.rng  in
            let uu____7531 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7529
              uu____7531 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___154_7553  ->
      match uu___154_7553 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7564 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7564 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7586 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7661 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7661 (FStar_String.concat "\n")  in
            let uu____7671 = FStar_Options.keep_query_captions ()  in
            if uu____7671
            then
              let uu____7675 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7677 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7675 uu____7677
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7686 =
                let uu____7688 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7688 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7686
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____7729 = caption_to_string print_captions c  in
            let uu____7731 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____7729 f
              (FStar_String.concat " " l) uu____7731
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____7746 = name_macro_binders arg_sorts  in
            (match uu____7746 with
             | (names1,binders) ->
                 let body1 =
                   let uu____7785 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____7785 body  in
                 let uu____7800 = caption_to_string print_captions c  in
                 let uu____7802 = strSort retsort  in
                 let uu____7804 =
                   let uu____7806 = escape f  in
                   termToSmt print_captions uu____7806 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____7800 f (FStar_String.concat " " binders) uu____7802
                   uu____7804)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___155_7833  ->
                      match uu___155_7833 with
                      | Name n1 ->
                          let uu____7836 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____7836
                      | Namespace ns ->
                          let uu____7840 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____7840
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____7850 =
                  let uu____7852 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____7852  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____7850
              else ""  in
            let n1 = a.assumption_name  in
            let uu____7863 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____7865 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____7863
              fids uu____7865 n1
        | Eval t ->
            let uu____7869 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____7869
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____7876 -> ""
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
      let uu____7897 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____7897 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____7908 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____7908 (FStar_String.concat "\n")

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
      let uu____8028 =
        let uu____8032 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8032
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8028 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decls_t) =
  fun sz  ->
    let uu____8061 =
      let uu____8062 =
        let uu____8064 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8064  in
      let uu____8073 =
        let uu____8076 =
          let uu____8077 =
            let uu____8079 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8079  in
          (uu____8077, (BitVec_sort sz), true)  in
        [uu____8076]  in
      (uu____8062, uu____8073, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8061 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8120  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8145 =
       let uu____8147 = FStar_ST.op_Bang __range_c  in
       uu____8147 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8145);
    (let uu____8192 =
       let uu____8200 = let uu____8203 = mkInteger' i norng  in [uu____8203]
          in
       ("Range_const", uu____8200)  in
     mkApp uu____8192 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8246 =
        let uu____8254 = let uu____8257 = mkInteger' i norng  in [uu____8257]
           in
        ("Tm_uvar", uu____8254)  in
      mkApp uu____8246 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8300 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8324 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8324 u v1 t
  
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
      let uu____8399 =
        let uu____8401 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8401  in
      let uu____8410 =
        let uu____8412 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8412  in
      elim_box true uu____8399 uu____8410 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8435 =
        let uu____8437 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8437  in
      let uu____8446 =
        let uu____8448 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8448  in
      elim_box true uu____8435 uu____8446 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____8471 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____8485 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8511 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8511
         | uu____8514 -> FStar_Pervasives_Native.None)
    | uu____8516 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8534::t1::t2::[]);
                       freevars = uu____8537; rng = uu____8538;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8554::t1::t2::[]);
                       freevars = uu____8557; rng = uu____8558;_}::[])
        -> let uu____8574 = mkEq (t1, t2) norng  in mkNot uu____8574 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8577; rng = uu____8578;_}::[])
        ->
        let uu____8594 =
          let uu____8599 = unboxInt t1  in
          let uu____8600 = unboxInt t2  in (uu____8599, uu____8600)  in
        mkLTE uu____8594 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8603; rng = uu____8604;_}::[])
        ->
        let uu____8620 =
          let uu____8625 = unboxInt t1  in
          let uu____8626 = unboxInt t2  in (uu____8625, uu____8626)  in
        mkLT uu____8620 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8629; rng = uu____8630;_}::[])
        ->
        let uu____8646 =
          let uu____8651 = unboxInt t1  in
          let uu____8652 = unboxInt t2  in (uu____8651, uu____8652)  in
        mkGTE uu____8646 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8655; rng = uu____8656;_}::[])
        ->
        let uu____8672 =
          let uu____8677 = unboxInt t1  in
          let uu____8678 = unboxInt t2  in (uu____8677, uu____8678)  in
        mkGT uu____8672 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8681; rng = uu____8682;_}::[])
        ->
        let uu____8698 =
          let uu____8703 = unboxBool t1  in
          let uu____8704 = unboxBool t2  in (uu____8703, uu____8704)  in
        mkAnd uu____8698 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____8707; rng = uu____8708;_}::[])
        ->
        let uu____8724 =
          let uu____8729 = unboxBool t1  in
          let uu____8730 = unboxBool t2  in (uu____8729, uu____8730)  in
        mkOr uu____8724 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____8732; rng = uu____8733;_}::[])
        -> let uu____8749 = unboxBool t1  in mkNot uu____8749 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____8753; rng = uu____8754;_}::[])
        when
        let uu____8770 = getBoxedInteger t0  in FStar_Util.is_some uu____8770
        ->
        let sz =
          let uu____8777 = getBoxedInteger t0  in
          match uu____8777 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____8785 -> failwith "impossible"  in
        let uu____8791 =
          let uu____8796 = unboxBitVec sz t1  in
          let uu____8797 = unboxBitVec sz t2  in (uu____8796, uu____8797)  in
        mkBvUlt uu____8791 t.rng
    | App
        (Var
         "Prims.equals",uu____8798::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____8802;
                                      rng = uu____8803;_}::uu____8804::[])
        when
        let uu____8820 = getBoxedInteger t0  in FStar_Util.is_some uu____8820
        ->
        let sz =
          let uu____8827 = getBoxedInteger t0  in
          match uu____8827 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____8835 -> failwith "impossible"  in
        let uu____8841 =
          let uu____8846 = unboxBitVec sz t1  in
          let uu____8847 = unboxBitVec sz t2  in (uu____8846, uu____8847)  in
        mkBvUlt uu____8841 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___156_8852 = unboxBool t1  in
        {
          tm = (uu___156_8852.tm);
          freevars = (uu___156_8852.freevars);
          rng = (t.rng)
        }
    | uu____8853 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____8914 = FStar_Options.unthrottle_inductives ()  in
        if uu____8914
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
    let uu____9047 =
      let uu____9048 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9048 t t.rng  in
    FStar_All.pipe_right uu____9047 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9066 =
        let uu____9074 = let uu____9077 = mkInteger' i norng  in [uu____9077]
           in
        ("FString_const", uu____9074)  in
      mkApp uu____9066 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9108 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9108 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9155 =
         let uu____9163 =
           let uu____9166 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9166]  in
         ("SFuel", uu____9163)  in
       mkApp uu____9155 norng)
  
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
            let uu____9214 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9214
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
      let uu____9277 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9277
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9297 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9297
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9308 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9308
  