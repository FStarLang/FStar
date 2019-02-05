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
  
type decls_elt =
  {
  sym_name: Prims.string FStar_Pervasives_Native.option ;
  key: Prims.string FStar_Pervasives_Native.option ;
  decls: decl Prims.list ;
  a_names: Prims.string Prims.list }
let (__proj__Mkdecls_elt__item__sym_name :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { sym_name; key; decls; a_names;_} -> sym_name
  
let (__proj__Mkdecls_elt__item__key :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { sym_name; key; decls; a_names;_} -> key
  
let (__proj__Mkdecls_elt__item__decls : decls_elt -> decl Prims.list) =
  fun projectee  ->
    match projectee with | { sym_name; key; decls; a_names;_} -> decls
  
let (__proj__Mkdecls_elt__item__a_names :
  decls_elt -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with | { sym_name; key; decls; a_names;_} -> a_names
  
type decls_t = decls_elt Prims.list
let (mk_decls :
  Prims.string ->
    Prims.string -> decl Prims.list -> decls_elt Prims.list -> decls_elt)
  =
  fun name  ->
    fun key  ->
      fun decls  ->
        fun aux_decls  ->
          let uu____2195 =
            let uu____2199 =
              FStar_List.collect (fun elt  -> elt.a_names) aux_decls  in
            let uu____2206 =
              FStar_List.collect
                (fun uu___121_2213  ->
                   match uu___121_2213 with
                   | Assume a -> [a.assumption_name]
                   | uu____2220 -> []) decls
               in
            FStar_List.append uu____2199 uu____2206  in
          {
            sym_name = (FStar_Pervasives_Native.Some name);
            key = (FStar_Pervasives_Native.Some key);
            decls;
            a_names = uu____2195
          }
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2235 =
      let uu____2236 =
        FStar_List.collect
          (fun uu___122_2243  ->
             match uu___122_2243 with
             | Assume a -> [a.assumption_name]
             | uu____2250 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2236
      }  in
    [uu____2235]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
  
let fv_sort :
  'Auu____2299 'Auu____2300 . ('Auu____2299 * 'Auu____2300) -> 'Auu____2300 =
  fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2339 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___123_2350  ->
    match uu___123_2350 with
    | { tm = FreeV x; freevars = uu____2352; rng = uu____2353;_} -> fv_sort x
    | uu____2369 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___124_2376  ->
    match uu___124_2376 with
    | { tm = FreeV fv; freevars = uu____2378; rng = uu____2379;_} -> fv
    | uu____2394 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2416 -> []
    | BoundV uu____2423 -> []
    | FreeV fv -> [fv]
    | App (uu____2446,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2457,uu____2458,uu____2459,uu____2460,t1) -> freevars t1
    | Labeled (t1,uu____2481,uu____2482) -> freevars t1
    | LblPos (t1,uu____2486) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2506 = FStar_ST.op_Bang t.freevars  in
    match uu____2506 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2583 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2583  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___125_2647  ->
    match uu___125_2647 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___126_2657  ->
    match uu___126_2657 with
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
        let uu____2692 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2692
    | NatToBv n1 ->
        let uu____2697 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2697
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___127_2711  ->
    match uu___127_2711 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2721 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2721
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____2741 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2741
    | FreeV x ->
        let uu____2750 =
          let uu____2752 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____2752  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____2750
    | App (op,tms) ->
        let uu____2763 =
          let uu____2765 = op_to_string op  in
          let uu____2767 =
            let uu____2769 =
              let uu____2771 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2771 (FStar_String.concat " ")  in
            Prims.strcat uu____2769 ")"  in
          Prims.strcat uu____2765 uu____2767  in
        Prims.strcat "(" uu____2763
    | Labeled (t1,r1,r2) ->
        let uu____2788 = hash_of_term t1  in
        let uu____2790 =
          let uu____2792 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2792  in
        Prims.strcat uu____2788 uu____2790
    | LblPos (t1,r) ->
        let uu____2798 =
          let uu____2800 = hash_of_term t1  in
          Prims.strcat uu____2800
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2798
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2828 =
          let uu____2830 =
            let uu____2832 =
              let uu____2834 =
                let uu____2836 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2836 (FStar_String.concat " ")  in
              let uu____2846 =
                let uu____2848 =
                  let uu____2850 = hash_of_term body  in
                  let uu____2852 =
                    let uu____2854 =
                      let uu____2856 = weightToSmt wopt  in
                      let uu____2858 =
                        let uu____2860 =
                          let uu____2862 =
                            let uu____2864 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2883 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2883
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2864
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2862 "))"  in
                        Prims.strcat " " uu____2860  in
                      Prims.strcat uu____2856 uu____2858  in
                    Prims.strcat " " uu____2854  in
                  Prims.strcat uu____2850 uu____2852  in
                Prims.strcat ")(! " uu____2848  in
              Prims.strcat uu____2834 uu____2846  in
            Prims.strcat " (" uu____2832  in
          Prims.strcat (qop_to_string qop) uu____2830  in
        Prims.strcat "(" uu____2828
    | Let (es,body) ->
        let uu____2910 =
          let uu____2912 =
            let uu____2914 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2914 (FStar_String.concat " ")  in
          let uu____2924 =
            let uu____2926 =
              let uu____2928 = hash_of_term body  in
              Prims.strcat uu____2928 ")"  in
            Prims.strcat ") " uu____2926  in
          Prims.strcat uu____2912 uu____2924  in
        Prims.strcat "(let (" uu____2910

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____2989 =
      let uu____2991 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____2991  in
    mkBoxFunctions uu____2989
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3008 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3008 = "Box") &&
        (let uu____3015 =
           let uu____3017 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3017  in
         Prims.op_Negation uu____3015)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3041 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3041; rng = r }
  
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
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3209  ->
    fun r  -> match uu____3209 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3239) -> mkFalse r
      | App (FalseOp ,uu____3244) -> mkTrue r
      | uu____3249 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3265  ->
    fun r  ->
      match uu____3265 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3273),uu____3274) -> t2
           | (uu____3279,App (TrueOp ,uu____3280)) -> t1
           | (App (FalseOp ,uu____3285),uu____3286) -> mkFalse r
           | (uu____3291,App (FalseOp ,uu____3292)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3309,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3318) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3325 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3345  ->
    fun r  ->
      match uu____3345 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3353),uu____3354) -> mkTrue r
           | (uu____3359,App (TrueOp ,uu____3360)) -> mkTrue r
           | (App (FalseOp ,uu____3365),uu____3366) -> t2
           | (uu____3371,App (FalseOp ,uu____3372)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3389,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3398) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3405 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3425  ->
    fun r  ->
      match uu____3425 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3433,App (TrueOp ,uu____3434)) -> mkTrue r
           | (App (FalseOp ,uu____3439),uu____3440) -> mkTrue r
           | (App (TrueOp ,uu____3445),uu____3446) -> t2
           | (uu____3451,App (Imp ,t1'::t2'::[])) ->
               let uu____3456 =
                 let uu____3463 =
                   let uu____3466 = mkAnd (t1, t1') r  in [uu____3466; t2']
                    in
                 (Imp, uu____3463)  in
               mkApp' uu____3456 r
           | uu____3469 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3494  ->
      fun r  -> match uu____3494 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3654  ->
      fun r  ->
        match uu____3654 with
        | (t1,t2) ->
            let uu____3663 =
              let uu____3670 =
                let uu____3673 =
                  let uu____3676 = mkNatToBv sz t2 r  in [uu____3676]  in
                t1 :: uu____3673  in
              (BvShl, uu____3670)  in
            mkApp' uu____3663 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3698  ->
      fun r  ->
        match uu____3698 with
        | (t1,t2) ->
            let uu____3707 =
              let uu____3714 =
                let uu____3717 =
                  let uu____3720 = mkNatToBv sz t2 r  in [uu____3720]  in
                t1 :: uu____3717  in
              (BvShr, uu____3714)  in
            mkApp' uu____3707 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3742  ->
      fun r  ->
        match uu____3742 with
        | (t1,t2) ->
            let uu____3751 =
              let uu____3758 =
                let uu____3761 =
                  let uu____3764 = mkNatToBv sz t2 r  in [uu____3764]  in
                t1 :: uu____3761  in
              (BvUdiv, uu____3758)  in
            mkApp' uu____3751 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3786  ->
      fun r  ->
        match uu____3786 with
        | (t1,t2) ->
            let uu____3795 =
              let uu____3802 =
                let uu____3805 =
                  let uu____3808 = mkNatToBv sz t2 r  in [uu____3808]  in
                t1 :: uu____3805  in
              (BvMod, uu____3802)  in
            mkApp' uu____3795 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3830  ->
      fun r  ->
        match uu____3830 with
        | (t1,t2) ->
            let uu____3839 =
              let uu____3846 =
                let uu____3849 =
                  let uu____3852 = mkNatToBv sz t2 r  in [uu____3852]  in
                t1 :: uu____3849  in
              (BvMul, uu____3846)  in
            mkApp' uu____3839 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3894  ->
    fun r  ->
      match uu____3894 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3913 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4050  ->
    fun r  ->
      match uu____4050 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4061) -> t2
           | App (FalseOp ,uu____4066) -> t3
           | uu____4071 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4072),App (TrueOp ,uu____4073)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4082),uu____4083) ->
                    let uu____4088 =
                      let uu____4093 = mkNot t1 t1.rng  in (uu____4093, t3)
                       in
                    mkImp uu____4088 r
                | (uu____4094,App (TrueOp ,uu____4095)) -> mkImp (t1, t2) r
                | (uu____4100,uu____4101) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4157 -> FStar_Pervasives_Native.None
      | BoundV uu____4159 -> FStar_Pervasives_Native.None
      | FreeV uu____4161 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4182 -> true
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
            | BvUext uu____4214 -> false
            | NatToBv uu____4217 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4228,uu____4229) -> aux t2
      | Quant uu____4232 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4252 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4267 = aux t1  in
          (match uu____4267 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4302 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4302
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4319 = op_to_string op  in
        let uu____4321 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4319 uu____4321
    | Labeled (t1,r1,r2) ->
        let uu____4329 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4329
    | LblPos (t1,s) ->
        let uu____4336 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4336
    | Quant (qop,l,uu____4341,uu____4342,t1) ->
        let uu____4362 = print_smt_term_list_list l  in
        let uu____4364 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4362
          uu____4364
    | Let (es,body) ->
        let uu____4373 = print_smt_term_list es  in
        let uu____4375 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4373 uu____4375

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4382 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4382 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4409 =
             let uu____4411 =
               let uu____4413 = print_smt_term_list l1  in
               Prims.strcat uu____4413 " ] "  in
             Prims.strcat "; [ " uu____4411  in
           Prims.strcat s uu____4409) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4453  ->
        match uu____4453 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4522 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4522 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4537 =
                         let uu____4543 =
                           let uu____4545 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4545
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4543)
                          in
                       FStar_Errors.log_issue r uu____4537);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4556) -> body
               | uu____4561 ->
                   let uu____4562 =
                     let uu____4563 =
                       let uu____4583 = all_pats_ok pats  in
                       (qop, uu____4583, wopt, vars, body)  in
                     Quant uu____4563  in
                   mk uu____4562 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4612  ->
    fun r  ->
      match uu____4612 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4658 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4658 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4691 = FStar_ST.op_Bang t1.freevars  in
        match uu____4691 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4750 ->
            (match t1.tm with
             | Integer uu____4760 -> t1
             | BoundV uu____4762 -> t1
             | FreeV x ->
                 let uu____4770 = index_of1 x  in
                 (match uu____4770 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4784 =
                   let uu____4791 = FStar_List.map (aux ix) tms  in
                   (op, uu____4791)  in
                 mkApp' uu____4784 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4801 =
                   let uu____4802 =
                     let uu____4810 = aux ix t2  in (uu____4810, r1, r2)  in
                   Labeled uu____4802  in
                 mk uu____4801 t2.rng
             | LblPos (t2,r) ->
                 let uu____4816 =
                   let uu____4817 =
                     let uu____4823 = aux ix t2  in (uu____4823, r)  in
                   LblPos uu____4817  in
                 mk uu____4816 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4849 =
                   let uu____4869 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4890 = aux (ix + n1) body  in
                   (qop, uu____4869, wopt, vars, uu____4890)  in
                 mkQuant t1.rng false uu____4849
             | Let (es,body) ->
                 let uu____4911 =
                   FStar_List.fold_left
                     (fun uu____4931  ->
                        fun e  ->
                          match uu____4931 with
                          | (ix1,l) ->
                              let uu____4955 =
                                let uu____4958 = aux ix1 e  in uu____4958 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____4955))
                     (ix, []) es
                    in
                 (match uu____4911 with
                  | (ix1,es_rev) ->
                      let uu____4974 =
                        let uu____4981 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____4981)  in
                      mkLet uu____4974 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5017 -> t1
        | FreeV uu____5019 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5041 =
              let uu____5048 = FStar_List.map (aux shift) tms2  in
              (op, uu____5048)  in
            mkApp' uu____5041 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5058 =
              let uu____5059 =
                let uu____5067 = aux shift t2  in (uu____5067, r1, r2)  in
              Labeled uu____5059  in
            mk uu____5058 t2.rng
        | LblPos (t2,r) ->
            let uu____5073 =
              let uu____5074 =
                let uu____5080 = aux shift t2  in (uu____5080, r)  in
              LblPos uu____5074  in
            mk uu____5073 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5112 =
              let uu____5132 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5149 = aux shift1 body  in
              (qop, uu____5132, wopt, vars, uu____5149)  in
            mkQuant t1.rng false uu____5112
        | Let (es,body) ->
            let uu____5166 =
              FStar_List.fold_left
                (fun uu____5186  ->
                   fun e  ->
                     match uu____5186 with
                     | (ix,es1) ->
                         let uu____5210 =
                           let uu____5213 = aux shift e  in uu____5213 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5210))
                (shift, []) es
               in
            (match uu____5166 with
             | (shift1,es_rev) ->
                 let uu____5229 =
                   let uu____5236 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5236)  in
                 mkLet uu____5229 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5256 = abstr [fv] t  in inst [s] uu____5256
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5286  ->
      match uu____5286 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5329 =
            let uu____5349 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5366 = FStar_List.map fv_sort vars  in
            let uu____5370 = abstr vars body  in
            (qop, uu____5349, wopt, uu____5366, uu____5370)  in
          mkQuant r true uu____5329
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5401  ->
      match uu____5401 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5460  ->
      match uu____5460 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5535  ->
      match uu____5535 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5598  ->
      match uu____5598 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5649  ->
    fun r  ->
      match uu____5649 with
      | (bindings,body) ->
          let uu____5675 = FStar_List.split bindings  in
          (match uu____5675 with
           | (vars,es) ->
               let uu____5694 =
                 let uu____5701 = abstr vars body  in (es, uu____5701)  in
               mkLet uu____5694 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)
    -> decl)
  =
  fun uu____5728  ->
    match uu____5728 with
    | (nm,vars,s,tm,c) ->
        let uu____5768 =
          let uu____5782 = FStar_List.map fv_sort vars  in
          let uu____5791 = abstr vars tm  in
          (nm, uu____5782, s, uu____5791, c)  in
        DefineFun uu____5768
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5802 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5802
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5820  ->
    fun id1  ->
      match uu____5820 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5836 =
              let uu____5837 =
                let uu____5842 = mkInteger' id1 norng  in
                let uu____5843 =
                  let uu____5844 =
                    let uu____5852 = constr_id_of_sort sort  in
                    let uu____5854 =
                      let uu____5857 = mkApp (tok_name, []) norng  in
                      [uu____5857]  in
                    (uu____5852, uu____5854)  in
                  mkApp uu____5844 norng  in
                (uu____5842, uu____5843)  in
              mkEq uu____5837 norng  in
            let uu____5864 = escape a_name  in
            {
              assumption_term = uu____5836;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5864;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5890  ->
      match uu____5890 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5930 =
                        let uu____5936 =
                          let uu____5938 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____5938  in
                        (uu____5936, s)  in
                      mkFreeV uu____5930 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____5960 =
              let uu____5968 = constr_id_of_sort sort  in
              (uu____5968, [capp])  in
            mkApp uu____5960 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____5977 =
              let uu____5978 =
                let uu____5989 =
                  let uu____5990 =
                    let uu____5995 = mkInteger id2 norng  in
                    (uu____5995, cid_app)  in
                  mkEq uu____5990 norng  in
                ([[capp]], bvar_names, uu____5989)  in
              mkForall rng uu____5978  in
            let uu____6004 = escape a_name  in
            {
              assumption_term = uu____5977;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6004;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6029  ->
      match uu____6029 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6062 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6062  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6097 = let uu____6103 = bvar_name i  in (uu____6103, s)
               in
            mkFreeV uu____6097  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6136  ->
                      match uu____6136 with
                      | (uu____6146,s,uu____6148) ->
                          let uu____6153 = bvar i s  in uu____6153 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6175 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6213  ->
                      match uu____6213 with
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
                              let uu____6246 =
                                let uu____6247 =
                                  let uu____6258 =
                                    let uu____6259 =
                                      let uu____6264 =
                                        let uu____6265 = bvar i s  in
                                        uu____6265 norng  in
                                      (cproj_app, uu____6264)  in
                                    mkEq uu____6259 norng  in
                                  ([[capp]], bvar_names, uu____6258)  in
                                mkForall rng uu____6247  in
                              let uu____6278 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6246;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6278;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6175 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6303  ->
      match uu____6303 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6351  ->
                    match uu____6351 with
                    | (uu____6360,sort1,uu____6362) -> sort1))
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
              let uu____6392 =
                let uu____6397 =
                  let uu____6398 =
                    let uu____6406 = constr_id_of_sort sort  in
                    (uu____6406, [xx])  in
                  mkApp uu____6398 norng  in
                let uu____6411 =
                  let uu____6412 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6412 norng  in
                (uu____6397, uu____6411)  in
              mkEq uu____6392 norng  in
            let uu____6414 =
              let uu____6430 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6493  ->
                          match uu____6493 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6533 = mkApp (proj, [xx]) norng  in
                                (uu____6533, [])
                              else
                                (let fi =
                                   let uu____6557 =
                                     let uu____6559 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____6559  in
                                   (uu____6557, s)  in
                                 let uu____6563 = mkFreeV fi norng  in
                                 (uu____6563, [fi]))))
                 in
              FStar_All.pipe_right uu____6430 FStar_List.split  in
            match uu____6414 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6654 =
                    let uu____6659 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6659)  in
                  mkEq uu____6654 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6669 ->
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
          let uu____6716 =
            let uu____6719 =
              let uu____6720 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6720  in
            uu____6719 :: cdecl :: cid :: projs  in
          let uu____6723 =
            let uu____6726 =
              let uu____6729 =
                let uu____6730 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6730  in
              [uu____6729]  in
            FStar_List.append [disc] uu____6726  in
          FStar_List.append uu____6716 uu____6723
  
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
          let uu____6797 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6861  ->
                    fun s  ->
                      match uu____6861 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6926 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6937 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6937  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____6955 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6955  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6797 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list))
  =
  fun sorts  ->
    let uu____7061 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7061 with
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
              (let uu____7260 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7260)
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
                               "Prims.guard_free",{ tm = BoundV uu____7306;
                                                    freevars = uu____7307;
                                                    rng = uu____7308;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7326 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____7402 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7402 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7431 = op_to_string op  in
              let uu____7433 =
                let uu____7435 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7435 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7431 uu____7433
          | Labeled (t2,uu____7447,uu____7448) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7455 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7455 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7483 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7483 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7551 ->
                         let uu____7556 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7575 =
                                     let uu____7577 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7585 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7585) pats2
                                        in
                                     FStar_String.concat " " uu____7577  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7575))
                            in
                         FStar_All.pipe_right uu____7556
                           (FStar_String.concat "\n")
                      in
                   let uu____7595 =
                     let uu____7599 =
                       let uu____7603 =
                         let uu____7607 = aux1 n2 names2 body  in
                         let uu____7609 =
                           let uu____7613 = weightToSmt wopt  in
                           [uu____7613; pats_str; qid]  in
                         uu____7607 :: uu____7609  in
                       binders1 :: uu____7603  in
                     (qop_to_string qop) :: uu____7599  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7595)
          | Let (es,body) ->
              let uu____7629 =
                FStar_List.fold_left
                  (fun uu____7672  ->
                     fun e  ->
                       match uu____7672 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7735 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7735  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____7754 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7754  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7629 with
               | (names2,binders,n2) ->
                   let uu____7808 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7808)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7824 = FStar_Range.string_of_range t1.rng  in
            let uu____7826 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7824
              uu____7826 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___128_7848  ->
      match uu___128_7848 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7859 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7859 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7881 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7956 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7956 (FStar_String.concat "\n")  in
            let uu____7966 = FStar_Options.keep_query_captions ()  in
            if uu____7966
            then
              let uu____7970 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7972 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7970 uu____7972
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7981 =
                let uu____7983 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7983 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7981
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8024 = caption_to_string print_captions c  in
            let uu____8026 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8024 f
              (FStar_String.concat " " l) uu____8026
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8041 = name_macro_binders arg_sorts  in
            (match uu____8041 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8080 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8080 body  in
                 let uu____8095 = caption_to_string print_captions c  in
                 let uu____8097 = strSort retsort  in
                 let uu____8099 =
                   let uu____8101 = escape f  in
                   termToSmt print_captions uu____8101 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8095 f (FStar_String.concat " " binders) uu____8097
                   uu____8099)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___129_8128  ->
                      match uu___129_8128 with
                      | Name n1 ->
                          let uu____8131 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____8131
                      | Namespace ns ->
                          let uu____8135 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____8135
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8145 =
                  let uu____8147 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8147  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8145
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8158 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8160 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8158
              fids uu____8160 n1
        | Eval t ->
            let uu____8164 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8164
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8171 -> ""
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
      let uu____8192 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8192 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8203 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8203 (FStar_String.concat "\n")

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
      let uu____8323 =
        let uu____8327 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8327
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8323 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8358 =
      let uu____8359 =
        let uu____8361 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8361  in
      let uu____8370 =
        let uu____8373 =
          let uu____8374 =
            let uu____8376 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8376  in
          (uu____8374, (BitVec_sort sz), true)  in
        [uu____8373]  in
      (uu____8359, uu____8370, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8358 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8419  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8444 =
       let uu____8446 = FStar_ST.op_Bang __range_c  in
       uu____8446 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8444);
    (let uu____8491 =
       let uu____8499 = let uu____8502 = mkInteger' i norng  in [uu____8502]
          in
       ("Range_const", uu____8499)  in
     mkApp uu____8491 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8545 =
        let uu____8553 = let uu____8556 = mkInteger' i norng  in [uu____8556]
           in
        ("Tm_uvar", uu____8553)  in
      mkApp uu____8545 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8599 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8623 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8623 u v1 t
  
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
      let uu____8698 =
        let uu____8700 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8700  in
      let uu____8709 =
        let uu____8711 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8711  in
      elim_box true uu____8698 uu____8709 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8734 =
        let uu____8736 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8736  in
      let uu____8745 =
        let uu____8747 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8747  in
      elim_box true uu____8734 uu____8745 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____8770 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____8784 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8810 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8810
         | uu____8813 -> FStar_Pervasives_Native.None)
    | uu____8815 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8833::t1::t2::[]);
                       freevars = uu____8836; rng = uu____8837;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8853::t1::t2::[]);
                       freevars = uu____8856; rng = uu____8857;_}::[])
        -> let uu____8873 = mkEq (t1, t2) norng  in mkNot uu____8873 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8876; rng = uu____8877;_}::[])
        ->
        let uu____8893 =
          let uu____8898 = unboxInt t1  in
          let uu____8899 = unboxInt t2  in (uu____8898, uu____8899)  in
        mkLTE uu____8893 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8902; rng = uu____8903;_}::[])
        ->
        let uu____8919 =
          let uu____8924 = unboxInt t1  in
          let uu____8925 = unboxInt t2  in (uu____8924, uu____8925)  in
        mkLT uu____8919 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8928; rng = uu____8929;_}::[])
        ->
        let uu____8945 =
          let uu____8950 = unboxInt t1  in
          let uu____8951 = unboxInt t2  in (uu____8950, uu____8951)  in
        mkGTE uu____8945 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8954; rng = uu____8955;_}::[])
        ->
        let uu____8971 =
          let uu____8976 = unboxInt t1  in
          let uu____8977 = unboxInt t2  in (uu____8976, uu____8977)  in
        mkGT uu____8971 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8980; rng = uu____8981;_}::[])
        ->
        let uu____8997 =
          let uu____9002 = unboxBool t1  in
          let uu____9003 = unboxBool t2  in (uu____9002, uu____9003)  in
        mkAnd uu____8997 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9006; rng = uu____9007;_}::[])
        ->
        let uu____9023 =
          let uu____9028 = unboxBool t1  in
          let uu____9029 = unboxBool t2  in (uu____9028, uu____9029)  in
        mkOr uu____9023 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9031; rng = uu____9032;_}::[])
        -> let uu____9048 = unboxBool t1  in mkNot uu____9048 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9052; rng = uu____9053;_}::[])
        when
        let uu____9069 = getBoxedInteger t0  in FStar_Util.is_some uu____9069
        ->
        let sz =
          let uu____9076 = getBoxedInteger t0  in
          match uu____9076 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9084 -> failwith "impossible"  in
        let uu____9090 =
          let uu____9095 = unboxBitVec sz t1  in
          let uu____9096 = unboxBitVec sz t2  in (uu____9095, uu____9096)  in
        mkBvUlt uu____9090 t.rng
    | App
        (Var
         "Prims.equals",uu____9097::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9101;
                                      rng = uu____9102;_}::uu____9103::[])
        when
        let uu____9119 = getBoxedInteger t0  in FStar_Util.is_some uu____9119
        ->
        let sz =
          let uu____9126 = getBoxedInteger t0  in
          match uu____9126 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9134 -> failwith "impossible"  in
        let uu____9140 =
          let uu____9145 = unboxBitVec sz t1  in
          let uu____9146 = unboxBitVec sz t2  in (uu____9145, uu____9146)  in
        mkBvUlt uu____9140 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___130_9151 = unboxBool t1  in
        {
          tm = (uu___130_9151.tm);
          freevars = (uu___130_9151.freevars);
          rng = (t.rng)
        }
    | uu____9152 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9213 = FStar_Options.unthrottle_inductives ()  in
        if uu____9213
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
    let uu____9346 =
      let uu____9347 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9347 t t.rng  in
    FStar_All.pipe_right uu____9346 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9365 =
        let uu____9373 = let uu____9376 = mkInteger' i norng  in [uu____9376]
           in
        ("FString_const", uu____9373)  in
      mkApp uu____9365 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9407 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9407 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9454 =
         let uu____9462 =
           let uu____9465 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9465]  in
         ("SFuel", uu____9462)  in
       mkApp uu____9454 norng)
  
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
            let uu____9513 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9513
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
      let uu____9576 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9576
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9596 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9596
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9607 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9607
  