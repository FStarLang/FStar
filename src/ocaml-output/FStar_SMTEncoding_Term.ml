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
  a_names: Prims.string Prims.list ;
  aux_decls: decls_elt Prims.list }
let (__proj__Mkdecls_elt__item__sym_name :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { sym_name; key; decls; a_names; aux_decls;_} -> sym_name
  
let (__proj__Mkdecls_elt__item__key :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { sym_name; key; decls; a_names; aux_decls;_} -> key
  
let (__proj__Mkdecls_elt__item__decls : decls_elt -> decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { sym_name; key; decls; a_names; aux_decls;_} -> decls
  
let (__proj__Mkdecls_elt__item__a_names :
  decls_elt -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { sym_name; key; decls; a_names; aux_decls;_} -> a_names
  
let (__proj__Mkdecls_elt__item__aux_decls :
  decls_elt -> decls_elt Prims.list) =
  fun projectee  ->
    match projectee with
    | { sym_name; key; decls; a_names; aux_decls;_} -> aux_decls
  
type decls_t = decls_elt Prims.list
let (mk_decls :
  Prims.string ->
    Prims.string -> decl Prims.list -> decls_elt Prims.list -> decls_t)
  =
  fun name  ->
    fun key  ->
      fun decls  ->
        fun aux_decls  ->
          let uu____2242 =
            let uu____2243 =
              let uu____2247 =
                FStar_List.collect (fun elt  -> elt.a_names) aux_decls  in
              let uu____2254 =
                FStar_List.collect
                  (fun uu___121_2261  ->
                     match uu___121_2261 with
                     | Assume a -> [a.assumption_name]
                     | uu____2268 -> []) decls
                 in
              FStar_List.append uu____2247 uu____2254  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2243;
              aux_decls
            }  in
          [uu____2242]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2283 =
      let uu____2284 =
        FStar_List.collect
          (fun uu___122_2291  ->
             match uu___122_2291 with
             | Assume a -> [a.assumption_name]
             | uu____2298 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2284;
        aux_decls = []
      }  in
    [uu____2283]
  
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
  'Auu____2347 'Auu____2348 . ('Auu____2347 * 'Auu____2348) -> 'Auu____2348 =
  fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2387 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___123_2398  ->
    match uu___123_2398 with
    | { tm = FreeV x; freevars = uu____2400; rng = uu____2401;_} -> fv_sort x
    | uu____2417 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___124_2424  ->
    match uu___124_2424 with
    | { tm = FreeV fv; freevars = uu____2426; rng = uu____2427;_} -> fv
    | uu____2442 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2464 -> []
    | BoundV uu____2471 -> []
    | FreeV fv -> [fv]
    | App (uu____2494,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2505,uu____2506,uu____2507,uu____2508,t1) -> freevars t1
    | Labeled (t1,uu____2529,uu____2530) -> freevars t1
    | LblPos (t1,uu____2534) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2554 = FStar_ST.op_Bang t.freevars  in
    match uu____2554 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2631 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2631  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___125_2695  ->
    match uu___125_2695 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___126_2705  ->
    match uu___126_2705 with
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
        let uu____2740 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2740
    | NatToBv n1 ->
        let uu____2745 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2745
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___127_2759  ->
    match uu___127_2759 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2769 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2769
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____2789 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2789
    | FreeV x ->
        let uu____2798 =
          let uu____2800 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____2800  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____2798
    | App (op,tms) ->
        let uu____2811 =
          let uu____2813 = op_to_string op  in
          let uu____2815 =
            let uu____2817 =
              let uu____2819 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2819 (FStar_String.concat " ")  in
            Prims.strcat uu____2817 ")"  in
          Prims.strcat uu____2813 uu____2815  in
        Prims.strcat "(" uu____2811
    | Labeled (t1,r1,r2) ->
        let uu____2836 = hash_of_term t1  in
        let uu____2838 =
          let uu____2840 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2840  in
        Prims.strcat uu____2836 uu____2838
    | LblPos (t1,r) ->
        let uu____2846 =
          let uu____2848 = hash_of_term t1  in
          Prims.strcat uu____2848
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2846
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2876 =
          let uu____2878 =
            let uu____2880 =
              let uu____2882 =
                let uu____2884 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2884 (FStar_String.concat " ")  in
              let uu____2894 =
                let uu____2896 =
                  let uu____2898 = hash_of_term body  in
                  let uu____2900 =
                    let uu____2902 =
                      let uu____2904 = weightToSmt wopt  in
                      let uu____2906 =
                        let uu____2908 =
                          let uu____2910 =
                            let uu____2912 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2931 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2931
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2912
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2910 "))"  in
                        Prims.strcat " " uu____2908  in
                      Prims.strcat uu____2904 uu____2906  in
                    Prims.strcat " " uu____2902  in
                  Prims.strcat uu____2898 uu____2900  in
                Prims.strcat ")(! " uu____2896  in
              Prims.strcat uu____2882 uu____2894  in
            Prims.strcat " (" uu____2880  in
          Prims.strcat (qop_to_string qop) uu____2878  in
        Prims.strcat "(" uu____2876
    | Let (es,body) ->
        let uu____2958 =
          let uu____2960 =
            let uu____2962 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2962 (FStar_String.concat " ")  in
          let uu____2972 =
            let uu____2974 =
              let uu____2976 = hash_of_term body  in
              Prims.strcat uu____2976 ")"  in
            Prims.strcat ") " uu____2974  in
          Prims.strcat uu____2960 uu____2972  in
        Prims.strcat "(let (" uu____2958

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3037 =
      let uu____3039 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____3039  in
    mkBoxFunctions uu____3037
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3056 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3056 = "Box") &&
        (let uu____3063 =
           let uu____3065 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3065  in
         Prims.op_Negation uu____3063)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3089 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3089; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3166 =
        let uu____3167 = FStar_Util.ensure_decimal i  in Integer uu____3167
         in
      mk uu____3166 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3182 = FStar_Util.string_of_int i  in mkInteger uu____3182 r
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3257  ->
    fun r  -> match uu____3257 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3287) -> mkFalse r
      | App (FalseOp ,uu____3292) -> mkTrue r
      | uu____3297 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3313  ->
    fun r  ->
      match uu____3313 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3321),uu____3322) -> t2
           | (uu____3327,App (TrueOp ,uu____3328)) -> t1
           | (App (FalseOp ,uu____3333),uu____3334) -> mkFalse r
           | (uu____3339,App (FalseOp ,uu____3340)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3357,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3366) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3373 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3393  ->
    fun r  ->
      match uu____3393 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3401),uu____3402) -> mkTrue r
           | (uu____3407,App (TrueOp ,uu____3408)) -> mkTrue r
           | (App (FalseOp ,uu____3413),uu____3414) -> t2
           | (uu____3419,App (FalseOp ,uu____3420)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3437,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3446) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3453 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3473  ->
    fun r  ->
      match uu____3473 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3481,App (TrueOp ,uu____3482)) -> mkTrue r
           | (App (FalseOp ,uu____3487),uu____3488) -> mkTrue r
           | (App (TrueOp ,uu____3493),uu____3494) -> t2
           | (uu____3499,App (Imp ,t1'::t2'::[])) ->
               let uu____3504 =
                 let uu____3511 =
                   let uu____3514 = mkAnd (t1, t1') r  in [uu____3514; t2']
                    in
                 (Imp, uu____3511)  in
               mkApp' uu____3504 r
           | uu____3517 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3542  ->
      fun r  -> match uu____3542 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3702  ->
      fun r  ->
        match uu____3702 with
        | (t1,t2) ->
            let uu____3711 =
              let uu____3718 =
                let uu____3721 =
                  let uu____3724 = mkNatToBv sz t2 r  in [uu____3724]  in
                t1 :: uu____3721  in
              (BvShl, uu____3718)  in
            mkApp' uu____3711 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3746  ->
      fun r  ->
        match uu____3746 with
        | (t1,t2) ->
            let uu____3755 =
              let uu____3762 =
                let uu____3765 =
                  let uu____3768 = mkNatToBv sz t2 r  in [uu____3768]  in
                t1 :: uu____3765  in
              (BvShr, uu____3762)  in
            mkApp' uu____3755 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3790  ->
      fun r  ->
        match uu____3790 with
        | (t1,t2) ->
            let uu____3799 =
              let uu____3806 =
                let uu____3809 =
                  let uu____3812 = mkNatToBv sz t2 r  in [uu____3812]  in
                t1 :: uu____3809  in
              (BvUdiv, uu____3806)  in
            mkApp' uu____3799 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3834  ->
      fun r  ->
        match uu____3834 with
        | (t1,t2) ->
            let uu____3843 =
              let uu____3850 =
                let uu____3853 =
                  let uu____3856 = mkNatToBv sz t2 r  in [uu____3856]  in
                t1 :: uu____3853  in
              (BvMod, uu____3850)  in
            mkApp' uu____3843 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3878  ->
      fun r  ->
        match uu____3878 with
        | (t1,t2) ->
            let uu____3887 =
              let uu____3894 =
                let uu____3897 =
                  let uu____3900 = mkNatToBv sz t2 r  in [uu____3900]  in
                t1 :: uu____3897  in
              (BvMul, uu____3894)  in
            mkApp' uu____3887 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3942  ->
    fun r  ->
      match uu____3942 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3961 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4098  ->
    fun r  ->
      match uu____4098 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4109) -> t2
           | App (FalseOp ,uu____4114) -> t3
           | uu____4119 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4120),App (TrueOp ,uu____4121)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4130),uu____4131) ->
                    let uu____4136 =
                      let uu____4141 = mkNot t1 t1.rng  in (uu____4141, t3)
                       in
                    mkImp uu____4136 r
                | (uu____4142,App (TrueOp ,uu____4143)) -> mkImp (t1, t2) r
                | (uu____4148,uu____4149) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4205 -> FStar_Pervasives_Native.None
      | BoundV uu____4207 -> FStar_Pervasives_Native.None
      | FreeV uu____4209 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4230 -> true
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
            | BvUext uu____4262 -> false
            | NatToBv uu____4265 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4276,uu____4277) -> aux t2
      | Quant uu____4280 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4300 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4315 = aux t1  in
          (match uu____4315 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4350 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4350
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4367 = op_to_string op  in
        let uu____4369 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4367 uu____4369
    | Labeled (t1,r1,r2) ->
        let uu____4377 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4377
    | LblPos (t1,s) ->
        let uu____4384 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4384
    | Quant (qop,l,uu____4389,uu____4390,t1) ->
        let uu____4410 = print_smt_term_list_list l  in
        let uu____4412 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4410
          uu____4412
    | Let (es,body) ->
        let uu____4421 = print_smt_term_list es  in
        let uu____4423 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4421 uu____4423

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4430 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4430 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4457 =
             let uu____4459 =
               let uu____4461 = print_smt_term_list l1  in
               Prims.strcat uu____4461 " ] "  in
             Prims.strcat "; [ " uu____4459  in
           Prims.strcat s uu____4457) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4501  ->
        match uu____4501 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4570 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4570 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4585 =
                         let uu____4591 =
                           let uu____4593 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4593
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4591)
                          in
                       FStar_Errors.log_issue r uu____4585);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4604) -> body
               | uu____4609 ->
                   let uu____4610 =
                     let uu____4611 =
                       let uu____4631 = all_pats_ok pats  in
                       (qop, uu____4631, wopt, vars, body)  in
                     Quant uu____4611  in
                   mk uu____4610 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4660  ->
    fun r  ->
      match uu____4660 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4706 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4706 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4739 = FStar_ST.op_Bang t1.freevars  in
        match uu____4739 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4798 ->
            (match t1.tm with
             | Integer uu____4808 -> t1
             | BoundV uu____4810 -> t1
             | FreeV x ->
                 let uu____4818 = index_of1 x  in
                 (match uu____4818 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4832 =
                   let uu____4839 = FStar_List.map (aux ix) tms  in
                   (op, uu____4839)  in
                 mkApp' uu____4832 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4849 =
                   let uu____4850 =
                     let uu____4858 = aux ix t2  in (uu____4858, r1, r2)  in
                   Labeled uu____4850  in
                 mk uu____4849 t2.rng
             | LblPos (t2,r) ->
                 let uu____4864 =
                   let uu____4865 =
                     let uu____4871 = aux ix t2  in (uu____4871, r)  in
                   LblPos uu____4865  in
                 mk uu____4864 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4897 =
                   let uu____4917 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4938 = aux (ix + n1) body  in
                   (qop, uu____4917, wopt, vars, uu____4938)  in
                 mkQuant t1.rng false uu____4897
             | Let (es,body) ->
                 let uu____4959 =
                   FStar_List.fold_left
                     (fun uu____4979  ->
                        fun e  ->
                          match uu____4979 with
                          | (ix1,l) ->
                              let uu____5003 =
                                let uu____5006 = aux ix1 e  in uu____5006 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5003))
                     (ix, []) es
                    in
                 (match uu____4959 with
                  | (ix1,es_rev) ->
                      let uu____5022 =
                        let uu____5029 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5029)  in
                      mkLet uu____5022 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5065 -> t1
        | FreeV uu____5067 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5089 =
              let uu____5096 = FStar_List.map (aux shift) tms2  in
              (op, uu____5096)  in
            mkApp' uu____5089 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5106 =
              let uu____5107 =
                let uu____5115 = aux shift t2  in (uu____5115, r1, r2)  in
              Labeled uu____5107  in
            mk uu____5106 t2.rng
        | LblPos (t2,r) ->
            let uu____5121 =
              let uu____5122 =
                let uu____5128 = aux shift t2  in (uu____5128, r)  in
              LblPos uu____5122  in
            mk uu____5121 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5160 =
              let uu____5180 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5197 = aux shift1 body  in
              (qop, uu____5180, wopt, vars, uu____5197)  in
            mkQuant t1.rng false uu____5160
        | Let (es,body) ->
            let uu____5214 =
              FStar_List.fold_left
                (fun uu____5234  ->
                   fun e  ->
                     match uu____5234 with
                     | (ix,es1) ->
                         let uu____5258 =
                           let uu____5261 = aux shift e  in uu____5261 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5258))
                (shift, []) es
               in
            (match uu____5214 with
             | (shift1,es_rev) ->
                 let uu____5277 =
                   let uu____5284 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5284)  in
                 mkLet uu____5277 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5304 = abstr [fv] t  in inst [s] uu____5304
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5334  ->
      match uu____5334 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5377 =
            let uu____5397 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5414 = FStar_List.map fv_sort vars  in
            let uu____5418 = abstr vars body  in
            (qop, uu____5397, wopt, uu____5414, uu____5418)  in
          mkQuant r true uu____5377
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5449  ->
      match uu____5449 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5508  ->
      match uu____5508 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5583  ->
      match uu____5583 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5646  ->
      match uu____5646 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5697  ->
    fun r  ->
      match uu____5697 with
      | (bindings,body) ->
          let uu____5723 = FStar_List.split bindings  in
          (match uu____5723 with
           | (vars,es) ->
               let uu____5742 =
                 let uu____5749 = abstr vars body  in (es, uu____5749)  in
               mkLet uu____5742 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5771  ->
    match uu____5771 with
    | (nm,vars,s,tm,c) ->
        let uu____5796 =
          let uu____5810 = FStar_List.map fv_sort vars  in
          let uu____5814 = abstr vars tm  in
          (nm, uu____5810, s, uu____5814, c)  in
        DefineFun uu____5796
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5825 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5825
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5843  ->
    fun id1  ->
      match uu____5843 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5859 =
              let uu____5860 =
                let uu____5865 = mkInteger' id1 norng  in
                let uu____5866 =
                  let uu____5867 =
                    let uu____5875 = constr_id_of_sort sort  in
                    let uu____5877 =
                      let uu____5880 = mkApp (tok_name, []) norng  in
                      [uu____5880]  in
                    (uu____5875, uu____5877)  in
                  mkApp uu____5867 norng  in
                (uu____5865, uu____5866)  in
              mkEq uu____5860 norng  in
            let uu____5887 = escape a_name  in
            {
              assumption_term = uu____5859;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5887;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5913  ->
      match uu____5913 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5953 =
                        let uu____5959 =
                          let uu____5961 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____5961  in
                        (uu____5959, s)  in
                      mkFreeV uu____5953 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____5983 =
              let uu____5991 = constr_id_of_sort sort  in
              (uu____5991, [capp])  in
            mkApp uu____5983 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____6000 =
              let uu____6001 =
                let uu____6012 =
                  let uu____6013 =
                    let uu____6018 = mkInteger id2 norng  in
                    (uu____6018, cid_app)  in
                  mkEq uu____6013 norng  in
                ([[capp]], bvar_names, uu____6012)  in
              mkForall rng uu____6001  in
            let uu____6027 = escape a_name  in
            {
              assumption_term = uu____6000;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6027;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6052  ->
      match uu____6052 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6085 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6085  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6120 = let uu____6126 = bvar_name i  in (uu____6126, s)
               in
            mkFreeV uu____6120  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6159  ->
                      match uu____6159 with
                      | (uu____6169,s,uu____6171) ->
                          let uu____6176 = bvar i s  in uu____6176 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6198 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6236  ->
                      match uu____6236 with
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
                              let uu____6269 =
                                let uu____6270 =
                                  let uu____6281 =
                                    let uu____6282 =
                                      let uu____6287 =
                                        let uu____6288 = bvar i s  in
                                        uu____6288 norng  in
                                      (cproj_app, uu____6287)  in
                                    mkEq uu____6282 norng  in
                                  ([[capp]], bvar_names, uu____6281)  in
                                mkForall rng uu____6270  in
                              let uu____6301 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6269;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6301;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6198 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6326  ->
      match uu____6326 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6374  ->
                    match uu____6374 with
                    | (uu____6383,sort1,uu____6385) -> sort1))
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
              let uu____6415 =
                let uu____6420 =
                  let uu____6421 =
                    let uu____6429 = constr_id_of_sort sort  in
                    (uu____6429, [xx])  in
                  mkApp uu____6421 norng  in
                let uu____6434 =
                  let uu____6435 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6435 norng  in
                (uu____6420, uu____6434)  in
              mkEq uu____6415 norng  in
            let uu____6437 =
              let uu____6453 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6516  ->
                          match uu____6516 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6556 = mkApp (proj, [xx]) norng  in
                                (uu____6556, [])
                              else
                                (let fi =
                                   let uu____6580 =
                                     let uu____6582 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____6582  in
                                   (uu____6580, s)  in
                                 let uu____6586 = mkFreeV fi norng  in
                                 (uu____6586, [fi]))))
                 in
              FStar_All.pipe_right uu____6453 FStar_List.split  in
            match uu____6437 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6677 =
                    let uu____6682 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6682)  in
                  mkEq uu____6677 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6692 ->
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
          let uu____6724 =
            let uu____6727 =
              let uu____6728 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6728  in
            uu____6727 :: cdecl :: cid :: projs  in
          let uu____6731 =
            let uu____6734 =
              let uu____6737 =
                let uu____6738 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6738  in
              [uu____6737]  in
            FStar_List.append [disc] uu____6734  in
          FStar_List.append uu____6724 uu____6731
  
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
          let uu____6805 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6869  ->
                    fun s  ->
                      match uu____6869 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6934 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6945 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6945  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____6963 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6963  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6805 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list))
  =
  fun sorts  ->
    let uu____7069 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7069 with
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
              (let uu____7268 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7268)
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
                               "Prims.guard_free",{ tm = BoundV uu____7314;
                                                    freevars = uu____7315;
                                                    rng = uu____7316;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7334 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____7410 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7410 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7439 = op_to_string op  in
              let uu____7441 =
                let uu____7443 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7443 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7439 uu____7441
          | Labeled (t2,uu____7455,uu____7456) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7463 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7463 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7491 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7491 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7559 ->
                         let uu____7564 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7583 =
                                     let uu____7585 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7593 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7593) pats2
                                        in
                                     FStar_String.concat " " uu____7585  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7583))
                            in
                         FStar_All.pipe_right uu____7564
                           (FStar_String.concat "\n")
                      in
                   let uu____7603 =
                     let uu____7607 =
                       let uu____7611 =
                         let uu____7615 = aux1 n2 names2 body  in
                         let uu____7617 =
                           let uu____7621 = weightToSmt wopt  in
                           [uu____7621; pats_str; qid]  in
                         uu____7615 :: uu____7617  in
                       binders1 :: uu____7611  in
                     (qop_to_string qop) :: uu____7607  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7603)
          | Let (es,body) ->
              let uu____7637 =
                FStar_List.fold_left
                  (fun uu____7680  ->
                     fun e  ->
                       match uu____7680 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7743 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7743  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____7762 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7762  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7637 with
               | (names2,binders,n2) ->
                   let uu____7816 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7816)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7832 = FStar_Range.string_of_range t1.rng  in
            let uu____7834 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7832
              uu____7834 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___128_7856  ->
      match uu___128_7856 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7867 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7867 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7889 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7964 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7964 (FStar_String.concat "\n")  in
            let uu____7974 = FStar_Options.keep_query_captions ()  in
            if uu____7974
            then
              let uu____7978 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7980 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7978 uu____7980
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7989 =
                let uu____7991 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7991 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7989
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8032 = caption_to_string print_captions c  in
            let uu____8034 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8032 f
              (FStar_String.concat " " l) uu____8034
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8049 = name_macro_binders arg_sorts  in
            (match uu____8049 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8088 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8088 body  in
                 let uu____8103 = caption_to_string print_captions c  in
                 let uu____8105 = strSort retsort  in
                 let uu____8107 =
                   let uu____8109 = escape f  in
                   termToSmt print_captions uu____8109 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8103 f (FStar_String.concat " " binders) uu____8105
                   uu____8107)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___129_8136  ->
                      match uu___129_8136 with
                      | Name n1 ->
                          let uu____8139 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____8139
                      | Namespace ns ->
                          let uu____8143 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____8143
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8153 =
                  let uu____8155 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8155  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8153
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8166 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8168 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8166
              fids uu____8168 n1
        | Eval t ->
            let uu____8172 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8172
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8179 -> ""
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
      let uu____8200 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8200 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8211 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8211 (FStar_String.concat "\n")

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
      let uu____8331 =
        let uu____8335 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8335
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8331 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8366 =
      let uu____8367 =
        let uu____8369 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8369  in
      let uu____8378 =
        let uu____8381 =
          let uu____8382 =
            let uu____8384 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8384  in
          (uu____8382, (BitVec_sort sz), true)  in
        [uu____8381]  in
      (uu____8367, uu____8378, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8366 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8427  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8452 =
       let uu____8454 = FStar_ST.op_Bang __range_c  in
       uu____8454 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8452);
    (let uu____8499 =
       let uu____8507 = let uu____8510 = mkInteger' i norng  in [uu____8510]
          in
       ("Range_const", uu____8507)  in
     mkApp uu____8499 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8553 =
        let uu____8561 = let uu____8564 = mkInteger' i norng  in [uu____8564]
           in
        ("Tm_uvar", uu____8561)  in
      mkApp uu____8553 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8607 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8631 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8631 u v1 t
  
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
      let uu____8706 =
        let uu____8708 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8708  in
      let uu____8717 =
        let uu____8719 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8719  in
      elim_box true uu____8706 uu____8717 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8742 =
        let uu____8744 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8744  in
      let uu____8753 =
        let uu____8755 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8755  in
      elim_box true uu____8742 uu____8753 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____8778 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____8792 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8818 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8818
         | uu____8821 -> FStar_Pervasives_Native.None)
    | uu____8823 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8841::t1::t2::[]);
                       freevars = uu____8844; rng = uu____8845;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8861::t1::t2::[]);
                       freevars = uu____8864; rng = uu____8865;_}::[])
        -> let uu____8881 = mkEq (t1, t2) norng  in mkNot uu____8881 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8884; rng = uu____8885;_}::[])
        ->
        let uu____8901 =
          let uu____8906 = unboxInt t1  in
          let uu____8907 = unboxInt t2  in (uu____8906, uu____8907)  in
        mkLTE uu____8901 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8910; rng = uu____8911;_}::[])
        ->
        let uu____8927 =
          let uu____8932 = unboxInt t1  in
          let uu____8933 = unboxInt t2  in (uu____8932, uu____8933)  in
        mkLT uu____8927 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8936; rng = uu____8937;_}::[])
        ->
        let uu____8953 =
          let uu____8958 = unboxInt t1  in
          let uu____8959 = unboxInt t2  in (uu____8958, uu____8959)  in
        mkGTE uu____8953 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8962; rng = uu____8963;_}::[])
        ->
        let uu____8979 =
          let uu____8984 = unboxInt t1  in
          let uu____8985 = unboxInt t2  in (uu____8984, uu____8985)  in
        mkGT uu____8979 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8988; rng = uu____8989;_}::[])
        ->
        let uu____9005 =
          let uu____9010 = unboxBool t1  in
          let uu____9011 = unboxBool t2  in (uu____9010, uu____9011)  in
        mkAnd uu____9005 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9014; rng = uu____9015;_}::[])
        ->
        let uu____9031 =
          let uu____9036 = unboxBool t1  in
          let uu____9037 = unboxBool t2  in (uu____9036, uu____9037)  in
        mkOr uu____9031 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9039; rng = uu____9040;_}::[])
        -> let uu____9056 = unboxBool t1  in mkNot uu____9056 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9060; rng = uu____9061;_}::[])
        when
        let uu____9077 = getBoxedInteger t0  in FStar_Util.is_some uu____9077
        ->
        let sz =
          let uu____9084 = getBoxedInteger t0  in
          match uu____9084 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9092 -> failwith "impossible"  in
        let uu____9098 =
          let uu____9103 = unboxBitVec sz t1  in
          let uu____9104 = unboxBitVec sz t2  in (uu____9103, uu____9104)  in
        mkBvUlt uu____9098 t.rng
    | App
        (Var
         "Prims.equals",uu____9105::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9109;
                                      rng = uu____9110;_}::uu____9111::[])
        when
        let uu____9127 = getBoxedInteger t0  in FStar_Util.is_some uu____9127
        ->
        let sz =
          let uu____9134 = getBoxedInteger t0  in
          match uu____9134 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9142 -> failwith "impossible"  in
        let uu____9148 =
          let uu____9153 = unboxBitVec sz t1  in
          let uu____9154 = unboxBitVec sz t2  in (uu____9153, uu____9154)  in
        mkBvUlt uu____9148 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___130_9159 = unboxBool t1  in
        {
          tm = (uu___130_9159.tm);
          freevars = (uu___130_9159.freevars);
          rng = (t.rng)
        }
    | uu____9160 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9221 = FStar_Options.unthrottle_inductives ()  in
        if uu____9221
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
    let uu____9354 =
      let uu____9355 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9355 t t.rng  in
    FStar_All.pipe_right uu____9354 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9373 =
        let uu____9381 = let uu____9384 = mkInteger' i norng  in [uu____9384]
           in
        ("FString_const", uu____9381)  in
      mkApp uu____9373 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9415 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9415 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9462 =
         let uu____9470 =
           let uu____9473 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9473]  in
         ("SFuel", uu____9470)  in
       mkApp uu____9462 norng)
  
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
            let uu____9521 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9521
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
      let uu____9584 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9584
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9604 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9604
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9615 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9615
  