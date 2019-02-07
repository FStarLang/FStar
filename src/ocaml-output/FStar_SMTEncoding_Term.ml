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
    Prims.string -> decl Prims.list -> decls_elt Prims.list -> decls_t)
  =
  fun name  ->
    fun key  ->
      fun decls  ->
        fun aux_decls  ->
          let uu____2195 =
            let uu____2196 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____2222 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2196
            }  in
          [uu____2195]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2236 =
      let uu____2237 =
        FStar_List.collect
          (fun uu___11_2244  ->
             match uu___11_2244 with
             | Assume a -> [a.assumption_name]
             | uu____2251 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2237
      }  in
    [uu____2236]
  
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
  'Auu____2300 'Auu____2301 . ('Auu____2300 * 'Auu____2301) -> 'Auu____2301 =
  fun x  -> FStar_Pervasives_Native.snd x 
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2340 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___12_2351  ->
    match uu___12_2351 with
    | { tm = FreeV x; freevars = uu____2353; rng = uu____2354;_} -> fv_sort x
    | uu____2370 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___13_2377  ->
    match uu___13_2377 with
    | { tm = FreeV fv; freevars = uu____2379; rng = uu____2380;_} -> fv
    | uu____2395 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2417 -> []
    | BoundV uu____2424 -> []
    | FreeV fv -> [fv]
    | App (uu____2447,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2458,uu____2459,uu____2460,uu____2461,t1) -> freevars t1
    | Labeled (t1,uu____2482,uu____2483) -> freevars t1
    | LblPos (t1,uu____2487) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2507 = FStar_ST.op_Bang t.freevars  in
    match uu____2507 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2584 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2584  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___14_2648  ->
    match uu___14_2648 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___15_2658  ->
    match uu___15_2658 with
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
        let uu____2693 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2693
    | NatToBv n1 ->
        let uu____2698 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2698
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___16_2712  ->
    match uu___16_2712 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2722 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2722
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____2742 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2742
    | FreeV x ->
        let uu____2751 =
          let uu____2753 = strSort (FStar_Pervasives_Native.snd x)  in
          Prims.strcat ":" uu____2753  in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____2751
    | App (op,tms) ->
        let uu____2764 =
          let uu____2766 = op_to_string op  in
          let uu____2768 =
            let uu____2770 =
              let uu____2772 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2772 (FStar_String.concat " ")  in
            Prims.strcat uu____2770 ")"  in
          Prims.strcat uu____2766 uu____2768  in
        Prims.strcat "(" uu____2764
    | Labeled (t1,r1,r2) ->
        let uu____2789 = hash_of_term t1  in
        let uu____2791 =
          let uu____2793 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2793  in
        Prims.strcat uu____2789 uu____2791
    | LblPos (t1,r) ->
        let uu____2799 =
          let uu____2801 = hash_of_term t1  in
          Prims.strcat uu____2801
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2799
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2829 =
          let uu____2831 =
            let uu____2833 =
              let uu____2835 =
                let uu____2837 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____2837 (FStar_String.concat " ")  in
              let uu____2847 =
                let uu____2849 =
                  let uu____2851 = hash_of_term body  in
                  let uu____2853 =
                    let uu____2855 =
                      let uu____2857 = weightToSmt wopt  in
                      let uu____2859 =
                        let uu____2861 =
                          let uu____2863 =
                            let uu____2865 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____2884 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____2884
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____2865
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____2863 "))"  in
                        Prims.strcat " " uu____2861  in
                      Prims.strcat uu____2857 uu____2859  in
                    Prims.strcat " " uu____2855  in
                  Prims.strcat uu____2851 uu____2853  in
                Prims.strcat ")(! " uu____2849  in
              Prims.strcat uu____2835 uu____2847  in
            Prims.strcat " (" uu____2833  in
          Prims.strcat (qop_to_string qop) uu____2831  in
        Prims.strcat "(" uu____2829
    | Let (es,body) ->
        let uu____2911 =
          let uu____2913 =
            let uu____2915 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____2915 (FStar_String.concat " ")  in
          let uu____2925 =
            let uu____2927 =
              let uu____2929 = hash_of_term body  in
              Prims.strcat uu____2929 ")"  in
            Prims.strcat ") " uu____2927  in
          Prims.strcat uu____2913 uu____2925  in
        Prims.strcat "(let (" uu____2911

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____2990 =
      let uu____2992 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____2992  in
    mkBoxFunctions uu____2990
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3009 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3009 = "Box") &&
        (let uu____3016 =
           let uu____3018 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3018  in
         Prims.op_Negation uu____3016)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3042 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3042; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3119 =
        let uu____3120 = FStar_Util.ensure_decimal i  in Integer uu____3120
         in
      mk uu____3119 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3135 = FStar_Util.string_of_int i  in mkInteger uu____3135 r
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3210  ->
    fun r  -> match uu____3210 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3240) -> mkFalse r
      | App (FalseOp ,uu____3245) -> mkTrue r
      | uu____3250 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3266  ->
    fun r  ->
      match uu____3266 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3274),uu____3275) -> t2
           | (uu____3280,App (TrueOp ,uu____3281)) -> t1
           | (App (FalseOp ,uu____3286),uu____3287) -> mkFalse r
           | (uu____3292,App (FalseOp ,uu____3293)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3310,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3319) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3326 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3346  ->
    fun r  ->
      match uu____3346 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3354),uu____3355) -> mkTrue r
           | (uu____3360,App (TrueOp ,uu____3361)) -> mkTrue r
           | (App (FalseOp ,uu____3366),uu____3367) -> t2
           | (uu____3372,App (FalseOp ,uu____3373)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3390,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3399) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3406 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3426  ->
    fun r  ->
      match uu____3426 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3434,App (TrueOp ,uu____3435)) -> mkTrue r
           | (App (FalseOp ,uu____3440),uu____3441) -> mkTrue r
           | (App (TrueOp ,uu____3446),uu____3447) -> t2
           | (uu____3452,App (Imp ,t1'::t2'::[])) ->
               let uu____3457 =
                 let uu____3464 =
                   let uu____3467 = mkAnd (t1, t1') r  in [uu____3467; t2']
                    in
                 (Imp, uu____3464)  in
               mkApp' uu____3457 r
           | uu____3470 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3495  ->
      fun r  -> match uu____3495 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3655  ->
      fun r  ->
        match uu____3655 with
        | (t1,t2) ->
            let uu____3664 =
              let uu____3671 =
                let uu____3674 =
                  let uu____3677 = mkNatToBv sz t2 r  in [uu____3677]  in
                t1 :: uu____3674  in
              (BvShl, uu____3671)  in
            mkApp' uu____3664 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3699  ->
      fun r  ->
        match uu____3699 with
        | (t1,t2) ->
            let uu____3708 =
              let uu____3715 =
                let uu____3718 =
                  let uu____3721 = mkNatToBv sz t2 r  in [uu____3721]  in
                t1 :: uu____3718  in
              (BvShr, uu____3715)  in
            mkApp' uu____3708 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3743  ->
      fun r  ->
        match uu____3743 with
        | (t1,t2) ->
            let uu____3752 =
              let uu____3759 =
                let uu____3762 =
                  let uu____3765 = mkNatToBv sz t2 r  in [uu____3765]  in
                t1 :: uu____3762  in
              (BvUdiv, uu____3759)  in
            mkApp' uu____3752 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3787  ->
      fun r  ->
        match uu____3787 with
        | (t1,t2) ->
            let uu____3796 =
              let uu____3803 =
                let uu____3806 =
                  let uu____3809 = mkNatToBv sz t2 r  in [uu____3809]  in
                t1 :: uu____3806  in
              (BvMod, uu____3803)  in
            mkApp' uu____3796 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3831  ->
      fun r  ->
        match uu____3831 with
        | (t1,t2) ->
            let uu____3840 =
              let uu____3847 =
                let uu____3850 =
                  let uu____3853 = mkNatToBv sz t2 r  in [uu____3853]  in
                t1 :: uu____3850  in
              (BvMul, uu____3847)  in
            mkApp' uu____3840 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3895  ->
    fun r  ->
      match uu____3895 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3914 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4051  ->
    fun r  ->
      match uu____4051 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4062) -> t2
           | App (FalseOp ,uu____4067) -> t3
           | uu____4072 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4073),App (TrueOp ,uu____4074)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4083),uu____4084) ->
                    let uu____4089 =
                      let uu____4094 = mkNot t1 t1.rng  in (uu____4094, t3)
                       in
                    mkImp uu____4089 r
                | (uu____4095,App (TrueOp ,uu____4096)) -> mkImp (t1, t2) r
                | (uu____4101,uu____4102) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4158 -> FStar_Pervasives_Native.None
      | BoundV uu____4160 -> FStar_Pervasives_Native.None
      | FreeV uu____4162 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4183 -> true
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
            | BvUext uu____4215 -> false
            | NatToBv uu____4218 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4229,uu____4230) -> aux t2
      | Quant uu____4233 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4253 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4268 = aux t1  in
          (match uu____4268 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4303 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4303
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4320 = op_to_string op  in
        let uu____4322 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4320 uu____4322
    | Labeled (t1,r1,r2) ->
        let uu____4330 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4330
    | LblPos (t1,s) ->
        let uu____4337 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4337
    | Quant (qop,l,uu____4342,uu____4343,t1) ->
        let uu____4363 = print_smt_term_list_list l  in
        let uu____4365 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4363
          uu____4365
    | Let (es,body) ->
        let uu____4374 = print_smt_term_list es  in
        let uu____4376 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4374 uu____4376

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4383 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4383 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4410 =
             let uu____4412 =
               let uu____4414 = print_smt_term_list l1  in
               Prims.strcat uu____4414 " ] "  in
             Prims.strcat "; [ " uu____4412  in
           Prims.strcat s uu____4410) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4454  ->
        match uu____4454 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4523 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4523 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4538 =
                         let uu____4544 =
                           let uu____4546 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4546
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4544)
                          in
                       FStar_Errors.log_issue r uu____4538);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4557) -> body
               | uu____4562 ->
                   let uu____4563 =
                     let uu____4564 =
                       let uu____4584 = all_pats_ok pats  in
                       (qop, uu____4584, wopt, vars, body)  in
                     Quant uu____4564  in
                   mk uu____4563 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4613  ->
    fun r  ->
      match uu____4613 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4659 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4659 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4692 = FStar_ST.op_Bang t1.freevars  in
        match uu____4692 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4751 ->
            (match t1.tm with
             | Integer uu____4761 -> t1
             | BoundV uu____4763 -> t1
             | FreeV x ->
                 let uu____4771 = index_of1 x  in
                 (match uu____4771 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4785 =
                   let uu____4792 = FStar_List.map (aux ix) tms  in
                   (op, uu____4792)  in
                 mkApp' uu____4785 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____4802 =
                   let uu____4803 =
                     let uu____4811 = aux ix t2  in (uu____4811, r1, r2)  in
                   Labeled uu____4803  in
                 mk uu____4802 t2.rng
             | LblPos (t2,r) ->
                 let uu____4817 =
                   let uu____4818 =
                     let uu____4824 = aux ix t2  in (uu____4824, r)  in
                   LblPos uu____4818  in
                 mk uu____4817 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____4850 =
                   let uu____4870 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____4891 = aux (ix + n1) body  in
                   (qop, uu____4870, wopt, vars, uu____4891)  in
                 mkQuant t1.rng false uu____4850
             | Let (es,body) ->
                 let uu____4912 =
                   FStar_List.fold_left
                     (fun uu____4932  ->
                        fun e  ->
                          match uu____4932 with
                          | (ix1,l) ->
                              let uu____4956 =
                                let uu____4959 = aux ix1 e  in uu____4959 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____4956))
                     (ix, []) es
                    in
                 (match uu____4912 with
                  | (ix1,es_rev) ->
                      let uu____4975 =
                        let uu____4982 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____4982)  in
                      mkLet uu____4975 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5018 -> t1
        | FreeV uu____5020 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5042 =
              let uu____5049 = FStar_List.map (aux shift) tms2  in
              (op, uu____5049)  in
            mkApp' uu____5042 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5059 =
              let uu____5060 =
                let uu____5068 = aux shift t2  in (uu____5068, r1, r2)  in
              Labeled uu____5060  in
            mk uu____5059 t2.rng
        | LblPos (t2,r) ->
            let uu____5074 =
              let uu____5075 =
                let uu____5081 = aux shift t2  in (uu____5081, r)  in
              LblPos uu____5075  in
            mk uu____5074 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5113 =
              let uu____5133 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5150 = aux shift1 body  in
              (qop, uu____5133, wopt, vars, uu____5150)  in
            mkQuant t1.rng false uu____5113
        | Let (es,body) ->
            let uu____5167 =
              FStar_List.fold_left
                (fun uu____5187  ->
                   fun e  ->
                     match uu____5187 with
                     | (ix,es1) ->
                         let uu____5211 =
                           let uu____5214 = aux shift e  in uu____5214 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5211))
                (shift, []) es
               in
            (match uu____5167 with
             | (shift1,es_rev) ->
                 let uu____5230 =
                   let uu____5237 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5237)  in
                 mkLet uu____5230 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5257 = abstr [fv] t  in inst [s] uu____5257
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5287  ->
      match uu____5287 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5330 =
            let uu____5350 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5367 = FStar_List.map fv_sort vars  in
            let uu____5371 = abstr vars body  in
            (qop, uu____5350, wopt, uu____5367, uu____5371)  in
          mkQuant r true uu____5330
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5402  ->
      match uu____5402 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5461  ->
      match uu____5461 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5536  ->
      match uu____5536 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5599  ->
      match uu____5599 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5650  ->
    fun r  ->
      match uu____5650 with
      | (bindings,body) ->
          let uu____5676 = FStar_List.split bindings  in
          (match uu____5676 with
           | (vars,es) ->
               let uu____5695 =
                 let uu____5702 = abstr vars body  in (es, uu____5702)  in
               mkLet uu____5695 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)
    -> decl)
  =
  fun uu____5729  ->
    match uu____5729 with
    | (nm,vars,s,tm,c) ->
        let uu____5769 =
          let uu____5783 = FStar_List.map fv_sort vars  in
          let uu____5792 = abstr vars tm  in
          (nm, uu____5783, s, uu____5792, c)  in
        DefineFun uu____5769
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5803 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5803
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5821  ->
    fun id1  ->
      match uu____5821 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____5837 =
              let uu____5838 =
                let uu____5843 = mkInteger' id1 norng  in
                let uu____5844 =
                  let uu____5845 =
                    let uu____5853 = constr_id_of_sort sort  in
                    let uu____5855 =
                      let uu____5858 = mkApp (tok_name, []) norng  in
                      [uu____5858]  in
                    (uu____5853, uu____5855)  in
                  mkApp uu____5845 norng  in
                (uu____5843, uu____5844)  in
              mkEq uu____5838 norng  in
            let uu____5865 = escape a_name  in
            {
              assumption_term = uu____5837;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____5865;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____5891  ->
      match uu____5891 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____5931 =
                        let uu____5937 =
                          let uu____5939 = FStar_Util.string_of_int i  in
                          Prims.strcat "x_" uu____5939  in
                        (uu____5937, s)  in
                      mkFreeV uu____5931 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____5961 =
              let uu____5969 = constr_id_of_sort sort  in
              (uu____5969, [capp])  in
            mkApp uu____5961 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____5978 =
              let uu____5979 =
                let uu____5990 =
                  let uu____5991 =
                    let uu____5996 = mkInteger id2 norng  in
                    (uu____5996, cid_app)  in
                  mkEq uu____5991 norng  in
                ([[capp]], bvar_names, uu____5990)  in
              mkForall rng uu____5979  in
            let uu____6005 = escape a_name  in
            {
              assumption_term = uu____5978;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6005;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6030  ->
      match uu____6030 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6063 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6063  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6098 = let uu____6104 = bvar_name i  in (uu____6104, s)
               in
            mkFreeV uu____6098  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6137  ->
                      match uu____6137 with
                      | (uu____6147,s,uu____6149) ->
                          let uu____6154 = bvar i s  in uu____6154 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6176 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6214  ->
                      match uu____6214 with
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
                              let uu____6247 =
                                let uu____6248 =
                                  let uu____6259 =
                                    let uu____6260 =
                                      let uu____6265 =
                                        let uu____6266 = bvar i s  in
                                        uu____6266 norng  in
                                      (cproj_app, uu____6265)  in
                                    mkEq uu____6260 norng  in
                                  ([[capp]], bvar_names, uu____6259)  in
                                mkForall rng uu____6248  in
                              let uu____6279 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6247;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6279;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6176 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6304  ->
      match uu____6304 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6352  ->
                    match uu____6352 with
                    | (uu____6361,sort1,uu____6363) -> sort1))
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
              let uu____6393 =
                let uu____6398 =
                  let uu____6399 =
                    let uu____6407 = constr_id_of_sort sort  in
                    (uu____6407, [xx])  in
                  mkApp uu____6399 norng  in
                let uu____6412 =
                  let uu____6413 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6413 norng  in
                (uu____6398, uu____6412)  in
              mkEq uu____6393 norng  in
            let uu____6415 =
              let uu____6431 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6494  ->
                          match uu____6494 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6534 = mkApp (proj, [xx]) norng  in
                                (uu____6534, [])
                              else
                                (let fi =
                                   let uu____6558 =
                                     let uu____6560 =
                                       FStar_Util.string_of_int i  in
                                     Prims.strcat "f_" uu____6560  in
                                   (uu____6558, s)  in
                                 let uu____6564 = mkFreeV fi norng  in
                                 (uu____6564, [fi]))))
                 in
              FStar_All.pipe_right uu____6431 FStar_List.split  in
            match uu____6415 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6655 =
                    let uu____6660 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6660)  in
                  mkEq uu____6655 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6670 ->
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
          let uu____6798 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____6862  ->
                    fun s  ->
                      match uu____6862 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____6927 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____6938 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____6938  in
                          let names2 = (nm, s) :: names1  in
                          let b =
                            let uu____6956 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____6956  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6798 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list))
  =
  fun sorts  ->
    let uu____7062 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7062 with
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
              (let uu____7261 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7261)
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
                               "Prims.guard_free",{ tm = BoundV uu____7307;
                                                    freevars = uu____7308;
                                                    rng = uu____7309;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7327 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____7403 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7403 FStar_Pervasives_Native.fst
          | FreeV x -> FStar_Pervasives_Native.fst x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7432 = op_to_string op  in
              let uu____7434 =
                let uu____7436 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7436 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7432 uu____7434
          | Labeled (t2,uu____7448,uu____7449) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7456 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7456 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7484 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7484 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7552 ->
                         let uu____7557 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7576 =
                                     let uu____7578 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7586 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7586) pats2
                                        in
                                     FStar_String.concat " " uu____7578  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7576))
                            in
                         FStar_All.pipe_right uu____7557
                           (FStar_String.concat "\n")
                      in
                   let uu____7596 =
                     let uu____7600 =
                       let uu____7604 =
                         let uu____7608 = aux1 n2 names2 body  in
                         let uu____7610 =
                           let uu____7614 = weightToSmt wopt  in
                           [uu____7614; pats_str; qid]  in
                         uu____7608 :: uu____7610  in
                       binders1 :: uu____7604  in
                     (qop_to_string qop) :: uu____7600  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7596)
          | Let (es,body) ->
              let uu____7630 =
                FStar_List.fold_left
                  (fun uu____7673  ->
                     fun e  ->
                       match uu____7673 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7736 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7736  in
                           let names01 = (nm, Term_sort) :: names0  in
                           let b =
                             let uu____7755 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7755  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7630 with
               | (names2,binders,n2) ->
                   let uu____7809 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7809)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7825 = FStar_Range.string_of_range t1.rng  in
            let uu____7827 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7825
              uu____7827 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___17_7849  ->
      match uu___17_7849 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7860 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7860 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7882 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7957 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7957 (FStar_String.concat "\n")  in
            let uu____7967 = FStar_Options.keep_query_captions ()  in
            if uu____7967
            then
              let uu____7971 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7973 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7971 uu____7973
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7982 =
                let uu____7984 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7984 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7982
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8025 = caption_to_string print_captions c  in
            let uu____8027 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8025 f
              (FStar_String.concat " " l) uu____8027
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8042 = name_macro_binders arg_sorts  in
            (match uu____8042 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8081 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8081 body  in
                 let uu____8096 = caption_to_string print_captions c  in
                 let uu____8098 = strSort retsort  in
                 let uu____8100 =
                   let uu____8102 = escape f  in
                   termToSmt print_captions uu____8102 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8096 f (FStar_String.concat " " binders) uu____8098
                   uu____8100)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___18_8129  ->
                      match uu___18_8129 with
                      | Name n1 ->
                          let uu____8132 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____8132
                      | Namespace ns ->
                          let uu____8136 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____8136
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8146 =
                  let uu____8148 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8148  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8146
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8159 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8161 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8159
              fids uu____8161 n1
        | Eval t ->
            let uu____8165 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8165
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8172 -> ""
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
      let uu____8193 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8193 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8204 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8204 (FStar_String.concat "\n")

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
      let uu____8324 =
        let uu____8328 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8328
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8324 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8359 =
      let uu____8360 =
        let uu____8362 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8362  in
      let uu____8371 =
        let uu____8374 =
          let uu____8375 =
            let uu____8377 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8377  in
          (uu____8375, (BitVec_sort sz), true)  in
        [uu____8374]  in
      (uu____8360, uu____8371, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8359 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8420  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8445 =
       let uu____8447 = FStar_ST.op_Bang __range_c  in
       uu____8447 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8445);
    (let uu____8492 =
       let uu____8500 = let uu____8503 = mkInteger' i norng  in [uu____8503]
          in
       ("Range_const", uu____8500)  in
     mkApp uu____8492 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8546 =
        let uu____8554 = let uu____8557 = mkInteger' i norng  in [uu____8557]
           in
        ("Tm_uvar", uu____8554)  in
      mkApp uu____8546 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8600 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8624 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8624 u v1 t
  
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
      let uu____8699 =
        let uu____8701 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8701  in
      let uu____8710 =
        let uu____8712 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8712  in
      elim_box true uu____8699 uu____8710 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8735 =
        let uu____8737 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8737  in
      let uu____8746 =
        let uu____8748 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8748  in
      elim_box true uu____8735 uu____8746 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____8771 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____8785 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8811 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8811
         | uu____8814 -> FStar_Pervasives_Native.None)
    | uu____8816 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8834::t1::t2::[]);
                       freevars = uu____8837; rng = uu____8838;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8854::t1::t2::[]);
                       freevars = uu____8857; rng = uu____8858;_}::[])
        -> let uu____8874 = mkEq (t1, t2) norng  in mkNot uu____8874 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8877; rng = uu____8878;_}::[])
        ->
        let uu____8894 =
          let uu____8899 = unboxInt t1  in
          let uu____8900 = unboxInt t2  in (uu____8899, uu____8900)  in
        mkLTE uu____8894 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8903; rng = uu____8904;_}::[])
        ->
        let uu____8920 =
          let uu____8925 = unboxInt t1  in
          let uu____8926 = unboxInt t2  in (uu____8925, uu____8926)  in
        mkLT uu____8920 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8929; rng = uu____8930;_}::[])
        ->
        let uu____8946 =
          let uu____8951 = unboxInt t1  in
          let uu____8952 = unboxInt t2  in (uu____8951, uu____8952)  in
        mkGTE uu____8946 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8955; rng = uu____8956;_}::[])
        ->
        let uu____8972 =
          let uu____8977 = unboxInt t1  in
          let uu____8978 = unboxInt t2  in (uu____8977, uu____8978)  in
        mkGT uu____8972 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8981; rng = uu____8982;_}::[])
        ->
        let uu____8998 =
          let uu____9003 = unboxBool t1  in
          let uu____9004 = unboxBool t2  in (uu____9003, uu____9004)  in
        mkAnd uu____8998 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9007; rng = uu____9008;_}::[])
        ->
        let uu____9024 =
          let uu____9029 = unboxBool t1  in
          let uu____9030 = unboxBool t2  in (uu____9029, uu____9030)  in
        mkOr uu____9024 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9032; rng = uu____9033;_}::[])
        -> let uu____9049 = unboxBool t1  in mkNot uu____9049 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9053; rng = uu____9054;_}::[])
        when
        let uu____9070 = getBoxedInteger t0  in FStar_Util.is_some uu____9070
        ->
        let sz =
          let uu____9077 = getBoxedInteger t0  in
          match uu____9077 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9085 -> failwith "impossible"  in
        let uu____9091 =
          let uu____9096 = unboxBitVec sz t1  in
          let uu____9097 = unboxBitVec sz t2  in (uu____9096, uu____9097)  in
        mkBvUlt uu____9091 t.rng
    | App
        (Var
         "Prims.equals",uu____9098::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9102;
                                      rng = uu____9103;_}::uu____9104::[])
        when
        let uu____9120 = getBoxedInteger t0  in FStar_Util.is_some uu____9120
        ->
        let sz =
          let uu____9127 = getBoxedInteger t0  in
          match uu____9127 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9135 -> failwith "impossible"  in
        let uu____9141 =
          let uu____9146 = unboxBitVec sz t1  in
          let uu____9147 = unboxBitVec sz t2  in (uu____9146, uu____9147)  in
        mkBvUlt uu____9141 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___19_9152 = unboxBool t1  in
        {
          tm = (uu___19_9152.tm);
          freevars = (uu___19_9152.freevars);
          rng = (t.rng)
        }
    | uu____9153 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9214 = FStar_Options.unthrottle_inductives ()  in
        if uu____9214
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
    let uu____9347 =
      let uu____9348 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9348 t t.rng  in
    FStar_All.pipe_right uu____9347 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9366 =
        let uu____9374 = let uu____9377 = mkInteger' i norng  in [uu____9377]
           in
        ("FString_const", uu____9374)  in
      mkApp uu____9366 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9408 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9408 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9455 =
         let uu____9463 =
           let uu____9466 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9466]  in
         ("SFuel", uu____9463)  in
       mkApp uu____9455 norng)
  
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
            let uu____9514 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9514
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
      let uu____9577 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9577
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9597 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9597
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9608 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9608
  