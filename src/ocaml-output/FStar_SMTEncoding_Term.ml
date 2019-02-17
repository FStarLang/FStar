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
    match projectee with | Integer _0 -> true | uu____855 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____879 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____910 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____960 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____1017 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1100 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1145 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1191 -> false
  
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
    match projectee with | Name _0 -> true | uu____1415 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1435 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1456 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1646 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1669 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1735 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1794 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1815 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1845 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1886 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1907 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1933 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1961 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1972 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1983 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1994 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____2012 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2049 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2060 -> false
  
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
          let uu____2234 =
            let uu____2235 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____2261 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2235
            }  in
          [uu____2234]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2275 =
      let uu____2276 =
        FStar_List.collect
          (fun uu___11_2283  ->
             match uu___11_2283 with
             | Assume a -> [a.assumption_name]
             | uu____2290 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2276
      }  in
    [uu____2275]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2327  -> match uu____2327 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____2347 = x  in
    match uu____2347 with | (nm,uu____2350,uu____2351) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____2362 = x  in
    match uu____2362 with | (uu____2363,sort,uu____2365) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____2377 = x  in
    match uu____2377 with | (uu____2379,uu____2380,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____2398 = fv_name x  in
      let uu____2400 = fv_name y  in uu____2398 = uu____2400
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2434 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___12_2445  ->
    match uu___12_2445 with
    | { tm = FreeV x; freevars = uu____2447; rng = uu____2448;_} -> fv_sort x
    | uu____2469 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___13_2476  ->
    match uu___13_2476 with
    | { tm = FreeV fv; freevars = uu____2478; rng = uu____2479;_} -> fv
    | uu____2500 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2528 -> []
    | BoundV uu____2538 -> []
    | FreeV fv -> [fv]
    | App (uu____2573,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2587,uu____2588,uu____2589,uu____2590,t1) -> freevars t1
    | Labeled (t1,uu____2611,uu____2612) -> freevars t1
    | LblPos (t1,uu____2616) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2639 = FStar_ST.op_Bang t.freevars  in
    match uu____2639 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2737 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2737  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___14_2816  ->
    match uu___14_2816 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___15_2826  ->
    match uu___15_2826 with
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
        let uu____2861 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2861
    | NatToBv n1 ->
        let uu____2866 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2866
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___16_2880  ->
    match uu___16_2880 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2890 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2890
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____2910 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____2910
    | FreeV x ->
        let uu____2922 = fv_name x  in
        let uu____2924 =
          let uu____2926 = let uu____2928 = fv_sort x  in strSort uu____2928
             in
          Prims.strcat ":" uu____2926  in
        Prims.strcat uu____2922 uu____2924
    | App (op,tms) ->
        let uu____2936 =
          let uu____2938 = op_to_string op  in
          let uu____2940 =
            let uu____2942 =
              let uu____2944 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2944 (FStar_String.concat " ")  in
            Prims.strcat uu____2942 ")"  in
          Prims.strcat uu____2938 uu____2940  in
        Prims.strcat "(" uu____2936
    | Labeled (t1,r1,r2) ->
        let uu____2961 = hash_of_term t1  in
        let uu____2963 =
          let uu____2965 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____2965  in
        Prims.strcat uu____2961 uu____2963
    | LblPos (t1,r) ->
        let uu____2971 =
          let uu____2973 = hash_of_term t1  in
          Prims.strcat uu____2973
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____2971
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____3001 =
          let uu____3003 =
            let uu____3005 =
              let uu____3007 =
                let uu____3009 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____3009 (FStar_String.concat " ")  in
              let uu____3019 =
                let uu____3021 =
                  let uu____3023 = hash_of_term body  in
                  let uu____3025 =
                    let uu____3027 =
                      let uu____3029 = weightToSmt wopt  in
                      let uu____3031 =
                        let uu____3033 =
                          let uu____3035 =
                            let uu____3037 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____3056 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____3056
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____3037
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____3035 "))"  in
                        Prims.strcat " " uu____3033  in
                      Prims.strcat uu____3029 uu____3031  in
                    Prims.strcat " " uu____3027  in
                  Prims.strcat uu____3023 uu____3025  in
                Prims.strcat ")(! " uu____3021  in
              Prims.strcat uu____3007 uu____3019  in
            Prims.strcat " (" uu____3005  in
          Prims.strcat (qop_to_string qop) uu____3003  in
        Prims.strcat "(" uu____3001
    | Let (es,body) ->
        let uu____3083 =
          let uu____3085 =
            let uu____3087 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____3087 (FStar_String.concat " ")  in
          let uu____3097 =
            let uu____3099 =
              let uu____3101 = hash_of_term body  in
              Prims.strcat uu____3101 ")"  in
            Prims.strcat ") " uu____3099  in
          Prims.strcat uu____3085 uu____3097  in
        Prims.strcat "(let (" uu____3083

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.strcat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3162 =
      let uu____3164 = FStar_Util.string_of_int sz  in
      Prims.strcat "BoxBitVec" uu____3164  in
    mkBoxFunctions uu____3162
  
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3181 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3181 = "Box") &&
        (let uu____3188 =
           let uu____3190 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3190  in
         Prims.op_Negation uu____3188)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3214 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3214; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3300 =
        let uu____3301 = FStar_Util.ensure_decimal i  in Integer uu____3301
         in
      mk uu____3300 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3316 = FStar_Util.string_of_int i  in mkInteger uu____3316 r
  
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3381  ->
    fun r  -> match uu____3381 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3411) -> mkFalse r
      | App (FalseOp ,uu____3416) -> mkTrue r
      | uu____3421 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3437  ->
    fun r  ->
      match uu____3437 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3445),uu____3446) -> t2
           | (uu____3451,App (TrueOp ,uu____3452)) -> t1
           | (App (FalseOp ,uu____3457),uu____3458) -> mkFalse r
           | (uu____3463,App (FalseOp ,uu____3464)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3481,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3490) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3497 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3517  ->
    fun r  ->
      match uu____3517 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3525),uu____3526) -> mkTrue r
           | (uu____3531,App (TrueOp ,uu____3532)) -> mkTrue r
           | (App (FalseOp ,uu____3537),uu____3538) -> t2
           | (uu____3543,App (FalseOp ,uu____3544)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3561,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3570) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3577 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3597  ->
    fun r  ->
      match uu____3597 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3605,App (TrueOp ,uu____3606)) -> mkTrue r
           | (App (FalseOp ,uu____3611),uu____3612) -> mkTrue r
           | (App (TrueOp ,uu____3617),uu____3618) -> t2
           | (uu____3623,App (Imp ,t1'::t2'::[])) ->
               let uu____3628 =
                 let uu____3635 =
                   let uu____3638 = mkAnd (t1, t1') r  in [uu____3638; t2']
                    in
                 (Imp, uu____3635)  in
               mkApp' uu____3628 r
           | uu____3641 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3666  ->
      fun r  -> match uu____3666 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3826  ->
      fun r  ->
        match uu____3826 with
        | (t1,t2) ->
            let uu____3835 =
              let uu____3842 =
                let uu____3845 =
                  let uu____3848 = mkNatToBv sz t2 r  in [uu____3848]  in
                t1 :: uu____3845  in
              (BvShl, uu____3842)  in
            mkApp' uu____3835 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3870  ->
      fun r  ->
        match uu____3870 with
        | (t1,t2) ->
            let uu____3879 =
              let uu____3886 =
                let uu____3889 =
                  let uu____3892 = mkNatToBv sz t2 r  in [uu____3892]  in
                t1 :: uu____3889  in
              (BvShr, uu____3886)  in
            mkApp' uu____3879 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3914  ->
      fun r  ->
        match uu____3914 with
        | (t1,t2) ->
            let uu____3923 =
              let uu____3930 =
                let uu____3933 =
                  let uu____3936 = mkNatToBv sz t2 r  in [uu____3936]  in
                t1 :: uu____3933  in
              (BvUdiv, uu____3930)  in
            mkApp' uu____3923 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3958  ->
      fun r  ->
        match uu____3958 with
        | (t1,t2) ->
            let uu____3967 =
              let uu____3974 =
                let uu____3977 =
                  let uu____3980 = mkNatToBv sz t2 r  in [uu____3980]  in
                t1 :: uu____3977  in
              (BvMod, uu____3974)  in
            mkApp' uu____3967 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4002  ->
      fun r  ->
        match uu____4002 with
        | (t1,t2) ->
            let uu____4011 =
              let uu____4018 =
                let uu____4021 =
                  let uu____4024 = mkNatToBv sz t2 r  in [uu____4024]  in
                t1 :: uu____4021  in
              (BvMul, uu____4018)  in
            mkApp' uu____4011 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4066  ->
    fun r  ->
      match uu____4066 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4085 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4222  ->
    fun r  ->
      match uu____4222 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4233) -> t2
           | App (FalseOp ,uu____4238) -> t3
           | uu____4243 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4244),App (TrueOp ,uu____4245)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4254),uu____4255) ->
                    let uu____4260 =
                      let uu____4265 = mkNot t1 t1.rng  in (uu____4265, t3)
                       in
                    mkImp uu____4260 r
                | (uu____4266,App (TrueOp ,uu____4267)) -> mkImp (t1, t2) r
                | (uu____4272,uu____4273) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4329 -> FStar_Pervasives_Native.None
      | BoundV uu____4331 -> FStar_Pervasives_Native.None
      | FreeV uu____4333 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4357 -> true
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
            | BvUext uu____4389 -> false
            | NatToBv uu____4392 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4403,uu____4404) -> aux t2
      | Quant uu____4407 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4427 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4442 = aux t1  in
          (match uu____4442 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None  -> aux_l ts1)
     in aux t
  
let rec (print_smt_term : term -> Prims.string) =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4477 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4477
    | FreeV fv ->
        let uu____4489 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4489
    | App (op,l) ->
        let uu____4498 = op_to_string op  in
        let uu____4500 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4498 uu____4500
    | Labeled (t1,r1,r2) ->
        let uu____4508 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4508
    | LblPos (t1,s) ->
        let uu____4515 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4515
    | Quant (qop,l,uu____4520,uu____4521,t1) ->
        let uu____4541 = print_smt_term_list_list l  in
        let uu____4543 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4541
          uu____4543
    | Let (es,body) ->
        let uu____4552 = print_smt_term_list es  in
        let uu____4554 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4552 uu____4554

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4561 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4561 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4588 =
             let uu____4590 =
               let uu____4592 = print_smt_term_list l1  in
               Prims.strcat uu____4592 " ] "  in
             Prims.strcat "; [ " uu____4590  in
           Prims.strcat s uu____4588) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4632  ->
        match uu____4632 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4701 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4701 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4716 =
                         let uu____4722 =
                           let uu____4724 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4724
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____4722)
                          in
                       FStar_Errors.log_issue r uu____4716);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4735) -> body
               | uu____4740 ->
                   let uu____4741 =
                     let uu____4742 =
                       let uu____4762 = all_pats_ok pats  in
                       (qop, uu____4762, wopt, vars, body)  in
                     Quant uu____4742  in
                   mk uu____4741 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4791  ->
    fun r  ->
      match uu____4791 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4837 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4837 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4870 = FStar_ST.op_Bang t1.freevars  in
        match uu____4870 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4944 ->
            (match t1.tm with
             | Integer uu____4957 -> t1
             | BoundV uu____4959 -> t1
             | FreeV x ->
                 let uu____4970 = index_of1 x  in
                 (match uu____4970 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____4984 =
                   let uu____4991 = FStar_List.map (aux ix) tms  in
                   (op, uu____4991)  in
                 mkApp' uu____4984 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____5001 =
                   let uu____5002 =
                     let uu____5010 = aux ix t2  in (uu____5010, r1, r2)  in
                   Labeled uu____5002  in
                 mk uu____5001 t2.rng
             | LblPos (t2,r) ->
                 let uu____5016 =
                   let uu____5017 =
                     let uu____5023 = aux ix t2  in (uu____5023, r)  in
                   LblPos uu____5017  in
                 mk uu____5016 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____5049 =
                   let uu____5069 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____5090 = aux (ix + n1) body  in
                   (qop, uu____5069, wopt, vars, uu____5090)  in
                 mkQuant t1.rng false uu____5049
             | Let (es,body) ->
                 let uu____5111 =
                   FStar_List.fold_left
                     (fun uu____5131  ->
                        fun e  ->
                          match uu____5131 with
                          | (ix1,l) ->
                              let uu____5155 =
                                let uu____5158 = aux ix1 e  in uu____5158 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5155))
                     (ix, []) es
                    in
                 (match uu____5111 with
                  | (ix1,es_rev) ->
                      let uu____5174 =
                        let uu____5181 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5181)  in
                      mkLet uu____5174 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5217 -> t1
        | FreeV uu____5219 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5244 =
              let uu____5251 = FStar_List.map (aux shift) tms2  in
              (op, uu____5251)  in
            mkApp' uu____5244 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5261 =
              let uu____5262 =
                let uu____5270 = aux shift t2  in (uu____5270, r1, r2)  in
              Labeled uu____5262  in
            mk uu____5261 t2.rng
        | LblPos (t2,r) ->
            let uu____5276 =
              let uu____5277 =
                let uu____5283 = aux shift t2  in (uu____5283, r)  in
              LblPos uu____5277  in
            mk uu____5276 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5315 =
              let uu____5335 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5352 = aux shift1 body  in
              (qop, uu____5335, wopt, vars, uu____5352)  in
            mkQuant t1.rng false uu____5315
        | Let (es,body) ->
            let uu____5369 =
              FStar_List.fold_left
                (fun uu____5389  ->
                   fun e  ->
                     match uu____5389 with
                     | (ix,es1) ->
                         let uu____5413 =
                           let uu____5416 = aux shift e  in uu____5416 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5413))
                (shift, []) es
               in
            (match uu____5369 with
             | (shift1,es_rev) ->
                 let uu____5432 =
                   let uu____5439 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5439)  in
                 mkLet uu____5432 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5459 = abstr [fv] t  in inst [s] uu____5459
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5489  ->
      match uu____5489 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5532 =
            let uu____5552 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5569 = FStar_List.map fv_sort vars  in
            let uu____5572 = abstr vars body  in
            (qop, uu____5552, wopt, uu____5569, uu____5572)  in
          mkQuant r true uu____5532
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5603  ->
      match uu____5603 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5662  ->
      match uu____5662 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5737  ->
      match uu____5737 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5800  ->
      match uu____5800 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5851  ->
    fun r  ->
      match uu____5851 with
      | (bindings,body) ->
          let uu____5877 = FStar_List.split bindings  in
          (match uu____5877 with
           | (vars,es) ->
               let uu____5896 =
                 let uu____5903 = abstr vars body  in (es, uu____5903)  in
               mkLet uu____5896 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5925  ->
    match uu____5925 with
    | (nm,vars,s,tm,c) ->
        let uu____5950 =
          let uu____5964 = FStar_List.map fv_sort vars  in
          let uu____5967 = abstr vars tm  in
          (nm, uu____5964, s, uu____5967, c)  in
        DefineFun uu____5950
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5978 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5978
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____5996  ->
    fun id1  ->
      match uu____5996 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let a =
            let uu____6012 =
              let uu____6013 =
                let uu____6018 = mkInteger' id1 norng  in
                let uu____6019 =
                  let uu____6020 =
                    let uu____6028 = constr_id_of_sort sort  in
                    let uu____6030 =
                      let uu____6033 = mkApp (tok_name, []) norng  in
                      [uu____6033]  in
                    (uu____6028, uu____6030)  in
                  mkApp uu____6020 norng  in
                (uu____6018, uu____6019)  in
              mkEq uu____6013 norng  in
            let uu____6040 = escape a_name  in
            {
              assumption_term = uu____6012;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____6040;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____6066  ->
      match uu____6066 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____6106 =
                        let uu____6107 =
                          let uu____6113 =
                            let uu____6115 = FStar_Util.string_of_int i  in
                            Prims.strcat "x_" uu____6115  in
                          (uu____6113, s)  in
                        mk_fv uu____6107  in
                      mkFreeV uu____6106 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6143 =
              let uu____6151 = constr_id_of_sort sort  in
              (uu____6151, [capp])  in
            mkApp uu____6143 norng  in
          let a_name = Prims.strcat "constructor_distinct_" name  in
          let a =
            let uu____6160 =
              let uu____6161 =
                let uu____6172 =
                  let uu____6173 =
                    let uu____6178 = mkInteger id2 norng  in
                    (uu____6178, cid_app)  in
                  mkEq uu____6173 norng  in
                ([[capp]], bvar_names, uu____6172)  in
              mkForall rng uu____6161  in
            let uu____6187 = escape a_name  in
            {
              assumption_term = uu____6160;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6187;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6212  ->
      match uu____6212 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6245 = FStar_Util.string_of_int i  in
            Prims.strcat "x_" uu____6245  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6280 =
              let uu____6281 =
                let uu____6287 = bvar_name i  in (uu____6287, s)  in
              mk_fv uu____6281  in
            FStar_All.pipe_left mkFreeV uu____6280  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6323  ->
                      match uu____6323 with
                      | (uu____6333,s,uu____6335) ->
                          let uu____6340 = bvar i s  in uu____6340 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6368 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6406  ->
                      match uu____6406 with
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
                              let uu____6439 =
                                let uu____6440 =
                                  let uu____6451 =
                                    let uu____6452 =
                                      let uu____6457 =
                                        let uu____6458 = bvar i s  in
                                        uu____6458 norng  in
                                      (cproj_app, uu____6457)  in
                                    mkEq uu____6452 norng  in
                                  ([[capp]], bvar_names, uu____6451)  in
                                mkForall rng uu____6440  in
                              let uu____6471 =
                                escape
                                  (Prims.strcat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6439;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6471;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6368 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6496  ->
      match uu____6496 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6544  ->
                    match uu____6544 with
                    | (uu____6553,sort1,uu____6555) -> sort1))
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
              let uu____6580 =
                let uu____6585 =
                  let uu____6586 =
                    let uu____6594 = constr_id_of_sort sort  in
                    (uu____6594, [xx])  in
                  mkApp uu____6586 norng  in
                let uu____6599 =
                  let uu____6600 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6600 norng  in
                (uu____6585, uu____6599)  in
              mkEq uu____6580 norng  in
            let uu____6602 =
              let uu____6621 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6685  ->
                          match uu____6685 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6715 = mkApp (proj, [xx]) norng  in
                                (uu____6715, [])
                              else
                                (let fi =
                                   let uu____6724 =
                                     let uu____6730 =
                                       let uu____6732 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "f_" uu____6732  in
                                     (uu____6730, s)  in
                                   mk_fv uu____6724  in
                                 let uu____6736 = mkFreeV fi norng  in
                                 (uu____6736, [fi]))))
                 in
              FStar_All.pipe_right uu____6621 FStar_List.split  in
            match uu____6602 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6833 =
                    let uu____6838 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6838)  in
                  mkEq uu____6833 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6851 ->
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
          let uu____6886 =
            let uu____6889 =
              let uu____6890 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6890  in
            uu____6889 :: cdecl :: cid :: projs  in
          let uu____6893 =
            let uu____6896 =
              let uu____6899 =
                let uu____6900 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6900  in
              [uu____6899]  in
            FStar_List.append [disc] uu____6896  in
          FStar_List.append uu____6886 uu____6893
  
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
          let uu____6952 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7001  ->
                    fun s  ->
                      match uu____7001 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____7046 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1
                             in
                          let nm =
                            let uu____7057 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____7057  in
                          let names2 =
                            let uu____7062 = mk_fv (nm, s)  in uu____7062 ::
                              names1
                             in
                          let b =
                            let uu____7066 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____7066  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6952 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____7137 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7137 with
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
              (let uu____7301 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7301)
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
                               "Prims.guard_free",{ tm = BoundV uu____7347;
                                                    freevars = uu____7348;
                                                    rng = uu____7349;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7370 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | BoundV i ->
              let uu____7446 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7446 fv_name
          | FreeV x when fv_force x ->
              let uu____7457 =
                let uu____7459 = fv_name x  in
                Prims.strcat uu____7459 " Dummy_value)"  in
              Prims.strcat "(" uu____7457
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7481 = op_to_string op  in
              let uu____7483 =
                let uu____7485 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7485 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7481 uu____7483
          | Labeled (t2,uu____7497,uu____7498) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7505 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7505 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7533 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7533 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7586 ->
                         let uu____7591 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7610 =
                                     let uu____7612 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7620 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7620) pats2
                                        in
                                     FStar_String.concat " " uu____7612  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7610))
                            in
                         FStar_All.pipe_right uu____7591
                           (FStar_String.concat "\n")
                      in
                   let uu____7630 =
                     let uu____7634 =
                       let uu____7638 =
                         let uu____7642 = aux1 n2 names2 body  in
                         let uu____7644 =
                           let uu____7648 = weightToSmt wopt  in
                           [uu____7648; pats_str; qid]  in
                         uu____7642 :: uu____7644  in
                       binders1 :: uu____7638  in
                     (qop_to_string qop) :: uu____7634  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7630)
          | Let (es,body) ->
              let uu____7664 =
                FStar_List.fold_left
                  (fun uu____7697  ->
                     fun e  ->
                       match uu____7697 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7740 = FStar_Util.string_of_int n0  in
                             Prims.strcat "@lb" uu____7740  in
                           let names01 =
                             let uu____7746 = mk_fv (nm, Term_sort)  in
                             uu____7746 :: names0  in
                           let b =
                             let uu____7750 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7750  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7664 with
               | (names2,binders,n2) ->
                   let uu____7784 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7784)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7800 = FStar_Range.string_of_range t1.rng  in
            let uu____7802 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7800
              uu____7802 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___17_7824  ->
      match uu___17_7824 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7835 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7835 (FStar_String.concat " ")  in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu____7857 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7932 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7932 (FStar_String.concat "\n")  in
            let uu____7942 = FStar_Options.keep_query_captions ()  in
            if uu____7942
            then
              let uu____7946 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7948 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7946 uu____7948
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7957 =
                let uu____7959 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.strcat "; " (Prims.strcat s "\n")))
                   in
                FStar_All.pipe_right uu____7959 (FStar_String.concat "")  in
              Prims.strcat "\n" uu____7957
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8000 = caption_to_string print_captions c  in
            let uu____8002 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8000 f
              (FStar_String.concat " " l) uu____8002
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8017 = name_macro_binders arg_sorts  in
            (match uu____8017 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8041 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8041 body  in
                 let uu____8046 = caption_to_string print_captions c  in
                 let uu____8048 = strSort retsort  in
                 let uu____8050 =
                   let uu____8052 = escape f  in
                   termToSmt print_captions uu____8052 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8046 f (FStar_String.concat " " binders) uu____8048
                   uu____8050)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___18_8079  ->
                      match uu___18_8079 with
                      | Name n1 ->
                          let uu____8082 = FStar_Ident.text_of_lid n1  in
                          Prims.strcat "Name " uu____8082
                      | Namespace ns ->
                          let uu____8086 = FStar_Ident.text_of_lid ns  in
                          Prims.strcat "Namespace " uu____8086
                      | Tag t -> Prims.strcat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8096 =
                  let uu____8098 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8098  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8096
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8109 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8111 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8109
              fids uu____8111 n1
        | Eval t ->
            let uu____8115 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8115
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8122 -> ""
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
      let uu____8143 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8143 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8154 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8154 (FStar_String.concat "\n")

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
      ("LexCons",
        [("LexCons_0", Term_sort, true);
        ("LexCons_1", Term_sort, true);
        ("LexCons_2", Term_sort, true)], Term_sort, (Prims.parse_int "11"),
        true)]
       in
    let bcons =
      let uu____8274 =
        let uu____8278 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8278
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8274 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8309 =
      let uu____8310 =
        let uu____8312 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8312  in
      let uu____8321 =
        let uu____8324 =
          let uu____8325 =
            let uu____8327 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8327  in
          (uu____8325, (BitVec_sort sz), true)  in
        [uu____8324]  in
      (uu____8310, uu____8321, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8309 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8370  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8395 =
       let uu____8397 = FStar_ST.op_Bang __range_c  in
       uu____8397 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8395);
    (let uu____8442 =
       let uu____8450 = let uu____8453 = mkInteger' i norng  in [uu____8453]
          in
       ("Range_const", uu____8450)  in
     mkApp uu____8442 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8496 =
        let uu____8504 = let uu____8507 = mkInteger' i norng  in [uu____8507]
           in
        ("Tm_uvar", uu____8504)  in
      mkApp uu____8496 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8550 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8574 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8574 u v1 t
  
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
      let uu____8649 =
        let uu____8651 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8651  in
      let uu____8660 =
        let uu____8662 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8662  in
      elim_box true uu____8649 uu____8660 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8685 =
        let uu____8687 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8687  in
      let uu____8696 =
        let uu____8698 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8698  in
      elim_box true uu____8685 uu____8696 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | uu____8721 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | uu____8735 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8761 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8761
         | uu____8764 -> FStar_Pervasives_Native.None)
    | uu____8766 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8784::t1::t2::[]);
                       freevars = uu____8787; rng = uu____8788;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8807::t1::t2::[]);
                       freevars = uu____8810; rng = uu____8811;_}::[])
        -> let uu____8830 = mkEq (t1, t2) norng  in mkNot uu____8830 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8833; rng = uu____8834;_}::[])
        ->
        let uu____8853 =
          let uu____8858 = unboxInt t1  in
          let uu____8859 = unboxInt t2  in (uu____8858, uu____8859)  in
        mkLTE uu____8853 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8862; rng = uu____8863;_}::[])
        ->
        let uu____8882 =
          let uu____8887 = unboxInt t1  in
          let uu____8888 = unboxInt t2  in (uu____8887, uu____8888)  in
        mkLT uu____8882 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8891; rng = uu____8892;_}::[])
        ->
        let uu____8911 =
          let uu____8916 = unboxInt t1  in
          let uu____8917 = unboxInt t2  in (uu____8916, uu____8917)  in
        mkGTE uu____8911 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8920; rng = uu____8921;_}::[])
        ->
        let uu____8940 =
          let uu____8945 = unboxInt t1  in
          let uu____8946 = unboxInt t2  in (uu____8945, uu____8946)  in
        mkGT uu____8940 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8949; rng = uu____8950;_}::[])
        ->
        let uu____8969 =
          let uu____8974 = unboxBool t1  in
          let uu____8975 = unboxBool t2  in (uu____8974, uu____8975)  in
        mkAnd uu____8969 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____8978; rng = uu____8979;_}::[])
        ->
        let uu____8998 =
          let uu____9003 = unboxBool t1  in
          let uu____9004 = unboxBool t2  in (uu____9003, uu____9004)  in
        mkOr uu____8998 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9006; rng = uu____9007;_}::[])
        -> let uu____9026 = unboxBool t1  in mkNot uu____9026 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9030; rng = uu____9031;_}::[])
        when
        let uu____9050 = getBoxedInteger t0  in FStar_Util.is_some uu____9050
        ->
        let sz =
          let uu____9057 = getBoxedInteger t0  in
          match uu____9057 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9065 -> failwith "impossible"  in
        let uu____9071 =
          let uu____9076 = unboxBitVec sz t1  in
          let uu____9077 = unboxBitVec sz t2  in (uu____9076, uu____9077)  in
        mkBvUlt uu____9071 t.rng
    | App
        (Var
         "Prims.equals",uu____9078::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9082;
                                      rng = uu____9083;_}::uu____9084::[])
        when
        let uu____9103 = getBoxedInteger t0  in FStar_Util.is_some uu____9103
        ->
        let sz =
          let uu____9110 = getBoxedInteger t0  in
          match uu____9110 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9118 -> failwith "impossible"  in
        let uu____9124 =
          let uu____9129 = unboxBitVec sz t1  in
          let uu____9130 = unboxBitVec sz t2  in (uu____9129, uu____9130)  in
        mkBvUlt uu____9124 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___19_9135 = unboxBool t1  in
        {
          tm = (uu___19_9135.tm);
          freevars = (uu___19_9135.freevars);
          rng = (t.rng)
        }
    | uu____9136 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9197 = FStar_Options.unthrottle_inductives ()  in
        if uu____9197
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
    let uu____9330 =
      let uu____9331 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9331 t t.rng  in
    FStar_All.pipe_right uu____9330 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9349 =
        let uu____9357 = let uu____9360 = mkInteger' i norng  in [uu____9360]
           in
        ("FString_const", uu____9357)  in
      mkApp uu____9349 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9391 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9391 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9438 =
         let uu____9446 =
           let uu____9449 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9449]  in
         ("SFuel", uu____9446)  in
       mkApp uu____9438 norng)
  
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
            let uu____9497 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9497
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
      let uu____9560 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9560
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9580 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9580
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9591 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9591
  
let (dummy_sort : sort) = Sort "Dummy_sort" 