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
    match projectee with | Bool_sort  -> true | uu____60 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____71 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____82 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____93 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____104 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____117 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____143 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____178 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____210 -> false
  
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
        let uu____237 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____237
    | Array (s1,s2) ->
        let uu____242 = strSort s1  in
        let uu____244 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____242 uu____244
    | Arrow (s1,s2) ->
        let uu____249 = strSort s1  in
        let uu____251 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____249 uu____251
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
    match projectee with | TrueOp  -> true | uu____283 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____294 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____305 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____316 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____327 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  -> match projectee with | Imp  -> true | uu____338 -> false 
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  -> match projectee with | Iff  -> true | uu____349 -> false 
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____360 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____371 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | LTE  -> true | uu____382 -> false 
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____393 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  -> match projectee with | GTE  -> true | uu____404 -> false 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____415 -> false 
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____426 -> false 
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____437 -> false 
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____448 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mul  -> true | uu____459 -> false 
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____470 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____481 -> false 
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____492 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____503 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BvOr  -> true | uu____514 -> false 
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____525 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____536 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____547 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____558 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____569 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____580 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____591 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____602 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____615 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____638 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____659 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  -> match projectee with | ITE  -> true | uu____670 -> false 
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____683 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____704 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____715 -> false
  
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
    match projectee with | Integer _0 -> true | uu____864 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____887 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____910 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____940 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____989 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____1045 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1127 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1171 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1216 -> false
  
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
    match projectee with | Name _0 -> true | uu____1406 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1425 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1445 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1634 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1657 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1722 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1780 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1800 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1829 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1869 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1889 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1914 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1941 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1952 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1963 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1974 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1992 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2028 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2039 -> false
  
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
          let uu____2213 =
            let uu____2214 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____2240 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2214
            }  in
          [uu____2213]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2254 =
      let uu____2255 =
        FStar_List.collect
          (fun uu___0_2262  ->
             match uu___0_2262 with
             | Assume a -> [a.assumption_name]
             | uu____2269 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2255
      }  in
    [uu____2254]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2306  -> match uu____2306 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____2326 = x  in
    match uu____2326 with | (nm,uu____2329,uu____2330) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____2341 = x  in
    match uu____2341 with | (uu____2342,sort,uu____2344) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____2356 = x  in
    match uu____2356 with | (uu____2358,uu____2359,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____2377 = fv_name x  in
      let uu____2379 = fv_name y  in uu____2377 = uu____2379
  
let (fvs_subset_of : fvs -> fvs -> Prims.bool) =
  fun x  ->
    fun y  ->
      let cmp_fv x1 y1 =
        let uu____2406 = fv_name x1  in
        let uu____2408 = fv_name y1  in
        FStar_Util.compare uu____2406 uu____2408  in
      let uu____2410 = FStar_Util.as_set x cmp_fv  in
      let uu____2429 = FStar_Util.as_set y cmp_fv  in
      FStar_Util.set_is_subset_of uu____2410 uu____2429
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2487 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___1_2498  ->
    match uu___1_2498 with
    | { tm = FreeV x; freevars = uu____2500; rng = uu____2501;_} -> fv_sort x
    | uu____2522 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___2_2529  ->
    match uu___2_2529 with
    | { tm = FreeV fv; freevars = uu____2531; rng = uu____2532;_} -> fv
    | uu____2553 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2581 -> []
    | Real uu____2591 -> []
    | BoundV uu____2601 -> []
    | FreeV fv when fv_force fv -> []
    | FreeV fv -> [fv]
    | App (uu____2653,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2667,uu____2668,uu____2669,uu____2670,t1) -> freevars t1
    | Labeled (t1,uu____2691,uu____2692) -> freevars t1
    | LblPos (t1,uu____2696) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2719 = FStar_ST.op_Bang t.freevars  in
    match uu____2719 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2817 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2817  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2896  ->
    match uu___3_2896 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___4_2906  ->
    match uu___4_2906 with
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
        let uu____2942 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2942
    | NatToBv n1 ->
        let uu____2947 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2947
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_2961  ->
    match uu___5_2961 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2971 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2971
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____2993 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____2993
    | FreeV x ->
        let uu____3005 = fv_name x  in
        let uu____3007 =
          let uu____3009 = let uu____3011 = fv_sort x  in strSort uu____3011
             in
          Prims.op_Hat ":" uu____3009  in
        Prims.op_Hat uu____3005 uu____3007
    | App (op,tms) ->
        let uu____3019 =
          let uu____3021 = op_to_string op  in
          let uu____3023 =
            let uu____3025 =
              let uu____3027 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____3027 (FStar_String.concat " ")  in
            Prims.op_Hat uu____3025 ")"  in
          Prims.op_Hat uu____3021 uu____3023  in
        Prims.op_Hat "(" uu____3019
    | Labeled (t1,r1,r2) ->
        let uu____3044 = hash_of_term t1  in
        let uu____3046 =
          let uu____3048 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____3048  in
        Prims.op_Hat uu____3044 uu____3046
    | LblPos (t1,r) ->
        let uu____3054 =
          let uu____3056 = hash_of_term t1  in
          Prims.op_Hat uu____3056
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____3054
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____3084 =
          let uu____3086 =
            let uu____3088 =
              let uu____3090 =
                let uu____3092 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____3092 (FStar_String.concat " ")  in
              let uu____3102 =
                let uu____3104 =
                  let uu____3106 = hash_of_term body  in
                  let uu____3108 =
                    let uu____3110 =
                      let uu____3112 = weightToSmt wopt  in
                      let uu____3114 =
                        let uu____3116 =
                          let uu____3118 =
                            let uu____3120 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____3139 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____3139
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____3120
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____3118 "))"  in
                        Prims.op_Hat " " uu____3116  in
                      Prims.op_Hat uu____3112 uu____3114  in
                    Prims.op_Hat " " uu____3110  in
                  Prims.op_Hat uu____3106 uu____3108  in
                Prims.op_Hat ")(! " uu____3104  in
              Prims.op_Hat uu____3090 uu____3102  in
            Prims.op_Hat " (" uu____3088  in
          Prims.op_Hat (qop_to_string qop) uu____3086  in
        Prims.op_Hat "(" uu____3084
    | Let (es,body) ->
        let uu____3166 =
          let uu____3168 =
            let uu____3170 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____3170 (FStar_String.concat " ")  in
          let uu____3180 =
            let uu____3182 =
              let uu____3184 = hash_of_term body  in
              Prims.op_Hat uu____3184 ")"  in
            Prims.op_Hat ") " uu____3182  in
          Prims.op_Hat uu____3168 uu____3180  in
        Prims.op_Hat "(let (" uu____3166

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3245 =
      let uu____3247 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____3247  in
    mkBoxFunctions uu____3245
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3272 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3272 = "Box") &&
        (let uu____3279 =
           let uu____3281 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3281  in
         Prims.op_Negation uu____3279)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3305 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3305; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3369 =
        let uu____3370 = FStar_Util.ensure_decimal i  in Integer uu____3370
         in
      mk uu____3369 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3385 = FStar_Util.string_of_int i  in mkInteger uu____3385 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3463  ->
    fun r  -> match uu____3463 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3493) -> mkFalse r
      | App (FalseOp ,uu____3498) -> mkTrue r
      | uu____3503 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3519  ->
    fun r  ->
      match uu____3519 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3527),uu____3528) -> t2
           | (uu____3533,App (TrueOp ,uu____3534)) -> t1
           | (App (FalseOp ,uu____3539),uu____3540) -> mkFalse r
           | (uu____3545,App (FalseOp ,uu____3546)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3563,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3572) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3579 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3599  ->
    fun r  ->
      match uu____3599 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3607),uu____3608) -> mkTrue r
           | (uu____3613,App (TrueOp ,uu____3614)) -> mkTrue r
           | (App (FalseOp ,uu____3619),uu____3620) -> t2
           | (uu____3625,App (FalseOp ,uu____3626)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3643,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3652) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3659 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3679  ->
    fun r  ->
      match uu____3679 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3687,App (TrueOp ,uu____3688)) -> mkTrue r
           | (App (FalseOp ,uu____3693),uu____3694) -> mkTrue r
           | (App (TrueOp ,uu____3699),uu____3700) -> t2
           | (uu____3705,App (Imp ,t1'::t2'::[])) ->
               let uu____3710 =
                 let uu____3717 =
                   let uu____3720 = mkAnd (t1, t1') r  in [uu____3720; t2']
                    in
                 (Imp, uu____3717)  in
               mkApp' uu____3710 r
           | uu____3723 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3748  ->
      fun r  -> match uu____3748 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3908  ->
      fun r  ->
        match uu____3908 with
        | (t1,t2) ->
            let uu____3917 =
              let uu____3924 =
                let uu____3927 =
                  let uu____3930 = mkNatToBv sz t2 r  in [uu____3930]  in
                t1 :: uu____3927  in
              (BvShl, uu____3924)  in
            mkApp' uu____3917 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3952  ->
      fun r  ->
        match uu____3952 with
        | (t1,t2) ->
            let uu____3961 =
              let uu____3968 =
                let uu____3971 =
                  let uu____3974 = mkNatToBv sz t2 r  in [uu____3974]  in
                t1 :: uu____3971  in
              (BvShr, uu____3968)  in
            mkApp' uu____3961 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3996  ->
      fun r  ->
        match uu____3996 with
        | (t1,t2) ->
            let uu____4005 =
              let uu____4012 =
                let uu____4015 =
                  let uu____4018 = mkNatToBv sz t2 r  in [uu____4018]  in
                t1 :: uu____4015  in
              (BvUdiv, uu____4012)  in
            mkApp' uu____4005 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4040  ->
      fun r  ->
        match uu____4040 with
        | (t1,t2) ->
            let uu____4049 =
              let uu____4056 =
                let uu____4059 =
                  let uu____4062 = mkNatToBv sz t2 r  in [uu____4062]  in
                t1 :: uu____4059  in
              (BvMod, uu____4056)  in
            mkApp' uu____4049 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4084  ->
      fun r  ->
        match uu____4084 with
        | (t1,t2) ->
            let uu____4093 =
              let uu____4100 =
                let uu____4103 =
                  let uu____4106 = mkNatToBv sz t2 r  in [uu____4106]  in
                t1 :: uu____4103  in
              (BvMul, uu____4100)  in
            mkApp' uu____4093 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4148  ->
    fun r  ->
      match uu____4148 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4167 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4332  ->
    fun r  ->
      match uu____4332 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4343) -> t2
           | App (FalseOp ,uu____4348) -> t3
           | uu____4353 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4354),App (TrueOp ,uu____4355)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4364),uu____4365) ->
                    let uu____4370 =
                      let uu____4375 = mkNot t1 t1.rng  in (uu____4375, t3)
                       in
                    mkImp uu____4370 r
                | (uu____4376,App (TrueOp ,uu____4377)) -> mkImp (t1, t2) r
                | (uu____4382,uu____4383) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4439 -> FStar_Pervasives_Native.None
      | Real uu____4441 -> FStar_Pervasives_Native.None
      | BoundV uu____4443 -> FStar_Pervasives_Native.None
      | FreeV uu____4445 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4469 -> true
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
            | BvUext uu____4502 -> false
            | NatToBv uu____4505 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4516,uu____4517) -> aux t2
      | Quant uu____4520 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4540 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4555 = aux t1  in
          (match uu____4555 with
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
        let uu____4593 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4593
    | FreeV fv ->
        let uu____4605 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4605
    | App (op,l) ->
        let uu____4614 = op_to_string op  in
        let uu____4616 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4614 uu____4616
    | Labeled (t1,r1,r2) ->
        let uu____4624 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4624
    | LblPos (t1,s) ->
        let uu____4631 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4631
    | Quant (qop,l,uu____4636,uu____4637,t1) ->
        let uu____4657 = print_smt_term_list_list l  in
        let uu____4659 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4657
          uu____4659
    | Let (es,body) ->
        let uu____4668 = print_smt_term_list es  in
        let uu____4670 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4668 uu____4670

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4677 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4677 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4704 =
             let uu____4706 =
               let uu____4708 = print_smt_term_list l1  in
               Prims.op_Hat uu____4708 " ] "  in
             Prims.op_Hat "; [ " uu____4706  in
           Prims.op_Hat s uu____4704) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4748  ->
        match uu____4748 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4817 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4817 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4832 =
                         let uu____4838 =
                           let uu____4840 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4840
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____4838)
                          in
                       FStar_Errors.log_issue r uu____4832);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4851) -> body
               | uu____4856 ->
                   let uu____4857 =
                     let uu____4858 =
                       let uu____4878 = all_pats_ok pats  in
                       (qop, uu____4878, wopt, vars, body)  in
                     Quant uu____4858  in
                   mk uu____4857 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4907  ->
    fun r  ->
      match uu____4907 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4953 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4953 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4980 = FStar_ST.op_Bang t1.freevars  in
        match uu____4980 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____5054 ->
            (match t1.tm with
             | Integer uu____5067 -> t1
             | Real uu____5069 -> t1
             | BoundV uu____5071 -> t1
             | FreeV x ->
                 let uu____5082 = index_of1 x  in
                 (match uu____5082 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____5096 =
                   let uu____5103 = FStar_List.map (aux ix) tms  in
                   (op, uu____5103)  in
                 mkApp' uu____5096 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____5113 =
                   let uu____5114 =
                     let uu____5122 = aux ix t2  in (uu____5122, r1, r2)  in
                   Labeled uu____5114  in
                 mk uu____5113 t2.rng
             | LblPos (t2,r) ->
                 let uu____5128 =
                   let uu____5129 =
                     let uu____5135 = aux ix t2  in (uu____5135, r)  in
                   LblPos uu____5129  in
                 mk uu____5128 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____5161 =
                   let uu____5181 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____5198 = aux (ix + n1) body  in
                   (qop, uu____5181, wopt, vars, uu____5198)  in
                 mkQuant t1.rng false uu____5161
             | Let (es,body) ->
                 let uu____5215 =
                   FStar_List.fold_left
                     (fun uu____5235  ->
                        fun e  ->
                          match uu____5235 with
                          | (ix1,l) ->
                              let uu____5259 =
                                let uu____5262 = aux ix1 e  in uu____5262 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5259))
                     (ix, []) es
                    in
                 (match uu____5215 with
                  | (ix1,es_rev) ->
                      let uu____5278 =
                        let uu____5285 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5285)  in
                      mkLet uu____5278 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5321 -> t1
        | Real uu____5323 -> t1
        | FreeV uu____5325 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5346 =
              let uu____5353 = FStar_List.map (aux shift) tms2  in
              (op, uu____5353)  in
            mkApp' uu____5346 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5363 =
              let uu____5364 =
                let uu____5372 = aux shift t2  in (uu____5372, r1, r2)  in
              Labeled uu____5364  in
            mk uu____5363 t2.rng
        | LblPos (t2,r) ->
            let uu____5378 =
              let uu____5379 =
                let uu____5385 = aux shift t2  in (uu____5385, r)  in
              LblPos uu____5379  in
            mk uu____5378 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5413 =
              let uu____5433 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5450 = aux shift1 body  in
              (qop, uu____5433, wopt, vars, uu____5450)  in
            mkQuant t1.rng false uu____5413
        | Let (es,body) ->
            let uu____5467 =
              FStar_List.fold_left
                (fun uu____5487  ->
                   fun e  ->
                     match uu____5487 with
                     | (ix,es1) ->
                         let uu____5511 =
                           let uu____5514 = aux shift e  in uu____5514 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5511))
                (shift, []) es
               in
            (match uu____5467 with
             | (shift1,es_rev) ->
                 let uu____5530 =
                   let uu____5537 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5537)  in
                 mkLet uu____5530 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5557 = abstr [fv] t  in inst [s] uu____5557
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5587  ->
      match uu____5587 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5630 =
            let uu____5650 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5667 = FStar_List.map fv_sort vars  in
            let uu____5670 = abstr vars body  in
            (qop, uu____5650, wopt, uu____5667, uu____5670)  in
          mkQuant r true uu____5630
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5701  ->
      match uu____5701 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5760  ->
      match uu____5760 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5835  ->
      match uu____5835 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5898  ->
      match uu____5898 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5949  ->
    fun r  ->
      match uu____5949 with
      | (bindings,body) ->
          let uu____5975 = FStar_List.split bindings  in
          (match uu____5975 with
           | (vars,es) ->
               let uu____5994 =
                 let uu____6001 = abstr vars body  in (es, uu____6001)  in
               mkLet uu____5994 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____6023  ->
    match uu____6023 with
    | (nm,vars,s,tm,c) ->
        let uu____6048 =
          let uu____6062 = FStar_List.map fv_sort vars  in
          let uu____6065 = abstr vars tm  in
          (nm, uu____6062, s, uu____6065, c)  in
        DefineFun uu____6048
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____6076 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____6076
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____6094  ->
    fun id1  ->
      match uu____6094 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____6110 =
              let uu____6111 =
                let uu____6116 = mkInteger' id1 norng  in
                let uu____6117 =
                  let uu____6118 =
                    let uu____6126 = constr_id_of_sort sort  in
                    let uu____6128 =
                      let uu____6131 = mkApp (tok_name, []) norng  in
                      [uu____6131]  in
                    (uu____6126, uu____6128)  in
                  mkApp uu____6118 norng  in
                (uu____6116, uu____6117)  in
              mkEq uu____6111 norng  in
            let uu____6138 = escape a_name  in
            {
              assumption_term = uu____6110;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____6138;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____6164  ->
      match uu____6164 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____6204 =
                        let uu____6205 =
                          let uu____6211 =
                            let uu____6213 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____6213  in
                          (uu____6211, s)  in
                        mk_fv uu____6205  in
                      mkFreeV uu____6204 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6241 =
              let uu____6249 = constr_id_of_sort sort  in
              (uu____6249, [capp])  in
            mkApp uu____6241 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____6258 =
              let uu____6259 =
                let uu____6270 =
                  let uu____6271 =
                    let uu____6276 = mkInteger id2 norng  in
                    (uu____6276, cid_app)  in
                  mkEq uu____6271 norng  in
                ([[capp]], bvar_names, uu____6270)  in
              mkForall rng uu____6259  in
            let uu____6285 = escape a_name  in
            {
              assumption_term = uu____6258;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6285;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6310  ->
      match uu____6310 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6343 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____6343  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6372 =
              let uu____6373 =
                let uu____6379 = bvar_name i  in (uu____6379, s)  in
              mk_fv uu____6373  in
            FStar_All.pipe_left mkFreeV uu____6372  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6415  ->
                      match uu____6415 with
                      | (uu____6425,s,uu____6427) ->
                          let uu____6432 = bvar i s  in uu____6432 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6460 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6498  ->
                      match uu____6498 with
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
                              let uu____6531 =
                                let uu____6532 =
                                  let uu____6543 =
                                    let uu____6544 =
                                      let uu____6549 =
                                        let uu____6550 = bvar i s  in
                                        uu____6550 norng  in
                                      (cproj_app, uu____6549)  in
                                    mkEq uu____6544 norng  in
                                  ([[capp]], bvar_names, uu____6543)  in
                                mkForall rng uu____6532  in
                              let uu____6563 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6531;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6563;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6460 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6588  ->
      match uu____6588 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6636  ->
                    match uu____6636 with
                    | (uu____6645,sort1,uu____6647) -> sort1))
             in
          let cdecl =
            DeclFun
              (name, field_sorts, sort,
                (FStar_Pervasives_Native.Some "Constructor"))
             in
          let cid = fresh_constructor rng (name, field_sorts, sort, id1)  in
          let disc =
            let disc_name = Prims.op_Hat "is-" name  in
            let xfv = mk_fv ("x", sort)  in
            let xx = mkFreeV xfv norng  in
            let disc_eq =
              let uu____6672 =
                let uu____6677 =
                  let uu____6678 =
                    let uu____6686 = constr_id_of_sort sort  in
                    (uu____6686, [xx])  in
                  mkApp uu____6678 norng  in
                let uu____6691 =
                  let uu____6692 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6692 norng  in
                (uu____6677, uu____6691)  in
              mkEq uu____6672 norng  in
            let uu____6694 =
              let uu____6713 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6777  ->
                          match uu____6777 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6807 = mkApp (proj, [xx]) norng  in
                                (uu____6807, [])
                              else
                                (let fi =
                                   let uu____6816 =
                                     let uu____6822 =
                                       let uu____6824 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____6824  in
                                     (uu____6822, s)  in
                                   mk_fv uu____6816  in
                                 let uu____6828 = mkFreeV fi norng  in
                                 (uu____6828, [fi]))))
                 in
              FStar_All.pipe_right uu____6713 FStar_List.split  in
            match uu____6694 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6925 =
                    let uu____6930 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6930)  in
                  mkEq uu____6925 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6943 ->
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
          let uu____6978 =
            let uu____6981 =
              let uu____6982 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6982  in
            uu____6981 :: cdecl :: cid :: projs  in
          let uu____6985 =
            let uu____6988 =
              let uu____6991 =
                let uu____6992 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6992  in
              [uu____6991]  in
            FStar_List.append [disc] uu____6988  in
          FStar_List.append uu____6978 uu____6985
  
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
          let uu____7044 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7093  ->
                    fun s  ->
                      match uu____7093 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____7138 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____7149 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____7149  in
                          let names2 =
                            let uu____7154 = mk_fv (nm, s)  in uu____7154 ::
                              names1
                             in
                          let b =
                            let uu____7158 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____7158  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____7044 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____7229 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7229 with
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
              (let uu____7338 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7338)
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
                               "Prims.guard_free",{ tm = BoundV uu____7384;
                                                    freevars = uu____7385;
                                                    rng = uu____7386;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7407 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7485 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7485 fv_name
          | FreeV x when fv_force x ->
              let uu____7496 =
                let uu____7498 = fv_name x  in
                Prims.op_Hat uu____7498 " Dummy_value)"  in
              Prims.op_Hat "(" uu____7496
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7520 = op_to_string op  in
              let uu____7522 =
                let uu____7524 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7524 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7520 uu____7522
          | Labeled (t2,uu____7536,uu____7537) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7544 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7544 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7572 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7572 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7625 ->
                         let uu____7630 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7649 =
                                     let uu____7651 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7659 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7659) pats2
                                        in
                                     FStar_String.concat " " uu____7651  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7649))
                            in
                         FStar_All.pipe_right uu____7630
                           (FStar_String.concat "\n")
                      in
                   let uu____7669 =
                     let uu____7673 =
                       let uu____7677 =
                         let uu____7681 = aux1 n2 names2 body  in
                         let uu____7683 =
                           let uu____7687 = weightToSmt wopt  in
                           [uu____7687; pats_str; qid]  in
                         uu____7681 :: uu____7683  in
                       binders1 :: uu____7677  in
                     (qop_to_string qop) :: uu____7673  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7669)
          | Let (es,body) ->
              let uu____7703 =
                FStar_List.fold_left
                  (fun uu____7736  ->
                     fun e  ->
                       match uu____7736 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7779 = FStar_Util.string_of_int n0  in
                             Prims.op_Hat "@lb" uu____7779  in
                           let names01 =
                             let uu____7785 = mk_fv (nm, Term_sort)  in
                             uu____7785 :: names0  in
                           let b =
                             let uu____7789 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7789  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7703 with
               | (names2,binders,n2) ->
                   let uu____7823 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7823)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7839 = FStar_Range.string_of_range t1.rng  in
            let uu____7841 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7839
              uu____7841 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___6_7863  ->
      match uu___6_7863 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7874 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7874 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____7896 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7971 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7971 (FStar_String.concat "\n")  in
            let uu____7981 = FStar_Options.keep_query_captions ()  in
            if uu____7981
            then
              let uu____7985 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7987 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7985 uu____7987
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7996 =
                let uu____7998 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____7998 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____7996
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8039 = caption_to_string print_captions c  in
            let uu____8041 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8039 f
              (FStar_String.concat " " l) uu____8041
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8056 = name_macro_binders arg_sorts  in
            (match uu____8056 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8080 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8080 body  in
                 let uu____8085 = caption_to_string print_captions c  in
                 let uu____8087 = strSort retsort  in
                 let uu____8089 =
                   let uu____8091 = escape f  in
                   termToSmt print_captions uu____8091 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8085 f (FStar_String.concat " " binders) uu____8087
                   uu____8089)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_8118  ->
                      match uu___7_8118 with
                      | Name n1 ->
                          let uu____8121 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____8121
                      | Namespace ns ->
                          let uu____8125 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____8125
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8135 =
                  let uu____8137 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8137  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8135
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8148 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8150 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8148
              fids uu____8150 n1
        | Eval t ->
            let uu____8154 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8154
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8161 -> ""
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
      let uu____8182 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8182 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8193 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8193 (FStar_String.concat "\n")

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.op_Hat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n(declare-fun IsTotFun (Term) Bool)\n\n                ;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))"
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
      let uu____8328 =
        let uu____8332 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8332
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8328 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n"
       in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n"
       in
    let uu____8359 =
      let uu____8361 =
        let uu____8363 =
          let uu____8365 =
            let uu____8367 = FStar_Options.smtencoding_valid_intro ()  in
            if uu____8367 then valid_intro else ""  in
          let uu____8374 =
            let uu____8376 = FStar_Options.smtencoding_valid_elim ()  in
            if uu____8376 then valid_elim else ""  in
          Prims.op_Hat uu____8365 uu____8374  in
        Prims.op_Hat lex_ordering uu____8363  in
      Prims.op_Hat bcons uu____8361  in
    Prims.op_Hat basic uu____8359

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8393 =
      let uu____8394 =
        let uu____8396 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8396  in
      let uu____8405 =
        let uu____8408 =
          let uu____8409 =
            let uu____8411 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8411  in
          (uu____8409, (BitVec_sort sz), true)  in
        [uu____8408]  in
      (uu____8394, uu____8405, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8393 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8443  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8468 =
       let uu____8470 = FStar_ST.op_Bang __range_c  in
       uu____8470 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8468);
    (let uu____8515 =
       let uu____8523 = let uu____8526 = mkInteger' i norng  in [uu____8526]
          in
       ("Range_const", uu____8523)  in
     mkApp uu____8515 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8569 =
        let uu____8577 = let uu____8580 = mkInteger' i norng  in [uu____8580]
           in
        ("Tm_uvar", uu____8577)  in
      mkApp uu____8569 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8623 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8647 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8647 u v1 t
  
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
      let uu____8742 =
        let uu____8744 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8744  in
      let uu____8753 =
        let uu____8755 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8755  in
      elim_box true uu____8742 uu____8753 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8778 =
        let uu____8780 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8780  in
      let uu____8789 =
        let uu____8791 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8791  in
      elim_box true uu____8778 uu____8789 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8815 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8830 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8856 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8856
         | uu____8859 -> FStar_Pervasives_Native.None)
    | uu____8861 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8879::t1::t2::[]);
                       freevars = uu____8882; rng = uu____8883;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8902::t1::t2::[]);
                       freevars = uu____8905; rng = uu____8906;_}::[])
        -> let uu____8925 = mkEq (t1, t2) norng  in mkNot uu____8925 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8928; rng = uu____8929;_}::[])
        ->
        let uu____8948 =
          let uu____8953 = unboxInt t1  in
          let uu____8954 = unboxInt t2  in (uu____8953, uu____8954)  in
        mkLTE uu____8948 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8957; rng = uu____8958;_}::[])
        ->
        let uu____8977 =
          let uu____8982 = unboxInt t1  in
          let uu____8983 = unboxInt t2  in (uu____8982, uu____8983)  in
        mkLT uu____8977 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8986; rng = uu____8987;_}::[])
        ->
        let uu____9006 =
          let uu____9011 = unboxInt t1  in
          let uu____9012 = unboxInt t2  in (uu____9011, uu____9012)  in
        mkGTE uu____9006 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____9015; rng = uu____9016;_}::[])
        ->
        let uu____9035 =
          let uu____9040 = unboxInt t1  in
          let uu____9041 = unboxInt t2  in (uu____9040, uu____9041)  in
        mkGT uu____9035 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____9044; rng = uu____9045;_}::[])
        ->
        let uu____9064 =
          let uu____9069 = unboxBool t1  in
          let uu____9070 = unboxBool t2  in (uu____9069, uu____9070)  in
        mkAnd uu____9064 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9073; rng = uu____9074;_}::[])
        ->
        let uu____9093 =
          let uu____9098 = unboxBool t1  in
          let uu____9099 = unboxBool t2  in (uu____9098, uu____9099)  in
        mkOr uu____9093 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9101; rng = uu____9102;_}::[])
        -> let uu____9121 = unboxBool t1  in mkNot uu____9121 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9125; rng = uu____9126;_}::[])
        when
        let uu____9145 = getBoxedInteger t0  in FStar_Util.is_some uu____9145
        ->
        let sz =
          let uu____9152 = getBoxedInteger t0  in
          match uu____9152 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9160 -> failwith "impossible"  in
        let uu____9166 =
          let uu____9171 = unboxBitVec sz t1  in
          let uu____9172 = unboxBitVec sz t2  in (uu____9171, uu____9172)  in
        mkBvUlt uu____9166 t.rng
    | App
        (Var
         "Prims.equals",uu____9173::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9177;
                                      rng = uu____9178;_}::uu____9179::[])
        when
        let uu____9198 = getBoxedInteger t0  in FStar_Util.is_some uu____9198
        ->
        let sz =
          let uu____9205 = getBoxedInteger t0  in
          match uu____9205 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9213 -> failwith "impossible"  in
        let uu____9219 =
          let uu____9224 = unboxBitVec sz t1  in
          let uu____9225 = unboxBitVec sz t2  in (uu____9224, uu____9225)  in
        mkBvUlt uu____9219 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1398_9230 = unboxBool t1  in
        {
          tm = (uu___1398_9230.tm);
          freevars = (uu___1398_9230.freevars);
          rng = (t.rng)
        }
    | uu____9231 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTotFun : term -> term) = fun t  -> mkApp ("IsTotFun", [t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9302 = FStar_Options.unthrottle_inductives ()  in
        if uu____9302
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
  fun n1  -> fun t  -> mkApp ((Prims.op_Hat "is-" n1), [t]) t.rng 
let (mk_ApplyTF : term -> term -> term) =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng 
let (mk_ApplyTT : term -> term -> FStar_Range.range -> term) =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r 
let (kick_partial_app : term -> term) =
  fun t  ->
    let uu____9435 =
      let uu____9436 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9436 t t.rng  in
    FStar_All.pipe_right uu____9435 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9454 =
        let uu____9462 = let uu____9465 = mkInteger' i norng  in [uu____9465]
           in
        ("FString_const", uu____9462)  in
      mkApp uu____9454 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9496 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9496 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9543 =
         let uu____9551 =
           let uu____9554 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9554]  in
         ("SFuel", uu____9551)  in
       mkApp uu____9543 norng)
  
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
            let uu____9602 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9602
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
      let uu____9665 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9665
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9685 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9685
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9696 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9696
  
let (dummy_sort : sort) = Sort "Dummy_sort" 