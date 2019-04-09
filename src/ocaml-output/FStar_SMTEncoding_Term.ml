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
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2413 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___1_2424  ->
    match uu___1_2424 with
    | { tm = FreeV x; freevars = uu____2426; rng = uu____2427;_} -> fv_sort x
    | uu____2448 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___2_2455  ->
    match uu___2_2455 with
    | { tm = FreeV fv; freevars = uu____2457; rng = uu____2458;_} -> fv
    | uu____2479 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2507 -> []
    | Real uu____2517 -> []
    | BoundV uu____2527 -> []
    | FreeV fv -> [fv]
    | App (uu____2562,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2576,uu____2577,uu____2578,uu____2579,t1) -> freevars t1
    | Labeled (t1,uu____2600,uu____2601) -> freevars t1
    | LblPos (t1,uu____2605) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2628 = FStar_ST.op_Bang t.freevars  in
    match uu____2628 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2726 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2726  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2805  ->
    match uu___3_2805 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___4_2815  ->
    match uu___4_2815 with
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
        let uu____2851 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2851
    | NatToBv n1 ->
        let uu____2856 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2856
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_2870  ->
    match uu___5_2870 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2880 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2880
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____2902 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____2902
    | FreeV x ->
        let uu____2914 = fv_name x  in
        let uu____2916 =
          let uu____2918 = let uu____2920 = fv_sort x  in strSort uu____2920
             in
          Prims.op_Hat ":" uu____2918  in
        Prims.op_Hat uu____2914 uu____2916
    | App (op,tms) ->
        let uu____2928 =
          let uu____2930 = op_to_string op  in
          let uu____2932 =
            let uu____2934 =
              let uu____2936 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____2936 (FStar_String.concat " ")  in
            Prims.op_Hat uu____2934 ")"  in
          Prims.op_Hat uu____2930 uu____2932  in
        Prims.op_Hat "(" uu____2928
    | Labeled (t1,r1,r2) ->
        let uu____2953 = hash_of_term t1  in
        let uu____2955 =
          let uu____2957 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____2957  in
        Prims.op_Hat uu____2953 uu____2955
    | LblPos (t1,r) ->
        let uu____2963 =
          let uu____2965 = hash_of_term t1  in
          Prims.op_Hat uu____2965
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____2963
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____2993 =
          let uu____2995 =
            let uu____2997 =
              let uu____2999 =
                let uu____3001 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____3001 (FStar_String.concat " ")  in
              let uu____3011 =
                let uu____3013 =
                  let uu____3015 = hash_of_term body  in
                  let uu____3017 =
                    let uu____3019 =
                      let uu____3021 = weightToSmt wopt  in
                      let uu____3023 =
                        let uu____3025 =
                          let uu____3027 =
                            let uu____3029 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____3048 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____3048
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____3029
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____3027 "))"  in
                        Prims.op_Hat " " uu____3025  in
                      Prims.op_Hat uu____3021 uu____3023  in
                    Prims.op_Hat " " uu____3019  in
                  Prims.op_Hat uu____3015 uu____3017  in
                Prims.op_Hat ")(! " uu____3013  in
              Prims.op_Hat uu____2999 uu____3011  in
            Prims.op_Hat " (" uu____2997  in
          Prims.op_Hat (qop_to_string qop) uu____2995  in
        Prims.op_Hat "(" uu____2993
    | Let (es,body) ->
        let uu____3075 =
          let uu____3077 =
            let uu____3079 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____3079 (FStar_String.concat " ")  in
          let uu____3089 =
            let uu____3091 =
              let uu____3093 = hash_of_term body  in
              Prims.op_Hat uu____3093 ")"  in
            Prims.op_Hat ") " uu____3091  in
          Prims.op_Hat uu____3077 uu____3089  in
        Prims.op_Hat "(let (" uu____3075

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3154 =
      let uu____3156 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____3156  in
    mkBoxFunctions uu____3154
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
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
      let uu____3278 =
        let uu____3279 = FStar_Util.ensure_decimal i  in Integer uu____3279
         in
      mk uu____3278 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3294 = FStar_Util.string_of_int i  in mkInteger uu____3294 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3372  ->
    fun r  -> match uu____3372 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3402) -> mkFalse r
      | App (FalseOp ,uu____3407) -> mkTrue r
      | uu____3412 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3428  ->
    fun r  ->
      match uu____3428 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3436),uu____3437) -> t2
           | (uu____3442,App (TrueOp ,uu____3443)) -> t1
           | (App (FalseOp ,uu____3448),uu____3449) -> mkFalse r
           | (uu____3454,App (FalseOp ,uu____3455)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3472,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3481) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3488 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3508  ->
    fun r  ->
      match uu____3508 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3516),uu____3517) -> mkTrue r
           | (uu____3522,App (TrueOp ,uu____3523)) -> mkTrue r
           | (App (FalseOp ,uu____3528),uu____3529) -> t2
           | (uu____3534,App (FalseOp ,uu____3535)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3552,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3561) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3568 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3588  ->
    fun r  ->
      match uu____3588 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3596,App (TrueOp ,uu____3597)) -> mkTrue r
           | (App (FalseOp ,uu____3602),uu____3603) -> mkTrue r
           | (App (TrueOp ,uu____3608),uu____3609) -> t2
           | (uu____3614,App (Imp ,t1'::t2'::[])) ->
               let uu____3619 =
                 let uu____3626 =
                   let uu____3629 = mkAnd (t1, t1') r  in [uu____3629; t2']
                    in
                 (Imp, uu____3626)  in
               mkApp' uu____3619 r
           | uu____3632 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3657  ->
      fun r  -> match uu____3657 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3817  ->
      fun r  ->
        match uu____3817 with
        | (t1,t2) ->
            let uu____3826 =
              let uu____3833 =
                let uu____3836 =
                  let uu____3839 = mkNatToBv sz t2 r  in [uu____3839]  in
                t1 :: uu____3836  in
              (BvShl, uu____3833)  in
            mkApp' uu____3826 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3861  ->
      fun r  ->
        match uu____3861 with
        | (t1,t2) ->
            let uu____3870 =
              let uu____3877 =
                let uu____3880 =
                  let uu____3883 = mkNatToBv sz t2 r  in [uu____3883]  in
                t1 :: uu____3880  in
              (BvShr, uu____3877)  in
            mkApp' uu____3870 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3905  ->
      fun r  ->
        match uu____3905 with
        | (t1,t2) ->
            let uu____3914 =
              let uu____3921 =
                let uu____3924 =
                  let uu____3927 = mkNatToBv sz t2 r  in [uu____3927]  in
                t1 :: uu____3924  in
              (BvUdiv, uu____3921)  in
            mkApp' uu____3914 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3949  ->
      fun r  ->
        match uu____3949 with
        | (t1,t2) ->
            let uu____3958 =
              let uu____3965 =
                let uu____3968 =
                  let uu____3971 = mkNatToBv sz t2 r  in [uu____3971]  in
                t1 :: uu____3968  in
              (BvMod, uu____3965)  in
            mkApp' uu____3958 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3993  ->
      fun r  ->
        match uu____3993 with
        | (t1,t2) ->
            let uu____4002 =
              let uu____4009 =
                let uu____4012 =
                  let uu____4015 = mkNatToBv sz t2 r  in [uu____4015]  in
                t1 :: uu____4012  in
              (BvMul, uu____4009)  in
            mkApp' uu____4002 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4057  ->
    fun r  ->
      match uu____4057 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4076 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4241  ->
    fun r  ->
      match uu____4241 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4252) -> t2
           | App (FalseOp ,uu____4257) -> t3
           | uu____4262 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4263),App (TrueOp ,uu____4264)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4273),uu____4274) ->
                    let uu____4279 =
                      let uu____4284 = mkNot t1 t1.rng  in (uu____4284, t3)
                       in
                    mkImp uu____4279 r
                | (uu____4285,App (TrueOp ,uu____4286)) -> mkImp (t1, t2) r
                | (uu____4291,uu____4292) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4348 -> FStar_Pervasives_Native.None
      | Real uu____4350 -> FStar_Pervasives_Native.None
      | BoundV uu____4352 -> FStar_Pervasives_Native.None
      | FreeV uu____4354 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4378 -> true
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
            | BvUext uu____4411 -> false
            | NatToBv uu____4414 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4425,uu____4426) -> aux t2
      | Quant uu____4429 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4449 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4464 = aux t1  in
          (match uu____4464 with
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
        let uu____4502 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4502
    | FreeV fv ->
        let uu____4514 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4514
    | App (op,l) ->
        let uu____4523 = op_to_string op  in
        let uu____4525 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4523 uu____4525
    | Labeled (t1,r1,r2) ->
        let uu____4533 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4533
    | LblPos (t1,s) ->
        let uu____4540 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4540
    | Quant (qop,l,uu____4545,uu____4546,t1) ->
        let uu____4566 = print_smt_term_list_list l  in
        let uu____4568 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4566
          uu____4568
    | Let (es,body) ->
        let uu____4577 = print_smt_term_list es  in
        let uu____4579 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4577 uu____4579

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4586 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4586 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4613 =
             let uu____4615 =
               let uu____4617 = print_smt_term_list l1  in
               Prims.op_Hat uu____4617 " ] "  in
             Prims.op_Hat "; [ " uu____4615  in
           Prims.op_Hat s uu____4613) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4657  ->
        match uu____4657 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4726 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4726 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4741 =
                         let uu____4747 =
                           let uu____4749 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4749
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____4747)
                          in
                       FStar_Errors.log_issue r uu____4741);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4760) -> body
               | uu____4765 ->
                   let uu____4766 =
                     let uu____4767 =
                       let uu____4787 = all_pats_ok pats  in
                       (qop, uu____4787, wopt, vars, body)  in
                     Quant uu____4767  in
                   mk uu____4766 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4816  ->
    fun r  ->
      match uu____4816 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4862 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4862 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4889 = FStar_ST.op_Bang t1.freevars  in
        match uu____4889 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____4963 ->
            (match t1.tm with
             | Integer uu____4976 -> t1
             | Real uu____4978 -> t1
             | BoundV uu____4980 -> t1
             | FreeV x ->
                 let uu____4991 = index_of1 x  in
                 (match uu____4991 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____5005 =
                   let uu____5012 = FStar_List.map (aux ix) tms  in
                   (op, uu____5012)  in
                 mkApp' uu____5005 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____5022 =
                   let uu____5023 =
                     let uu____5031 = aux ix t2  in (uu____5031, r1, r2)  in
                   Labeled uu____5023  in
                 mk uu____5022 t2.rng
             | LblPos (t2,r) ->
                 let uu____5037 =
                   let uu____5038 =
                     let uu____5044 = aux ix t2  in (uu____5044, r)  in
                   LblPos uu____5038  in
                 mk uu____5037 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____5070 =
                   let uu____5090 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____5107 = aux (ix + n1) body  in
                   (qop, uu____5090, wopt, vars, uu____5107)  in
                 mkQuant t1.rng false uu____5070
             | Let (es,body) ->
                 let uu____5124 =
                   FStar_List.fold_left
                     (fun uu____5144  ->
                        fun e  ->
                          match uu____5144 with
                          | (ix1,l) ->
                              let uu____5168 =
                                let uu____5171 = aux ix1 e  in uu____5171 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5168))
                     (ix, []) es
                    in
                 (match uu____5124 with
                  | (ix1,es_rev) ->
                      let uu____5187 =
                        let uu____5194 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5194)  in
                      mkLet uu____5187 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5230 -> t1
        | Real uu____5232 -> t1
        | FreeV uu____5234 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5255 =
              let uu____5262 = FStar_List.map (aux shift) tms2  in
              (op, uu____5262)  in
            mkApp' uu____5255 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5272 =
              let uu____5273 =
                let uu____5281 = aux shift t2  in (uu____5281, r1, r2)  in
              Labeled uu____5273  in
            mk uu____5272 t2.rng
        | LblPos (t2,r) ->
            let uu____5287 =
              let uu____5288 =
                let uu____5294 = aux shift t2  in (uu____5294, r)  in
              LblPos uu____5288  in
            mk uu____5287 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5322 =
              let uu____5342 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5359 = aux shift1 body  in
              (qop, uu____5342, wopt, vars, uu____5359)  in
            mkQuant t1.rng false uu____5322
        | Let (es,body) ->
            let uu____5376 =
              FStar_List.fold_left
                (fun uu____5396  ->
                   fun e  ->
                     match uu____5396 with
                     | (ix,es1) ->
                         let uu____5420 =
                           let uu____5423 = aux shift e  in uu____5423 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5420))
                (shift, []) es
               in
            (match uu____5376 with
             | (shift1,es_rev) ->
                 let uu____5439 =
                   let uu____5446 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5446)  in
                 mkLet uu____5439 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5466 = abstr [fv] t  in inst [s] uu____5466
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5496  ->
      match uu____5496 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5539 =
            let uu____5559 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5576 = FStar_List.map fv_sort vars  in
            let uu____5579 = abstr vars body  in
            (qop, uu____5559, wopt, uu____5576, uu____5579)  in
          mkQuant r true uu____5539
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5610  ->
      match uu____5610 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5669  ->
      match uu____5669 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5744  ->
      match uu____5744 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5807  ->
      match uu____5807 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5858  ->
    fun r  ->
      match uu____5858 with
      | (bindings,body) ->
          let uu____5884 = FStar_List.split bindings  in
          (match uu____5884 with
           | (vars,es) ->
               let uu____5903 =
                 let uu____5910 = abstr vars body  in (es, uu____5910)  in
               mkLet uu____5903 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____5932  ->
    match uu____5932 with
    | (nm,vars,s,tm,c) ->
        let uu____5957 =
          let uu____5971 = FStar_List.map fv_sort vars  in
          let uu____5974 = abstr vars tm  in
          (nm, uu____5971, s, uu____5974, c)  in
        DefineFun uu____5957
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____5985 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____5985
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____6003  ->
    fun id1  ->
      match uu____6003 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____6019 =
              let uu____6020 =
                let uu____6025 = mkInteger' id1 norng  in
                let uu____6026 =
                  let uu____6027 =
                    let uu____6035 = constr_id_of_sort sort  in
                    let uu____6037 =
                      let uu____6040 = mkApp (tok_name, []) norng  in
                      [uu____6040]  in
                    (uu____6035, uu____6037)  in
                  mkApp uu____6027 norng  in
                (uu____6025, uu____6026)  in
              mkEq uu____6020 norng  in
            let uu____6047 = escape a_name  in
            {
              assumption_term = uu____6019;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____6047;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____6073  ->
      match uu____6073 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____6113 =
                        let uu____6114 =
                          let uu____6120 =
                            let uu____6122 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____6122  in
                          (uu____6120, s)  in
                        mk_fv uu____6114  in
                      mkFreeV uu____6113 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6150 =
              let uu____6158 = constr_id_of_sort sort  in
              (uu____6158, [capp])  in
            mkApp uu____6150 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____6167 =
              let uu____6168 =
                let uu____6179 =
                  let uu____6180 =
                    let uu____6185 = mkInteger id2 norng  in
                    (uu____6185, cid_app)  in
                  mkEq uu____6180 norng  in
                ([[capp]], bvar_names, uu____6179)  in
              mkForall rng uu____6168  in
            let uu____6194 = escape a_name  in
            {
              assumption_term = uu____6167;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6194;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6219  ->
      match uu____6219 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6252 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____6252  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6281 =
              let uu____6282 =
                let uu____6288 = bvar_name i  in (uu____6288, s)  in
              mk_fv uu____6282  in
            FStar_All.pipe_left mkFreeV uu____6281  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6324  ->
                      match uu____6324 with
                      | (uu____6334,s,uu____6336) ->
                          let uu____6341 = bvar i s  in uu____6341 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6369 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6407  ->
                      match uu____6407 with
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
                              let uu____6440 =
                                let uu____6441 =
                                  let uu____6452 =
                                    let uu____6453 =
                                      let uu____6458 =
                                        let uu____6459 = bvar i s  in
                                        uu____6459 norng  in
                                      (cproj_app, uu____6458)  in
                                    mkEq uu____6453 norng  in
                                  ([[capp]], bvar_names, uu____6452)  in
                                mkForall rng uu____6441  in
                              let uu____6472 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6440;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6472;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6369 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6497  ->
      match uu____6497 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6545  ->
                    match uu____6545 with
                    | (uu____6554,sort1,uu____6556) -> sort1))
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
              let uu____6581 =
                let uu____6586 =
                  let uu____6587 =
                    let uu____6595 = constr_id_of_sort sort  in
                    (uu____6595, [xx])  in
                  mkApp uu____6587 norng  in
                let uu____6600 =
                  let uu____6601 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6601 norng  in
                (uu____6586, uu____6600)  in
              mkEq uu____6581 norng  in
            let uu____6603 =
              let uu____6622 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6686  ->
                          match uu____6686 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6716 = mkApp (proj, [xx]) norng  in
                                (uu____6716, [])
                              else
                                (let fi =
                                   let uu____6725 =
                                     let uu____6731 =
                                       let uu____6733 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____6733  in
                                     (uu____6731, s)  in
                                   mk_fv uu____6725  in
                                 let uu____6737 = mkFreeV fi norng  in
                                 (uu____6737, [fi]))))
                 in
              FStar_All.pipe_right uu____6622 FStar_List.split  in
            match uu____6603 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6834 =
                    let uu____6839 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6839)  in
                  mkEq uu____6834 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6852 ->
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
          let uu____6887 =
            let uu____6890 =
              let uu____6891 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6891  in
            uu____6890 :: cdecl :: cid :: projs  in
          let uu____6894 =
            let uu____6897 =
              let uu____6900 =
                let uu____6901 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6901  in
              [uu____6900]  in
            FStar_List.append [disc] uu____6897  in
          FStar_List.append uu____6887 uu____6894
  
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
          let uu____6953 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7002  ->
                    fun s  ->
                      match uu____7002 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____7047 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____7058 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____7058  in
                          let names2 =
                            let uu____7063 = mk_fv (nm, s)  in uu____7063 ::
                              names1
                             in
                          let b =
                            let uu____7067 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____7067  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____6953 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____7138 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7138 with
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
              (let uu____7247 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7247)
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
                               "Prims.guard_free",{ tm = BoundV uu____7293;
                                                    freevars = uu____7294;
                                                    rng = uu____7295;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7316 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7394 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7394 fv_name
          | FreeV x when fv_force x ->
              let uu____7405 =
                let uu____7407 = fv_name x  in
                Prims.op_Hat uu____7407 " Dummy_value)"  in
              Prims.op_Hat "(" uu____7405
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7429 = op_to_string op  in
              let uu____7431 =
                let uu____7433 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7433 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7429 uu____7431
          | Labeled (t2,uu____7445,uu____7446) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7453 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7453 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7481 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7481 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7534 ->
                         let uu____7539 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7558 =
                                     let uu____7560 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7568 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7568) pats2
                                        in
                                     FStar_String.concat " " uu____7560  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7558))
                            in
                         FStar_All.pipe_right uu____7539
                           (FStar_String.concat "\n")
                      in
                   let uu____7578 =
                     let uu____7582 =
                       let uu____7586 =
                         let uu____7590 = aux1 n2 names2 body  in
                         let uu____7592 =
                           let uu____7596 = weightToSmt wopt  in
                           [uu____7596; pats_str; qid]  in
                         uu____7590 :: uu____7592  in
                       binders1 :: uu____7586  in
                     (qop_to_string qop) :: uu____7582  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7578)
          | Let (es,body) ->
              let uu____7612 =
                FStar_List.fold_left
                  (fun uu____7645  ->
                     fun e  ->
                       match uu____7645 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7688 = FStar_Util.string_of_int n0  in
                             Prims.op_Hat "@lb" uu____7688  in
                           let names01 =
                             let uu____7694 = mk_fv (nm, Term_sort)  in
                             uu____7694 :: names0  in
                           let b =
                             let uu____7698 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7698  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7612 with
               | (names2,binders,n2) ->
                   let uu____7732 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7732)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7748 = FStar_Range.string_of_range t1.rng  in
            let uu____7750 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7748
              uu____7750 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___6_7772  ->
      match uu___6_7772 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7783 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7783 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____7805 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7880 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7880 (FStar_String.concat "\n")  in
            let uu____7890 = FStar_Options.keep_query_captions ()  in
            if uu____7890
            then
              let uu____7894 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7896 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7894 uu____7896
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7905 =
                let uu____7907 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____7907 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____7905
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____7948 = caption_to_string print_captions c  in
            let uu____7950 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____7948 f
              (FStar_String.concat " " l) uu____7950
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____7965 = name_macro_binders arg_sorts  in
            (match uu____7965 with
             | (names1,binders) ->
                 let body1 =
                   let uu____7989 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____7989 body  in
                 let uu____7994 = caption_to_string print_captions c  in
                 let uu____7996 = strSort retsort  in
                 let uu____7998 =
                   let uu____8000 = escape f  in
                   termToSmt print_captions uu____8000 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____7994 f (FStar_String.concat " " binders) uu____7996
                   uu____7998)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_8027  ->
                      match uu___7_8027 with
                      | Name n1 ->
                          let uu____8030 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____8030
                      | Namespace ns ->
                          let uu____8034 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____8034
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8044 =
                  let uu____8046 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8046  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8044
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8057 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8059 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8057
              fids uu____8059 n1
        | Eval t ->
            let uu____8063 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8063
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8070 -> ""
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
      let uu____8091 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8091 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8102 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8102 (FStar_String.concat "\n")

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.op_Hat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeZ x t) (HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))"
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
      let uu____8237 =
        let uu____8241 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8241
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8237 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n"
       in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n"
       in
    let uu____8268 =
      let uu____8270 =
        let uu____8272 =
          let uu____8274 =
            let uu____8276 = FStar_Options.smtencoding_valid_intro ()  in
            if uu____8276 then valid_intro else ""  in
          let uu____8283 =
            let uu____8285 = FStar_Options.smtencoding_valid_elim ()  in
            if uu____8285 then valid_elim else ""  in
          Prims.op_Hat uu____8274 uu____8283  in
        Prims.op_Hat lex_ordering uu____8272  in
      Prims.op_Hat bcons uu____8270  in
    Prims.op_Hat basic uu____8268

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8302 =
      let uu____8303 =
        let uu____8305 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8305  in
      let uu____8314 =
        let uu____8317 =
          let uu____8318 =
            let uu____8320 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8320  in
          (uu____8318, (BitVec_sort sz), true)  in
        [uu____8317]  in
      (uu____8303, uu____8314, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8302 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8352  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8377 =
       let uu____8379 = FStar_ST.op_Bang __range_c  in
       uu____8379 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8377);
    (let uu____8424 =
       let uu____8432 = let uu____8435 = mkInteger' i norng  in [uu____8435]
          in
       ("Range_const", uu____8432)  in
     mkApp uu____8424 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8478 =
        let uu____8486 = let uu____8489 = mkInteger' i norng  in [uu____8489]
           in
        ("Tm_uvar", uu____8486)  in
      mkApp uu____8478 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8532 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8556 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8556 u v1 t
  
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
      let uu____8651 =
        let uu____8653 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8653  in
      let uu____8662 =
        let uu____8664 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8664  in
      elim_box true uu____8651 uu____8662 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8687 =
        let uu____8689 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8689  in
      let uu____8698 =
        let uu____8700 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8700  in
      elim_box true uu____8687 uu____8698 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8724 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8739 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8765 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8765
         | uu____8768 -> FStar_Pervasives_Native.None)
    | uu____8770 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8788::t1::t2::[]);
                       freevars = uu____8791; rng = uu____8792;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8811::t1::t2::[]);
                       freevars = uu____8814; rng = uu____8815;_}::[])
        -> let uu____8834 = mkEq (t1, t2) norng  in mkNot uu____8834 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8837; rng = uu____8838;_}::[])
        ->
        let uu____8857 =
          let uu____8862 = unboxInt t1  in
          let uu____8863 = unboxInt t2  in (uu____8862, uu____8863)  in
        mkLTE uu____8857 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8866; rng = uu____8867;_}::[])
        ->
        let uu____8886 =
          let uu____8891 = unboxInt t1  in
          let uu____8892 = unboxInt t2  in (uu____8891, uu____8892)  in
        mkLT uu____8886 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8895; rng = uu____8896;_}::[])
        ->
        let uu____8915 =
          let uu____8920 = unboxInt t1  in
          let uu____8921 = unboxInt t2  in (uu____8920, uu____8921)  in
        mkGTE uu____8915 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8924; rng = uu____8925;_}::[])
        ->
        let uu____8944 =
          let uu____8949 = unboxInt t1  in
          let uu____8950 = unboxInt t2  in (uu____8949, uu____8950)  in
        mkGT uu____8944 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____8953; rng = uu____8954;_}::[])
        ->
        let uu____8973 =
          let uu____8978 = unboxBool t1  in
          let uu____8979 = unboxBool t2  in (uu____8978, uu____8979)  in
        mkAnd uu____8973 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____8982; rng = uu____8983;_}::[])
        ->
        let uu____9002 =
          let uu____9007 = unboxBool t1  in
          let uu____9008 = unboxBool t2  in (uu____9007, uu____9008)  in
        mkOr uu____9002 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9010; rng = uu____9011;_}::[])
        -> let uu____9030 = unboxBool t1  in mkNot uu____9030 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9034; rng = uu____9035;_}::[])
        when
        let uu____9054 = getBoxedInteger t0  in FStar_Util.is_some uu____9054
        ->
        let sz =
          let uu____9061 = getBoxedInteger t0  in
          match uu____9061 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9069 -> failwith "impossible"  in
        let uu____9075 =
          let uu____9080 = unboxBitVec sz t1  in
          let uu____9081 = unboxBitVec sz t2  in (uu____9080, uu____9081)  in
        mkBvUlt uu____9075 t.rng
    | App
        (Var
         "Prims.equals",uu____9082::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9086;
                                      rng = uu____9087;_}::uu____9088::[])
        when
        let uu____9107 = getBoxedInteger t0  in FStar_Util.is_some uu____9107
        ->
        let sz =
          let uu____9114 = getBoxedInteger t0  in
          match uu____9114 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9122 -> failwith "impossible"  in
        let uu____9128 =
          let uu____9133 = unboxBitVec sz t1  in
          let uu____9134 = unboxBitVec sz t2  in (uu____9133, uu____9134)  in
        mkBvUlt uu____9128 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1391_9139 = unboxBool t1  in
        {
          tm = (uu___1391_9139.tm);
          freevars = (uu___1391_9139.freevars);
          rng = (t.rng)
        }
    | uu____9140 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____9201 = FStar_Options.unthrottle_inductives ()  in
        if uu____9201
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
    let uu____9334 =
      let uu____9335 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9335 t t.rng  in
    FStar_All.pipe_right uu____9334 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9353 =
        let uu____9361 = let uu____9364 = mkInteger' i norng  in [uu____9364]
           in
        ("FString_const", uu____9361)  in
      mkApp uu____9353 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9395 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9395 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9442 =
         let uu____9450 =
           let uu____9453 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9453]  in
         ("SFuel", uu____9450)  in
       mkApp uu____9442 norng)
  
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
            let uu____9501 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9501
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
      let uu____9564 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9564
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9584 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9584
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9595 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9595
  
let (dummy_sort : sort) = Sort "Dummy_sort" 