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
    | FreeV fv -> [fv]
    | App (uu____2636,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2650,uu____2651,uu____2652,uu____2653,t1) -> freevars t1
    | Labeled (t1,uu____2674,uu____2675) -> freevars t1
    | LblPos (t1,uu____2679) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2702 = FStar_ST.op_Bang t.freevars  in
    match uu____2702 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2800 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2800  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2879  ->
    match uu___3_2879 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___4_2889  ->
    match uu___4_2889 with
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
        let uu____2925 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2925
    | NatToBv n1 ->
        let uu____2930 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2930
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_2944  ->
    match uu___5_2944 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2954 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2954
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____2976 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____2976
    | FreeV x ->
        let uu____2988 = fv_name x  in
        let uu____2990 =
          let uu____2992 = let uu____2994 = fv_sort x  in strSort uu____2994
             in
          Prims.op_Hat ":" uu____2992  in
        Prims.op_Hat uu____2988 uu____2990
    | App (op,tms) ->
        let uu____3002 =
          let uu____3004 = op_to_string op  in
          let uu____3006 =
            let uu____3008 =
              let uu____3010 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____3010 (FStar_String.concat " ")  in
            Prims.op_Hat uu____3008 ")"  in
          Prims.op_Hat uu____3004 uu____3006  in
        Prims.op_Hat "(" uu____3002
    | Labeled (t1,r1,r2) ->
        let uu____3027 = hash_of_term t1  in
        let uu____3029 =
          let uu____3031 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____3031  in
        Prims.op_Hat uu____3027 uu____3029
    | LblPos (t1,r) ->
        let uu____3037 =
          let uu____3039 = hash_of_term t1  in
          Prims.op_Hat uu____3039
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____3037
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____3067 =
          let uu____3069 =
            let uu____3071 =
              let uu____3073 =
                let uu____3075 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____3075 (FStar_String.concat " ")  in
              let uu____3085 =
                let uu____3087 =
                  let uu____3089 = hash_of_term body  in
                  let uu____3091 =
                    let uu____3093 =
                      let uu____3095 = weightToSmt wopt  in
                      let uu____3097 =
                        let uu____3099 =
                          let uu____3101 =
                            let uu____3103 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____3122 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____3122
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____3103
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____3101 "))"  in
                        Prims.op_Hat " " uu____3099  in
                      Prims.op_Hat uu____3095 uu____3097  in
                    Prims.op_Hat " " uu____3093  in
                  Prims.op_Hat uu____3089 uu____3091  in
                Prims.op_Hat ")(! " uu____3087  in
              Prims.op_Hat uu____3073 uu____3085  in
            Prims.op_Hat " (" uu____3071  in
          Prims.op_Hat (qop_to_string qop) uu____3069  in
        Prims.op_Hat "(" uu____3067
    | Let (es,body) ->
        let uu____3149 =
          let uu____3151 =
            let uu____3153 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____3153 (FStar_String.concat " ")  in
          let uu____3163 =
            let uu____3165 =
              let uu____3167 = hash_of_term body  in
              Prims.op_Hat uu____3167 ")"  in
            Prims.op_Hat ") " uu____3165  in
          Prims.op_Hat uu____3151 uu____3163  in
        Prims.op_Hat "(let (" uu____3149

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3228 =
      let uu____3230 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____3230  in
    mkBoxFunctions uu____3228
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____3255 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____3255 = "Box") &&
        (let uu____3262 =
           let uu____3264 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3264  in
         Prims.op_Negation uu____3262)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3288 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3288; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3352 =
        let uu____3353 = FStar_Util.ensure_decimal i  in Integer uu____3353
         in
      mk uu____3352 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3368 = FStar_Util.string_of_int i  in mkInteger uu____3368 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3446  ->
    fun r  -> match uu____3446 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3476) -> mkFalse r
      | App (FalseOp ,uu____3481) -> mkTrue r
      | uu____3486 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3502  ->
    fun r  ->
      match uu____3502 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3510),uu____3511) -> t2
           | (uu____3516,App (TrueOp ,uu____3517)) -> t1
           | (App (FalseOp ,uu____3522),uu____3523) -> mkFalse r
           | (uu____3528,App (FalseOp ,uu____3529)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3546,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3555) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3562 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3582  ->
    fun r  ->
      match uu____3582 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3590),uu____3591) -> mkTrue r
           | (uu____3596,App (TrueOp ,uu____3597)) -> mkTrue r
           | (App (FalseOp ,uu____3602),uu____3603) -> t2
           | (uu____3608,App (FalseOp ,uu____3609)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3626,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3635) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3642 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3662  ->
    fun r  ->
      match uu____3662 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3670,App (TrueOp ,uu____3671)) -> mkTrue r
           | (App (FalseOp ,uu____3676),uu____3677) -> mkTrue r
           | (App (TrueOp ,uu____3682),uu____3683) -> t2
           | (uu____3688,App (Imp ,t1'::t2'::[])) ->
               let uu____3693 =
                 let uu____3700 =
                   let uu____3703 = mkAnd (t1, t1') r  in [uu____3703; t2']
                    in
                 (Imp, uu____3700)  in
               mkApp' uu____3693 r
           | uu____3706 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3731  ->
      fun r  -> match uu____3731 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3891  ->
      fun r  ->
        match uu____3891 with
        | (t1,t2) ->
            let uu____3900 =
              let uu____3907 =
                let uu____3910 =
                  let uu____3913 = mkNatToBv sz t2 r  in [uu____3913]  in
                t1 :: uu____3910  in
              (BvShl, uu____3907)  in
            mkApp' uu____3900 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3935  ->
      fun r  ->
        match uu____3935 with
        | (t1,t2) ->
            let uu____3944 =
              let uu____3951 =
                let uu____3954 =
                  let uu____3957 = mkNatToBv sz t2 r  in [uu____3957]  in
                t1 :: uu____3954  in
              (BvShr, uu____3951)  in
            mkApp' uu____3944 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3979  ->
      fun r  ->
        match uu____3979 with
        | (t1,t2) ->
            let uu____3988 =
              let uu____3995 =
                let uu____3998 =
                  let uu____4001 = mkNatToBv sz t2 r  in [uu____4001]  in
                t1 :: uu____3998  in
              (BvUdiv, uu____3995)  in
            mkApp' uu____3988 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4023  ->
      fun r  ->
        match uu____4023 with
        | (t1,t2) ->
            let uu____4032 =
              let uu____4039 =
                let uu____4042 =
                  let uu____4045 = mkNatToBv sz t2 r  in [uu____4045]  in
                t1 :: uu____4042  in
              (BvMod, uu____4039)  in
            mkApp' uu____4032 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4067  ->
      fun r  ->
        match uu____4067 with
        | (t1,t2) ->
            let uu____4076 =
              let uu____4083 =
                let uu____4086 =
                  let uu____4089 = mkNatToBv sz t2 r  in [uu____4089]  in
                t1 :: uu____4086  in
              (BvMul, uu____4083)  in
            mkApp' uu____4076 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4131  ->
    fun r  ->
      match uu____4131 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4150 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4315  ->
    fun r  ->
      match uu____4315 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4326) -> t2
           | App (FalseOp ,uu____4331) -> t3
           | uu____4336 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4337),App (TrueOp ,uu____4338)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4347),uu____4348) ->
                    let uu____4353 =
                      let uu____4358 = mkNot t1 t1.rng  in (uu____4358, t3)
                       in
                    mkImp uu____4353 r
                | (uu____4359,App (TrueOp ,uu____4360)) -> mkImp (t1, t2) r
                | (uu____4365,uu____4366) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4422 -> FStar_Pervasives_Native.None
      | Real uu____4424 -> FStar_Pervasives_Native.None
      | BoundV uu____4426 -> FStar_Pervasives_Native.None
      | FreeV uu____4428 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4452 -> true
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
            | BvUext uu____4485 -> false
            | NatToBv uu____4488 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4499,uu____4500) -> aux t2
      | Quant uu____4503 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4523 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4538 = aux t1  in
          (match uu____4538 with
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
        let uu____4576 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4576
    | FreeV fv ->
        let uu____4588 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4588
    | App (op,l) ->
        let uu____4597 = op_to_string op  in
        let uu____4599 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4597 uu____4599
    | Labeled (t1,r1,r2) ->
        let uu____4607 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4607
    | LblPos (t1,s) ->
        let uu____4614 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4614
    | Quant (qop,l,uu____4619,uu____4620,t1) ->
        let uu____4640 = print_smt_term_list_list l  in
        let uu____4642 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4640
          uu____4642
    | Let (es,body) ->
        let uu____4651 = print_smt_term_list es  in
        let uu____4653 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4651 uu____4653

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4660 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4660 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4687 =
             let uu____4689 =
               let uu____4691 = print_smt_term_list l1  in
               Prims.op_Hat uu____4691 " ] "  in
             Prims.op_Hat "; [ " uu____4689  in
           Prims.op_Hat s uu____4687) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4731  ->
        match uu____4731 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4800 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4800 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4815 =
                         let uu____4821 =
                           let uu____4823 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4823
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____4821)
                          in
                       FStar_Errors.log_issue r uu____4815);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4834) -> body
               | uu____4839 ->
                   let uu____4840 =
                     let uu____4841 =
                       let uu____4861 = all_pats_ok pats  in
                       (qop, uu____4861, wopt, vars, body)  in
                     Quant uu____4841  in
                   mk uu____4840 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4890  ->
    fun r  ->
      match uu____4890 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4936 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4936 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____4963 = FStar_ST.op_Bang t1.freevars  in
        match uu____4963 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____5037 ->
            (match t1.tm with
             | Integer uu____5050 -> t1
             | Real uu____5052 -> t1
             | BoundV uu____5054 -> t1
             | FreeV x ->
                 let uu____5065 = index_of1 x  in
                 (match uu____5065 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____5079 =
                   let uu____5086 = FStar_List.map (aux ix) tms  in
                   (op, uu____5086)  in
                 mkApp' uu____5079 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____5096 =
                   let uu____5097 =
                     let uu____5105 = aux ix t2  in (uu____5105, r1, r2)  in
                   Labeled uu____5097  in
                 mk uu____5096 t2.rng
             | LblPos (t2,r) ->
                 let uu____5111 =
                   let uu____5112 =
                     let uu____5118 = aux ix t2  in (uu____5118, r)  in
                   LblPos uu____5112  in
                 mk uu____5111 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____5144 =
                   let uu____5164 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____5181 = aux (ix + n1) body  in
                   (qop, uu____5164, wopt, vars, uu____5181)  in
                 mkQuant t1.rng false uu____5144
             | Let (es,body) ->
                 let uu____5198 =
                   FStar_List.fold_left
                     (fun uu____5218  ->
                        fun e  ->
                          match uu____5218 with
                          | (ix1,l) ->
                              let uu____5242 =
                                let uu____5245 = aux ix1 e  in uu____5245 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____5242))
                     (ix, []) es
                    in
                 (match uu____5198 with
                  | (ix1,es_rev) ->
                      let uu____5261 =
                        let uu____5268 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5268)  in
                      mkLet uu____5261 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5304 -> t1
        | Real uu____5306 -> t1
        | FreeV uu____5308 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5329 =
              let uu____5336 = FStar_List.map (aux shift) tms2  in
              (op, uu____5336)  in
            mkApp' uu____5329 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5346 =
              let uu____5347 =
                let uu____5355 = aux shift t2  in (uu____5355, r1, r2)  in
              Labeled uu____5347  in
            mk uu____5346 t2.rng
        | LblPos (t2,r) ->
            let uu____5361 =
              let uu____5362 =
                let uu____5368 = aux shift t2  in (uu____5368, r)  in
              LblPos uu____5362  in
            mk uu____5361 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5396 =
              let uu____5416 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5433 = aux shift1 body  in
              (qop, uu____5416, wopt, vars, uu____5433)  in
            mkQuant t1.rng false uu____5396
        | Let (es,body) ->
            let uu____5450 =
              FStar_List.fold_left
                (fun uu____5470  ->
                   fun e  ->
                     match uu____5470 with
                     | (ix,es1) ->
                         let uu____5494 =
                           let uu____5497 = aux shift e  in uu____5497 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____5494))
                (shift, []) es
               in
            (match uu____5450 with
             | (shift1,es_rev) ->
                 let uu____5513 =
                   let uu____5520 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5520)  in
                 mkLet uu____5513 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5540 = abstr [fv] t  in inst [s] uu____5540
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5570  ->
      match uu____5570 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5613 =
            let uu____5633 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5650 = FStar_List.map fv_sort vars  in
            let uu____5653 = abstr vars body  in
            (qop, uu____5633, wopt, uu____5650, uu____5653)  in
          mkQuant r true uu____5613
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5684  ->
      match uu____5684 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5743  ->
      match uu____5743 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5818  ->
      match uu____5818 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5881  ->
      match uu____5881 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5932  ->
    fun r  ->
      match uu____5932 with
      | (bindings,body) ->
          let uu____5958 = FStar_List.split bindings  in
          (match uu____5958 with
           | (vars,es) ->
               let uu____5977 =
                 let uu____5984 = abstr vars body  in (es, uu____5984)  in
               mkLet uu____5977 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____6006  ->
    match uu____6006 with
    | (nm,vars,s,tm,c) ->
        let uu____6031 =
          let uu____6045 = FStar_List.map fv_sort vars  in
          let uu____6048 = abstr vars tm  in
          (nm, uu____6045, s, uu____6048, c)  in
        DefineFun uu____6031
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____6059 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____6059
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____6077  ->
    fun id1  ->
      match uu____6077 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____6093 =
              let uu____6094 =
                let uu____6099 = mkInteger' id1 norng  in
                let uu____6100 =
                  let uu____6101 =
                    let uu____6109 = constr_id_of_sort sort  in
                    let uu____6111 =
                      let uu____6114 = mkApp (tok_name, []) norng  in
                      [uu____6114]  in
                    (uu____6109, uu____6111)  in
                  mkApp uu____6101 norng  in
                (uu____6099, uu____6100)  in
              mkEq uu____6094 norng  in
            let uu____6121 = escape a_name  in
            {
              assumption_term = uu____6093;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____6121;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____6147  ->
      match uu____6147 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____6187 =
                        let uu____6188 =
                          let uu____6194 =
                            let uu____6196 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____6196  in
                          (uu____6194, s)  in
                        mk_fv uu____6188  in
                      mkFreeV uu____6187 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6224 =
              let uu____6232 = constr_id_of_sort sort  in
              (uu____6232, [capp])  in
            mkApp uu____6224 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____6241 =
              let uu____6242 =
                let uu____6253 =
                  let uu____6254 =
                    let uu____6259 = mkInteger id2 norng  in
                    (uu____6259, cid_app)  in
                  mkEq uu____6254 norng  in
                ([[capp]], bvar_names, uu____6253)  in
              mkForall rng uu____6242  in
            let uu____6268 = escape a_name  in
            {
              assumption_term = uu____6241;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6268;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6293  ->
      match uu____6293 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6326 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____6326  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____6355 =
              let uu____6356 =
                let uu____6362 = bvar_name i  in (uu____6362, s)  in
              mk_fv uu____6356  in
            FStar_All.pipe_left mkFreeV uu____6355  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6398  ->
                      match uu____6398 with
                      | (uu____6408,s,uu____6410) ->
                          let uu____6415 = bvar i s  in uu____6415 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6443 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6481  ->
                      match uu____6481 with
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
                              let uu____6514 =
                                let uu____6515 =
                                  let uu____6526 =
                                    let uu____6527 =
                                      let uu____6532 =
                                        let uu____6533 = bvar i s  in
                                        uu____6533 norng  in
                                      (cproj_app, uu____6532)  in
                                    mkEq uu____6527 norng  in
                                  ([[capp]], bvar_names, uu____6526)  in
                                mkForall rng uu____6515  in
                              let uu____6546 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6514;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6546;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6443 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6571  ->
      match uu____6571 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6619  ->
                    match uu____6619 with
                    | (uu____6628,sort1,uu____6630) -> sort1))
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
              let uu____6655 =
                let uu____6660 =
                  let uu____6661 =
                    let uu____6669 = constr_id_of_sort sort  in
                    (uu____6669, [xx])  in
                  mkApp uu____6661 norng  in
                let uu____6674 =
                  let uu____6675 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6675 norng  in
                (uu____6660, uu____6674)  in
              mkEq uu____6655 norng  in
            let uu____6677 =
              let uu____6696 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6760  ->
                          match uu____6760 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6790 = mkApp (proj, [xx]) norng  in
                                (uu____6790, [])
                              else
                                (let fi =
                                   let uu____6799 =
                                     let uu____6805 =
                                       let uu____6807 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____6807  in
                                     (uu____6805, s)  in
                                   mk_fv uu____6799  in
                                 let uu____6811 = mkFreeV fi norng  in
                                 (uu____6811, [fi]))))
                 in
              FStar_All.pipe_right uu____6696 FStar_List.split  in
            match uu____6677 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6908 =
                    let uu____6913 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6913)  in
                  mkEq uu____6908 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6926 ->
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
          let uu____6961 =
            let uu____6964 =
              let uu____6965 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____6965  in
            uu____6964 :: cdecl :: cid :: projs  in
          let uu____6968 =
            let uu____6971 =
              let uu____6974 =
                let uu____6975 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____6975  in
              [uu____6974]  in
            FStar_List.append [disc] uu____6971  in
          FStar_List.append uu____6961 uu____6968
  
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
          let uu____7027 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7076  ->
                    fun s  ->
                      match uu____7076 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____7121 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____7132 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____7132  in
                          let names2 =
                            let uu____7137 = mk_fv (nm, s)  in uu____7137 ::
                              names1
                             in
                          let b =
                            let uu____7141 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____7141  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____7027 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____7212 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____7212 with
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
              (let uu____7321 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7321)
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
                               "Prims.guard_free",{ tm = BoundV uu____7367;
                                                    freevars = uu____7368;
                                                    rng = uu____7369;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7390 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7468 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7468 fv_name
          | FreeV x when fv_force x ->
              let uu____7479 =
                let uu____7481 = fv_name x  in
                Prims.op_Hat uu____7481 " Dummy_value)"  in
              Prims.op_Hat "(" uu____7479
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7503 = op_to_string op  in
              let uu____7505 =
                let uu____7507 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7507 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7503 uu____7505
          | Labeled (t2,uu____7519,uu____7520) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7527 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7527 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7555 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7555 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7608 ->
                         let uu____7613 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7632 =
                                     let uu____7634 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7642 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7642) pats2
                                        in
                                     FStar_String.concat " " uu____7634  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7632))
                            in
                         FStar_All.pipe_right uu____7613
                           (FStar_String.concat "\n")
                      in
                   let uu____7652 =
                     let uu____7656 =
                       let uu____7660 =
                         let uu____7664 = aux1 n2 names2 body  in
                         let uu____7666 =
                           let uu____7670 = weightToSmt wopt  in
                           [uu____7670; pats_str; qid]  in
                         uu____7664 :: uu____7666  in
                       binders1 :: uu____7660  in
                     (qop_to_string qop) :: uu____7656  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7652)
          | Let (es,body) ->
              let uu____7686 =
                FStar_List.fold_left
                  (fun uu____7719  ->
                     fun e  ->
                       match uu____7719 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7762 = FStar_Util.string_of_int n0  in
                             Prims.op_Hat "@lb" uu____7762  in
                           let names01 =
                             let uu____7768 = mk_fv (nm, Term_sort)  in
                             uu____7768 :: names0  in
                           let b =
                             let uu____7772 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7772  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____7686 with
               | (names2,binders,n2) ->
                   let uu____7806 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7806)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7822 = FStar_Range.string_of_range t1.rng  in
            let uu____7824 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7822
              uu____7824 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___6_7846  ->
      match uu___6_7846 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7857 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7857 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____7879 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7954 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7954 (FStar_String.concat "\n")  in
            let uu____7964 = FStar_Options.keep_query_captions ()  in
            if uu____7964
            then
              let uu____7968 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7970 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____7968 uu____7970
            else res
        | Caption c ->
            if print_captions
            then
              let uu____7979 =
                let uu____7981 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____7981 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____7979
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8022 = caption_to_string print_captions c  in
            let uu____8024 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8022 f
              (FStar_String.concat " " l) uu____8024
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8039 = name_macro_binders arg_sorts  in
            (match uu____8039 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8063 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8063 body  in
                 let uu____8068 = caption_to_string print_captions c  in
                 let uu____8070 = strSort retsort  in
                 let uu____8072 =
                   let uu____8074 = escape f  in
                   termToSmt print_captions uu____8074 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8068 f (FStar_String.concat " " binders) uu____8070
                   uu____8072)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_8101  ->
                      match uu___7_8101 with
                      | Name n1 ->
                          let uu____8104 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____8104
                      | Namespace ns ->
                          let uu____8108 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____8108
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8118 =
                  let uu____8120 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8120  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8118
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8131 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8133 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8131
              fids uu____8133 n1
        | Eval t ->
            let uu____8137 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8137
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8144 -> ""
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
      let uu____8165 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8165 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8176 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8176 (FStar_String.concat "\n")

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
      let uu____8311 =
        let uu____8315 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8315
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8311 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n"
       in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n"
       in
    let uu____8342 =
      let uu____8344 =
        let uu____8346 =
          let uu____8348 =
            let uu____8350 = FStar_Options.smtencoding_valid_intro ()  in
            if uu____8350 then valid_intro else ""  in
          let uu____8357 =
            let uu____8359 = FStar_Options.smtencoding_valid_elim ()  in
            if uu____8359 then valid_elim else ""  in
          Prims.op_Hat uu____8348 uu____8357  in
        Prims.op_Hat lex_ordering uu____8346  in
      Prims.op_Hat bcons uu____8344  in
    Prims.op_Hat basic uu____8342

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8376 =
      let uu____8377 =
        let uu____8379 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8379  in
      let uu____8388 =
        let uu____8391 =
          let uu____8392 =
            let uu____8394 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8394  in
          (uu____8392, (BitVec_sort sz), true)  in
        [uu____8391]  in
      (uu____8377, uu____8388, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____8376 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____8426  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8451 =
       let uu____8453 = FStar_ST.op_Bang __range_c  in
       uu____8453 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____8451);
    (let uu____8498 =
       let uu____8506 = let uu____8509 = mkInteger' i norng  in [uu____8509]
          in
       ("Range_const", uu____8506)  in
     mkApp uu____8498 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8552 =
        let uu____8560 = let uu____8563 = mkInteger' i norng  in [uu____8563]
           in
        ("Tm_uvar", uu____8560)  in
      mkApp uu____8552 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8606 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8630 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8630 u v1 t
  
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
      let uu____8725 =
        let uu____8727 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8727  in
      let uu____8736 =
        let uu____8738 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8738  in
      elim_box true uu____8725 uu____8736 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8761 =
        let uu____8763 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8763  in
      let uu____8772 =
        let uu____8774 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8774  in
      elim_box true uu____8761 uu____8772 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8798 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8813 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8839 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8839
         | uu____8842 -> FStar_Pervasives_Native.None)
    | uu____8844 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8862::t1::t2::[]);
                       freevars = uu____8865; rng = uu____8866;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8885::t1::t2::[]);
                       freevars = uu____8888; rng = uu____8889;_}::[])
        -> let uu____8908 = mkEq (t1, t2) norng  in mkNot uu____8908 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8911; rng = uu____8912;_}::[])
        ->
        let uu____8931 =
          let uu____8936 = unboxInt t1  in
          let uu____8937 = unboxInt t2  in (uu____8936, uu____8937)  in
        mkLTE uu____8931 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8940; rng = uu____8941;_}::[])
        ->
        let uu____8960 =
          let uu____8965 = unboxInt t1  in
          let uu____8966 = unboxInt t2  in (uu____8965, uu____8966)  in
        mkLT uu____8960 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____8969; rng = uu____8970;_}::[])
        ->
        let uu____8989 =
          let uu____8994 = unboxInt t1  in
          let uu____8995 = unboxInt t2  in (uu____8994, uu____8995)  in
        mkGTE uu____8989 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____8998; rng = uu____8999;_}::[])
        ->
        let uu____9018 =
          let uu____9023 = unboxInt t1  in
          let uu____9024 = unboxInt t2  in (uu____9023, uu____9024)  in
        mkGT uu____9018 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____9027; rng = uu____9028;_}::[])
        ->
        let uu____9047 =
          let uu____9052 = unboxBool t1  in
          let uu____9053 = unboxBool t2  in (uu____9052, uu____9053)  in
        mkAnd uu____9047 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9056; rng = uu____9057;_}::[])
        ->
        let uu____9076 =
          let uu____9081 = unboxBool t1  in
          let uu____9082 = unboxBool t2  in (uu____9081, uu____9082)  in
        mkOr uu____9076 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9084; rng = uu____9085;_}::[])
        -> let uu____9104 = unboxBool t1  in mkNot uu____9104 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9108; rng = uu____9109;_}::[])
        when
        let uu____9128 = getBoxedInteger t0  in FStar_Util.is_some uu____9128
        ->
        let sz =
          let uu____9135 = getBoxedInteger t0  in
          match uu____9135 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9143 -> failwith "impossible"  in
        let uu____9149 =
          let uu____9154 = unboxBitVec sz t1  in
          let uu____9155 = unboxBitVec sz t2  in (uu____9154, uu____9155)  in
        mkBvUlt uu____9149 t.rng
    | App
        (Var
         "Prims.equals",uu____9156::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9160;
                                      rng = uu____9161;_}::uu____9162::[])
        when
        let uu____9181 = getBoxedInteger t0  in FStar_Util.is_some uu____9181
        ->
        let sz =
          let uu____9188 = getBoxedInteger t0  in
          match uu____9188 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9196 -> failwith "impossible"  in
        let uu____9202 =
          let uu____9207 = unboxBitVec sz t1  in
          let uu____9208 = unboxBitVec sz t2  in (uu____9207, uu____9208)  in
        mkBvUlt uu____9202 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1396_9213 = unboxBool t1  in
        {
          tm = (uu___1396_9213.tm);
          freevars = (uu___1396_9213.freevars);
          rng = (t.rng)
        }
    | uu____9214 -> mkApp ("Valid", [t]) t.rng
  
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
        let uu____9285 = FStar_Options.unthrottle_inductives ()  in
        if uu____9285
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
    let uu____9418 =
      let uu____9419 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9419 t t.rng  in
    FStar_All.pipe_right uu____9418 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9437 =
        let uu____9445 = let uu____9448 = mkInteger' i norng  in [uu____9448]
           in
        ("FString_const", uu____9445)  in
      mkApp uu____9437 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9479 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9479 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9526 =
         let uu____9534 =
           let uu____9537 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____9537]  in
         ("SFuel", uu____9534)  in
       mkApp uu____9526 norng)
  
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
            let uu____9585 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9585
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
      let uu____9648 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9648
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9668 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9668
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9679 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9679
  
let (dummy_sort : sort) = Sort "Dummy_sort" 