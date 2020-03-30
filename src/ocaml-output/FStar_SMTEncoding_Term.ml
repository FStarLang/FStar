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
    match projectee with | Integer _0 -> true | uu____890 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____913 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____936 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____966 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1015 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____1071 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1153 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1197 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____1242 -> false
  
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
    match projectee with | Name _0 -> true | uu____1432 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____1451 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____1471 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____1660 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____1683 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____1748 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____1806 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____1826 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____1855 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____1895 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____1915 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____1940 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____1967 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____1978 -> false 
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1989 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____2000 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____2018 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____2054 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____2065 -> false
  
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
          let uu____2239 =
            let uu____2240 =
              let sm = FStar_Util.smap_create (Prims.of_int (20))  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____2266 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2240
            }  in
          [uu____2239]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____2280 =
      let uu____2281 =
        FStar_List.collect
          (fun uu___0_2288  ->
             match uu___0_2288 with
             | Assume a -> [a.assumption_name]
             | uu____2295 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2281
      }  in
    [uu____2280]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2332  -> match uu____2332 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____2352 = x  in
    match uu____2352 with | (nm,uu____2355,uu____2356) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____2367 = x  in
    match uu____2367 with | (uu____2368,sort,uu____2370) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____2382 = x  in
    match uu____2382 with | (uu____2384,uu____2385,force1) -> force1
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____2403 = fv_name x  in
      let uu____2405 = fv_name y  in uu____2403 = uu____2405
  
let (fvs_subset_of : fvs -> fvs -> Prims.bool) =
  fun x  ->
    fun y  ->
      let cmp_fv x1 y1 =
        let uu____2432 = fv_name x1  in
        let uu____2434 = fv_name y1  in
        FStar_Util.compare uu____2432 uu____2434  in
      let uu____2436 = FStar_Util.as_set x cmp_fv  in
      let uu____2455 = FStar_Util.as_set y cmp_fv  in
      FStar_Util.set_is_subset_of uu____2436 uu____2455
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____2513 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___1_2524  ->
    match uu___1_2524 with
    | { tm = FreeV x; freevars = uu____2526; rng = uu____2527;_} -> fv_sort x
    | uu____2548 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___2_2555  ->
    match uu___2_2555 with
    | { tm = FreeV fv; freevars = uu____2557; rng = uu____2558;_} -> fv
    | uu____2579 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____2607 -> []
    | Real uu____2617 -> []
    | BoundV uu____2627 -> []
    | FreeV fv when fv_force fv -> []
    | FreeV fv -> [fv]
    | App (uu____2679,tms) -> FStar_List.collect freevars tms
    | Quant (uu____2693,uu____2694,uu____2695,uu____2696,t1) -> freevars t1
    | Labeled (t1,uu____2717,uu____2718) -> freevars t1
    | LblPos (t1,uu____2722) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____2745 = FStar_ST.op_Bang t.freevars  in
    match uu____2745 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____2843 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____2843  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2922  ->
    match uu___3_2922 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___4_2932  ->
    match uu___4_2932 with
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
        let uu____2968 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2968
    | NatToBv n1 ->
        let uu____2973 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____2973
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_2987  ->
    match uu___5_2987 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2997 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____2997
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____3019 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____3019
    | FreeV x ->
        let uu____3031 = fv_name x  in
        let uu____3033 =
          let uu____3035 = let uu____3037 = fv_sort x  in strSort uu____3037
             in
          Prims.op_Hat ":" uu____3035  in
        Prims.op_Hat uu____3031 uu____3033
    | App (op,tms) ->
        let uu____3045 =
          let uu____3047 = op_to_string op  in
          let uu____3049 =
            let uu____3051 =
              let uu____3053 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____3053 (FStar_String.concat " ")  in
            Prims.op_Hat uu____3051 ")"  in
          Prims.op_Hat uu____3047 uu____3049  in
        Prims.op_Hat "(" uu____3045
    | Labeled (t1,r1,r2) ->
        let uu____3070 = hash_of_term t1  in
        let uu____3072 =
          let uu____3074 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____3074  in
        Prims.op_Hat uu____3070 uu____3072
    | LblPos (t1,r) ->
        let uu____3080 =
          let uu____3082 = hash_of_term t1  in
          Prims.op_Hat uu____3082
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____3080
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____3110 =
          let uu____3112 =
            let uu____3114 =
              let uu____3116 =
                let uu____3118 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____3118 (FStar_String.concat " ")  in
              let uu____3128 =
                let uu____3130 =
                  let uu____3132 = hash_of_term body  in
                  let uu____3134 =
                    let uu____3136 =
                      let uu____3138 = weightToSmt wopt  in
                      let uu____3140 =
                        let uu____3142 =
                          let uu____3144 =
                            let uu____3146 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____3165 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____3165
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____3146
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____3144 "))"  in
                        Prims.op_Hat " " uu____3142  in
                      Prims.op_Hat uu____3138 uu____3140  in
                    Prims.op_Hat " " uu____3136  in
                  Prims.op_Hat uu____3132 uu____3134  in
                Prims.op_Hat ")(! " uu____3130  in
              Prims.op_Hat uu____3116 uu____3128  in
            Prims.op_Hat " (" uu____3114  in
          Prims.op_Hat (qop_to_string qop) uu____3112  in
        Prims.op_Hat "(" uu____3110
    | Let (es,body) ->
        let uu____3192 =
          let uu____3194 =
            let uu____3196 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____3196 (FStar_String.concat " ")  in
          let uu____3206 =
            let uu____3208 =
              let uu____3210 = hash_of_term body  in
              Prims.op_Hat uu____3210 ")"  in
            Prims.op_Hat ") " uu____3208  in
          Prims.op_Hat uu____3194 uu____3206  in
        Prims.op_Hat "(let (" uu____3192

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____3271 =
      let uu____3273 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____3273  in
    mkBoxFunctions uu____3271
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.of_int (3))
    then
      (let uu____3298 =
         FStar_String.substring s Prims.int_zero (Prims.of_int (3))  in
       uu____3298 = "Box") &&
        (let uu____3305 =
           let uu____3307 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____3307  in
         Prims.op_Negation uu____3305)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____3331 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____3331; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3395 =
        let uu____3396 = FStar_Util.ensure_decimal i  in Integer uu____3396
         in
      mk uu____3395 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____3411 = FStar_Util.string_of_int i  in mkInteger uu____3411 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3489  ->
    fun r  -> match uu____3489 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____3519) -> mkFalse r
      | App (FalseOp ,uu____3524) -> mkTrue r
      | uu____3529 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3545  ->
    fun r  ->
      match uu____3545 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3553),uu____3554) -> t2
           | (uu____3559,App (TrueOp ,uu____3560)) -> t1
           | (App (FalseOp ,uu____3565),uu____3566) -> mkFalse r
           | (uu____3571,App (FalseOp ,uu____3572)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3589,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____3598) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3605 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3625  ->
    fun r  ->
      match uu____3625 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____3633),uu____3634) -> mkTrue r
           | (uu____3639,App (TrueOp ,uu____3640)) -> mkTrue r
           | (App (FalseOp ,uu____3645),uu____3646) -> t2
           | (uu____3651,App (FalseOp ,uu____3652)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3669,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____3678) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3685 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3705  ->
    fun r  ->
      match uu____3705 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3713,App (TrueOp ,uu____3714)) -> mkTrue r
           | (App (FalseOp ,uu____3719),uu____3720) -> mkTrue r
           | (App (TrueOp ,uu____3725),uu____3726) -> t2
           | (uu____3731,App (Imp ,t1'::t2'::[])) ->
               let uu____3736 =
                 let uu____3743 =
                   let uu____3746 = mkAnd (t1, t1') r  in [uu____3746; t2']
                    in
                 (Imp, uu____3743)  in
               mkApp' uu____3736 r
           | uu____3749 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____3774  ->
      fun r  -> match uu____3774 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____3934  ->
      fun r  ->
        match uu____3934 with
        | (t1,t2) ->
            let uu____3943 =
              let uu____3950 =
                let uu____3953 =
                  let uu____3956 = mkNatToBv sz t2 r  in [uu____3956]  in
                t1 :: uu____3953  in
              (BvShl, uu____3950)  in
            mkApp' uu____3943 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____3978  ->
      fun r  ->
        match uu____3978 with
        | (t1,t2) ->
            let uu____3987 =
              let uu____3994 =
                let uu____3997 =
                  let uu____4000 = mkNatToBv sz t2 r  in [uu____4000]  in
                t1 :: uu____3997  in
              (BvShr, uu____3994)  in
            mkApp' uu____3987 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4022  ->
      fun r  ->
        match uu____4022 with
        | (t1,t2) ->
            let uu____4031 =
              let uu____4038 =
                let uu____4041 =
                  let uu____4044 = mkNatToBv sz t2 r  in [uu____4044]  in
                t1 :: uu____4041  in
              (BvUdiv, uu____4038)  in
            mkApp' uu____4031 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4066  ->
      fun r  ->
        match uu____4066 with
        | (t1,t2) ->
            let uu____4075 =
              let uu____4082 =
                let uu____4085 =
                  let uu____4088 = mkNatToBv sz t2 r  in [uu____4088]  in
                t1 :: uu____4085  in
              (BvMod, uu____4082)  in
            mkApp' uu____4075 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____4110  ->
      fun r  ->
        match uu____4110 with
        | (t1,t2) ->
            let uu____4119 =
              let uu____4126 =
                let uu____4129 =
                  let uu____4132 = mkNatToBv sz t2 r  in [uu____4132]  in
                t1 :: uu____4129  in
              (BvMul, uu____4126)  in
            mkApp' uu____4119 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4174  ->
    fun r  ->
      match uu____4174 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4193 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____4358  ->
    fun r  ->
      match uu____4358 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____4369) -> t2
           | App (FalseOp ,uu____4374) -> t3
           | uu____4379 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____4380),App (TrueOp ,uu____4381)) ->
                    mkTrue r
                | (App (TrueOp ,uu____4390),uu____4391) ->
                    let uu____4396 =
                      let uu____4401 = mkNot t1 t1.rng  in (uu____4401, t3)
                       in
                    mkImp uu____4396 r
                | (uu____4402,App (TrueOp ,uu____4403)) -> mkImp (t1, t2) r
                | (uu____4408,uu____4409) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____4465 -> FStar_Pervasives_Native.None
      | Real uu____4467 -> FStar_Pervasives_Native.None
      | BoundV uu____4469 -> FStar_Pervasives_Native.None
      | FreeV uu____4471 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____4495 -> true
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
            | BvUext uu____4528 -> false
            | NatToBv uu____4531 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____4542,uu____4543) -> aux t2
      | Quant uu____4546 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4566 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4581 = aux t1  in
          (match uu____4581 with
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
        let uu____4619 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____4619
    | FreeV fv ->
        let uu____4631 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____4631
    | App (op,l) ->
        let uu____4640 = op_to_string op  in
        let uu____4642 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____4640 uu____4642
    | Labeled (t1,r1,r2) ->
        let uu____4650 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4650
    | LblPos (t1,s) ->
        let uu____4657 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4657
    | Quant (qop,l,uu____4662,uu____4663,t1) ->
        let uu____4683 = print_smt_term_list_list l  in
        let uu____4685 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4683
          uu____4685
    | Let (es,body) ->
        let uu____4694 = print_smt_term_list es  in
        let uu____4696 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____4694 uu____4696

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____4703 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____4703 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4730 =
             let uu____4732 =
               let uu____4734 = print_smt_term_list l1  in
               Prims.op_Hat uu____4734 " ] "  in
             Prims.op_Hat "; [ " uu____4732  in
           Prims.op_Hat s uu____4730) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____4774  ->
        match uu____4774 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4843 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____4843 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4858 =
                         let uu____4864 =
                           let uu____4866 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4866
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____4864)
                          in
                       FStar_Errors.log_issue r uu____4858);
                      []))
               in
            if (FStar_List.length vars) = Prims.int_zero
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____4877) -> body
               | uu____4882 ->
                   let uu____4883 =
                     let uu____4884 =
                       let uu____4904 = all_pats_ok pats  in
                       (qop, uu____4904, wopt, vars, body)  in
                     Quant uu____4884  in
                   mk uu____4883 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4933  ->
    fun r  ->
      match uu____4933 with
      | (es,body) ->
          if (FStar_List.length es) = Prims.int_zero
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____4979 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____4979 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some (nvars - (i + Prims.int_one))
         in
      let rec aux ix t1 =
        let uu____5006 = FStar_ST.op_Bang t1.freevars  in
        match uu____5006 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____5080 ->
            (match t1.tm with
             | Integer uu____5093 -> t1
             | Real uu____5095 -> t1
             | BoundV uu____5097 -> t1
             | FreeV x ->
                 let uu____5108 = index_of1 x  in
                 (match uu____5108 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____5122 =
                   let uu____5129 = FStar_List.map (aux ix) tms  in
                   (op, uu____5129)  in
                 mkApp' uu____5122 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____5139 =
                   let uu____5140 =
                     let uu____5148 = aux ix t2  in (uu____5148, r1, r2)  in
                   Labeled uu____5140  in
                 mk uu____5139 t2.rng
             | LblPos (t2,r) ->
                 let uu____5154 =
                   let uu____5155 =
                     let uu____5161 = aux ix t2  in (uu____5161, r)  in
                   LblPos uu____5155  in
                 mk uu____5154 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____5187 =
                   let uu____5207 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____5224 = aux (ix + n1) body  in
                   (qop, uu____5207, wopt, vars, uu____5224)  in
                 mkQuant t1.rng false uu____5187
             | Let (es,body) ->
                 let uu____5241 =
                   FStar_List.fold_left
                     (fun uu____5261  ->
                        fun e  ->
                          match uu____5261 with
                          | (ix1,l) ->
                              let uu____5285 =
                                let uu____5288 = aux ix1 e  in uu____5288 ::
                                  l
                                 in
                              ((ix1 + Prims.int_one), uu____5285)) (ix, [])
                     es
                    in
                 (match uu____5241 with
                  | (ix1,es_rev) ->
                      let uu____5304 =
                        let uu____5311 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____5311)  in
                      mkLet uu____5304 t1.rng))
         in
      aux Prims.int_zero t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____5347 -> t1
        | Real uu____5349 -> t1
        | FreeV uu____5351 -> t1
        | BoundV i ->
            if (Prims.int_zero <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____5372 =
              let uu____5379 = FStar_List.map (aux shift) tms2  in
              (op, uu____5379)  in
            mkApp' uu____5372 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____5389 =
              let uu____5390 =
                let uu____5398 = aux shift t2  in (uu____5398, r1, r2)  in
              Labeled uu____5390  in
            mk uu____5389 t2.rng
        | LblPos (t2,r) ->
            let uu____5404 =
              let uu____5405 =
                let uu____5411 = aux shift t2  in (uu____5411, r)  in
              LblPos uu____5405  in
            mk uu____5404 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____5439 =
              let uu____5459 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____5476 = aux shift1 body  in
              (qop, uu____5459, wopt, vars, uu____5476)  in
            mkQuant t1.rng false uu____5439
        | Let (es,body) ->
            let uu____5493 =
              FStar_List.fold_left
                (fun uu____5513  ->
                   fun e  ->
                     match uu____5513 with
                     | (ix,es1) ->
                         let uu____5537 =
                           let uu____5540 = aux shift e  in uu____5540 :: es1
                            in
                         ((shift + Prims.int_one), uu____5537)) (shift, [])
                es
               in
            (match uu____5493 with
             | (shift1,es_rev) ->
                 let uu____5556 =
                   let uu____5563 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____5563)  in
                 mkLet uu____5556 t1.rng)
         in
      aux Prims.int_zero t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____5583 = abstr [fv] t  in inst [s] uu____5583
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5613  ->
      match uu____5613 with
      | (qop,pats,wopt,vars,body) ->
          let uu____5656 =
            let uu____5676 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____5693 = FStar_List.map fv_sort vars  in
            let uu____5696 = abstr vars body  in
            (qop, uu____5676, wopt, uu____5693, uu____5696)  in
          mkQuant r true uu____5656
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5727  ->
      match uu____5727 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____5786  ->
      match uu____5786 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____5861  ->
      match uu____5861 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____5924  ->
      match uu____5924 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5975  ->
    fun r  ->
      match uu____5975 with
      | (bindings,body) ->
          let uu____6001 = FStar_List.split bindings  in
          (match uu____6001 with
           | (vars,es) ->
               let uu____6020 =
                 let uu____6027 = abstr vars body  in (es, uu____6027)  in
               mkLet uu____6020 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____6049  ->
    match uu____6049 with
    | (nm,vars,s,tm,c) ->
        let uu____6074 =
          let uu____6088 = FStar_List.map fv_sort vars  in
          let uu____6091 = abstr vars tm  in
          (nm, uu____6088, s, uu____6091, c)  in
        DefineFun uu____6074
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____6102 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____6102
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____6120  ->
    fun id1  ->
      match uu____6120 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____6136 =
              let uu____6137 =
                let uu____6142 = mkInteger' id1 norng  in
                let uu____6143 =
                  let uu____6144 =
                    let uu____6152 = constr_id_of_sort sort  in
                    let uu____6154 =
                      let uu____6157 = mkApp (tok_name, []) norng  in
                      [uu____6157]  in
                    (uu____6152, uu____6154)  in
                  mkApp uu____6144 norng  in
                (uu____6142, uu____6143)  in
              mkEq uu____6137 norng  in
            let uu____6164 = escape a_name  in
            {
              assumption_term = uu____6136;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____6164;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____6190  ->
      match uu____6190 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____6230 =
                        let uu____6231 =
                          let uu____6237 =
                            let uu____6239 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____6239  in
                          (uu____6237, s)  in
                        mk_fv uu____6231  in
                      mkFreeV uu____6230 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____6267 =
              let uu____6275 = constr_id_of_sort sort  in
              (uu____6275, [capp])  in
            mkApp uu____6267 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____6284 =
              let uu____6285 =
                let uu____6296 =
                  let uu____6297 =
                    let uu____6302 = mkInteger id2 norng  in
                    (uu____6302, cid_app)  in
                  mkEq uu____6297 norng  in
                ([[capp]], bvar_names, uu____6296)  in
              mkForall rng uu____6285  in
            let uu____6311 = escape a_name  in
            {
              assumption_term = uu____6284;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6311;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____6336  ->
      match uu____6336 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____6369 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____6369  in
          let bvar_index i = n_bvars - (i + Prims.int_one)  in
          let bvar i s =
            let uu____6398 =
              let uu____6399 =
                let uu____6405 = bvar_name i  in (uu____6405, s)  in
              mk_fv uu____6399  in
            FStar_All.pipe_left mkFreeV uu____6398  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6441  ->
                      match uu____6441 with
                      | (uu____6451,s,uu____6453) ->
                          let uu____6458 = bvar i s  in uu____6458 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____6486 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____6524  ->
                      match uu____6524 with
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
                              let uu____6557 =
                                let uu____6558 =
                                  let uu____6569 =
                                    let uu____6570 =
                                      let uu____6575 =
                                        let uu____6576 = bvar i s  in
                                        uu____6576 norng  in
                                      (cproj_app, uu____6575)  in
                                    mkEq uu____6570 norng  in
                                  ([[capp]], bvar_names, uu____6569)  in
                                mkForall rng uu____6558  in
                              let uu____6589 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____6557;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6589;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____6486 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____6614  ->
      match uu____6614 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6662  ->
                    match uu____6662 with
                    | (uu____6671,sort1,uu____6673) -> sort1))
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
              let uu____6698 =
                let uu____6703 =
                  let uu____6704 =
                    let uu____6712 = constr_id_of_sort sort  in
                    (uu____6712, [xx])  in
                  mkApp uu____6704 norng  in
                let uu____6717 =
                  let uu____6718 = FStar_Util.string_of_int id1  in
                  mkInteger uu____6718 norng  in
                (uu____6703, uu____6717)  in
              mkEq uu____6698 norng  in
            let uu____6720 =
              let uu____6739 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____6803  ->
                          match uu____6803 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____6833 = mkApp (proj, [xx]) norng  in
                                (uu____6833, [])
                              else
                                (let fi =
                                   let uu____6842 =
                                     let uu____6848 =
                                       let uu____6850 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____6850  in
                                     (uu____6848, s)  in
                                   mk_fv uu____6842  in
                                 let uu____6854 = mkFreeV fi norng  in
                                 (uu____6854, [fi]))))
                 in
              FStar_All.pipe_right uu____6739 FStar_List.split  in
            match uu____6720 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____6951 =
                    let uu____6956 = mkApp (name, proj_terms) norng  in
                    (xx, uu____6956)  in
                  mkEq uu____6951 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____6969 ->
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
          let uu____7004 =
            let uu____7007 =
              let uu____7008 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____7008  in
            uu____7007 :: cdecl :: cid :: projs  in
          let uu____7011 =
            let uu____7014 =
              let uu____7017 =
                let uu____7018 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____7018  in
              [uu____7017]  in
            FStar_List.append [disc] uu____7014  in
          FStar_List.append uu____7004 uu____7011
  
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
          let uu____7070 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7119  ->
                    fun s  ->
                      match uu____7119 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____7164 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____7175 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____7175  in
                          let names2 =
                            let uu____7180 = mk_fv (nm, s)  in uu____7180 ::
                              names1
                             in
                          let b =
                            let uu____7184 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____7184  in
                          (names2, (b :: binders), (n1 + Prims.int_one)))
                 (outer_names, [], start))
             in
          match uu____7070 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____7255 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        Prims.int_zero sorts
       in
    match uu____7255 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
  
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  fun print_ranges  ->
    fun enclosing_name  ->
      fun t  ->
        let next_qid =
          let ctr = FStar_Util.mk_ref Prims.int_zero  in
          fun depth  ->
            let n1 = FStar_ST.op_Bang ctr  in
            FStar_Util.incr ctr;
            if n1 = Prims.int_zero
            then enclosing_name
            else
              (let uu____7364 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7364)
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
                               "Prims.guard_free",{ tm = BoundV uu____7410;
                                                    freevars = uu____7411;
                                                    rng = uu____7412;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____7433 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + Prims.int_one)  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7511 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____7511 fv_name
          | FreeV x when fv_force x ->
              let uu____7522 =
                let uu____7524 = fv_name x  in
                Prims.op_Hat uu____7524 " Dummy_value)"  in
              Prims.op_Hat "(" uu____7522
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____7546 = op_to_string op  in
              let uu____7548 =
                let uu____7550 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____7550 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____7546 uu____7548
          | Labeled (t2,uu____7562,uu____7563) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____7570 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7570 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____7598 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____7598 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7651 ->
                         let uu____7656 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____7675 =
                                     let uu____7677 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____7685 = aux1 n2 names2 p
                                               in
                                            FStar_Util.format1 "%s"
                                              uu____7685) pats2
                                        in
                                     FStar_String.concat " " uu____7677  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7675))
                            in
                         FStar_All.pipe_right uu____7656
                           (FStar_String.concat "\n")
                      in
                   let uu____7695 =
                     let uu____7699 =
                       let uu____7703 =
                         let uu____7707 = aux1 n2 names2 body  in
                         let uu____7709 =
                           let uu____7713 = weightToSmt wopt  in
                           [uu____7713; pats_str; qid]  in
                         uu____7707 :: uu____7709  in
                       binders1 :: uu____7703  in
                     (qop_to_string qop) :: uu____7699  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____7695)
          | Let (es,body) ->
              let uu____7729 =
                FStar_List.fold_left
                  (fun uu____7762  ->
                     fun e  ->
                       match uu____7762 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____7805 = FStar_Util.string_of_int n0  in
                             Prims.op_Hat "@lb" uu____7805  in
                           let names01 =
                             let uu____7811 = mk_fv (nm, Term_sort)  in
                             uu____7811 :: names0  in
                           let b =
                             let uu____7815 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____7815  in
                           (names01, (b :: binders), (n0 + Prims.int_one)))
                  (names1, [], n1) es
                 in
              (match uu____7729 with
               | (names2,binders,n2) ->
                   let uu____7849 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____7849)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____7865 = FStar_Range.string_of_range t1.rng  in
            let uu____7867 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____7865
              uu____7867 s
          else s
         in aux Prims.int_zero Prims.int_zero [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___6_7889  ->
      match uu___6_7889 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____7900 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____7900 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____7922 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____7975 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____7975 (FStar_String.concat "\n")  in
            let uu____7985 = FStar_Options.keep_query_captions ()  in
            if uu____7985
            then
              let uu____7989 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____7991 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start %s\n%s\n;;; End %s (%s decls; total size %s)" s
                res s uu____7989 uu____7991
            else res
        | Caption c ->
            if print_captions
            then
              let uu____8000 =
                let uu____8002 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____8002 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____8000
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____8043 = caption_to_string print_captions c  in
            let uu____8045 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8043 f
              (FStar_String.concat " " l) uu____8045
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____8060 = name_macro_binders arg_sorts  in
            (match uu____8060 with
             | (names1,binders) ->
                 let body1 =
                   let uu____8084 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____8084 body  in
                 let uu____8089 = caption_to_string print_captions c  in
                 let uu____8091 = strSort retsort  in
                 let uu____8093 =
                   let uu____8095 = escape f  in
                   termToSmt print_captions uu____8095 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8089 f (FStar_String.concat " " binders) uu____8091
                   uu____8093)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_8122  ->
                      match uu___7_8122 with
                      | Name n1 ->
                          let uu____8125 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____8125
                      | Namespace ns ->
                          let uu____8129 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____8129
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____8139 =
                  let uu____8141 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____8141  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8139
              else ""  in
            let n1 = a.assumption_name  in
            let uu____8152 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____8154 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8152
              fids uu____8154 n1
        | Eval t ->
            let uu____8158 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____8158
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8165 -> ""
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
      let uu____8186 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____8186 z3options decl

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.op_Hat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n(declare-fun IsTotFun (Term) Bool)\n\n                ;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))"
       in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, Prims.int_zero, true);
      ("Tm_type", [], Term_sort, (Prims.of_int (2)), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.of_int (3)), false);
      ("Tm_unit", [], Term_sort, (Prims.of_int (6)), true);
      ((FStar_Pervasives_Native.fst boxIntFun),
        [((FStar_Pervasives_Native.snd boxIntFun), Int_sort, true)],
        Term_sort, (Prims.of_int (7)), true);
      ((FStar_Pervasives_Native.fst boxBoolFun),
        [((FStar_Pervasives_Native.snd boxBoolFun), Bool_sort, true)],
        Term_sort, (Prims.of_int (8)), true);
      ((FStar_Pervasives_Native.fst boxStringFun),
        [((FStar_Pervasives_Native.snd boxStringFun), String_sort, true)],
        Term_sort, (Prims.of_int (9)), true);
      ((FStar_Pervasives_Native.fst boxRealFun),
        [((FStar_Pervasives_Native.snd boxRealFun), (Sort "Real"), true)],
        Term_sort, (Prims.of_int (10)), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true);
        ("LexCons_1", Term_sort, true);
        ("LexCons_2", Term_sort, true)], Term_sort, (Prims.of_int (11)),
        true)]
       in
    let bcons =
      let uu____8313 =
        let uu____8317 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____8317
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____8313 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n"
       in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n"
       in
    let uu____8344 =
      let uu____8346 =
        let uu____8348 =
          let uu____8350 =
            let uu____8352 = FStar_Options.smtencoding_valid_intro ()  in
            if uu____8352 then valid_intro else ""  in
          let uu____8359 =
            let uu____8361 = FStar_Options.smtencoding_valid_elim ()  in
            if uu____8361 then valid_elim else ""  in
          Prims.op_Hat uu____8350 uu____8359  in
        Prims.op_Hat lex_ordering uu____8348  in
      Prims.op_Hat bcons uu____8346  in
    Prims.op_Hat basic uu____8344

let (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____8386 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____8386 (FStar_String.concat "\n")
  
let (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl 
let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____8421 =
      let uu____8422 =
        let uu____8424 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8424  in
      let uu____8433 =
        let uu____8436 =
          let uu____8437 =
            let uu____8439 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____8439  in
          (uu____8437, (BitVec_sort sz), true)  in
        [uu____8436]  in
      (uu____8422, uu____8433, Term_sort, ((Prims.of_int (12)) + sz), true)
       in
    FStar_All.pipe_right uu____8421 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero 
let (mk_Range_const : unit -> term) =
  fun uu____8471  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____8496 =
       let uu____8498 = FStar_ST.op_Bang __range_c  in
       uu____8498 + Prims.int_one  in
     FStar_ST.op_Colon_Equals __range_c uu____8496);
    (let uu____8543 =
       let uu____8551 = let uu____8554 = mkInteger' i norng  in [uu____8554]
          in
       ("Range_const", uu____8551)  in
     mkApp uu____8543 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____8597 =
        let uu____8605 = let uu____8608 = mkInteger' i norng  in [uu____8608]
           in
        ("Tm_uvar", uu____8605)  in
      mkApp uu____8597 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____8651 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____8675 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____8675 u v1 t
  
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
      let uu____8770 =
        let uu____8772 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8772  in
      let uu____8781 =
        let uu____8783 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8783  in
      elim_box true uu____8770 uu____8781 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____8806 =
        let uu____8808 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____8808  in
      let uu____8817 =
        let uu____8819 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____8819  in
      elim_box true uu____8806 uu____8817 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____8843 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____8858 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____8884 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____8884
         | uu____8887 -> FStar_Pervasives_Native.None)
    | uu____8889 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____8907::t1::t2::[]);
                       freevars = uu____8910; rng = uu____8911;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____8930::t1::t2::[]);
                       freevars = uu____8933; rng = uu____8934;_}::[])
        -> let uu____8953 = mkEq (t1, t2) norng  in mkNot uu____8953 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____8956; rng = uu____8957;_}::[])
        ->
        let uu____8976 =
          let uu____8981 = unboxInt t1  in
          let uu____8982 = unboxInt t2  in (uu____8981, uu____8982)  in
        mkLTE uu____8976 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____8985; rng = uu____8986;_}::[])
        ->
        let uu____9005 =
          let uu____9010 = unboxInt t1  in
          let uu____9011 = unboxInt t2  in (uu____9010, uu____9011)  in
        mkLT uu____9005 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____9014; rng = uu____9015;_}::[])
        ->
        let uu____9034 =
          let uu____9039 = unboxInt t1  in
          let uu____9040 = unboxInt t2  in (uu____9039, uu____9040)  in
        mkGTE uu____9034 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____9043; rng = uu____9044;_}::[])
        ->
        let uu____9063 =
          let uu____9068 = unboxInt t1  in
          let uu____9069 = unboxInt t2  in (uu____9068, uu____9069)  in
        mkGT uu____9063 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____9072; rng = uu____9073;_}::[])
        ->
        let uu____9092 =
          let uu____9097 = unboxBool t1  in
          let uu____9098 = unboxBool t2  in (uu____9097, uu____9098)  in
        mkAnd uu____9092 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____9101; rng = uu____9102;_}::[])
        ->
        let uu____9121 =
          let uu____9126 = unboxBool t1  in
          let uu____9127 = unboxBool t2  in (uu____9126, uu____9127)  in
        mkOr uu____9121 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____9129; rng = uu____9130;_}::[])
        -> let uu____9149 = unboxBool t1  in mkNot uu____9149 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____9153; rng = uu____9154;_}::[])
        when
        let uu____9173 = getBoxedInteger t0  in FStar_Util.is_some uu____9173
        ->
        let sz =
          let uu____9180 = getBoxedInteger t0  in
          match uu____9180 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9188 -> failwith "impossible"  in
        let uu____9194 =
          let uu____9199 = unboxBitVec sz t1  in
          let uu____9200 = unboxBitVec sz t2  in (uu____9199, uu____9200)  in
        mkBvUlt uu____9194 t.rng
    | App
        (Var
         "Prims.equals",uu____9201::{
                                      tm = App
                                        (Var "FStar.BV.bvult",t0::t1::t2::[]);
                                      freevars = uu____9205;
                                      rng = uu____9206;_}::uu____9207::[])
        when
        let uu____9226 = getBoxedInteger t0  in FStar_Util.is_some uu____9226
        ->
        let sz =
          let uu____9233 = getBoxedInteger t0  in
          match uu____9233 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9241 -> failwith "impossible"  in
        let uu____9247 =
          let uu____9252 = unboxBitVec sz t1  in
          let uu____9253 = unboxBitVec sz t2  in (uu____9252, uu____9253)  in
        mkBvUlt uu____9247 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1398_9258 = unboxBool t1  in
        {
          tm = (uu___1398_9258.tm);
          freevars = (uu___1398_9258.freevars);
          rng = (t.rng)
        }
    | uu____9259 -> mkApp ("Valid", [t]) t.rng
  
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
        let uu____9330 = FStar_Options.unthrottle_inductives ()  in
        if uu____9330
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
    let uu____9463 =
      let uu____9464 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____9464 t t.rng  in
    FStar_All.pipe_right uu____9463 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____9482 =
        let uu____9490 = let uu____9493 = mkInteger' i norng  in [uu____9493]
           in
        ("FString_const", uu____9490)  in
      mkApp uu____9482 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____9524 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r  in
            FStar_All.pipe_right uu____9524 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = Prims.int_zero
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9571 =
         let uu____9579 =
           let uu____9582 = n_fuel (n1 - Prims.int_one)  in [uu____9582]  in
         ("SFuel", uu____9579)  in
       mkApp uu____9571 norng)
  
let (fuel_2 : term) = n_fuel (Prims.of_int (2)) 
let (fuel_100 : term) = n_fuel (Prims.of_int (100)) 
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
            let uu____9630 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____9630
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
      let uu____9693 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____9693
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____9713 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____9713
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____9724 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____9724
  
let (dummy_sort : sort) = Sort "Dummy_sort" 