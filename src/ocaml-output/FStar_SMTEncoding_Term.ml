open Prims
let (escape : Prims.string -> Prims.string) =
  fun s -> FStar_Util.replace_char s 39 95
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
  fun projectee ->
    match projectee with | Bool_sort -> true | uu____60 -> false
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Int_sort -> true | uu____71 -> false
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | String_sort -> true | uu____82 -> false
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_sort -> true | uu____93 -> false
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Fuel_sort -> true | uu____104 -> false
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | BitVec_sort _0 -> true | uu____117 -> false
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee -> match projectee with | BitVec_sort _0 -> _0
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Array _0 -> true | uu____143 -> false
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Array _0 -> _0
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrow _0 -> true | uu____178 -> false
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Sort _0 -> true | uu____210 -> false
let (__proj__Sort__item___0 : sort -> Prims.string) =
  fun projectee -> match projectee with | Sort _0 -> _0
let rec (strSort : sort -> Prims.string) =
  fun x ->
    match x with
    | Bool_sort -> "Bool"
    | Int_sort -> "Int"
    | Term_sort -> "Term"
    | String_sort -> "FString"
    | Fuel_sort -> "Fuel"
    | BitVec_sort n1 ->
        let uu____237 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ BitVec %s)" uu____237
    | Array (s1, s2) ->
        let uu____242 = strSort s1 in
        let uu____244 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____242 uu____244
    | Arrow (s1, s2) ->
        let uu____249 = strSort s1 in
        let uu____251 = strSort s2 in
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
  fun projectee -> match projectee with | TrueOp -> true | uu____283 -> false
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee ->
    match projectee with | FalseOp -> true | uu____294 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____305 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____316 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____327 -> false
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee -> match projectee with | Imp -> true | uu____338 -> false
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee -> match projectee with | Iff -> true | uu____349 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____360 -> false
let (uu___is_LT : op -> Prims.bool) =
  fun projectee -> match projectee with | LT -> true | uu____371 -> false
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee -> match projectee with | LTE -> true | uu____382 -> false
let (uu___is_GT : op -> Prims.bool) =
  fun projectee -> match projectee with | GT -> true | uu____393 -> false
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee -> match projectee with | GTE -> true | uu____404 -> false
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____415 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____426 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____437 -> false
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee ->
    match projectee with | RealDiv -> true | uu____448 -> false
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee -> match projectee with | Mul -> true | uu____459 -> false
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee -> match projectee with | Minus -> true | uu____470 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____481 -> false
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAnd -> true | uu____492 -> false
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BvXor -> true | uu____503 -> false
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvOr -> true | uu____514 -> false
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAdd -> true | uu____525 -> false
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee -> match projectee with | BvSub -> true | uu____536 -> false
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShl -> true | uu____547 -> false
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShr -> true | uu____558 -> false
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUdiv -> true | uu____569 -> false
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMod -> true | uu____580 -> false
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMul -> true | uu____591 -> false
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUlt -> true | uu____602 -> false
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BvUext _0 -> true | uu____615 -> false
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | BvUext _0 -> _0
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee ->
    match projectee with | NatToBv _0 -> true | uu____638 -> false
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | NatToBv _0 -> _0
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BvToNat -> true | uu____659 -> false
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee -> match projectee with | ITE -> true | uu____670 -> false
let (uu___is_Var : op -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu____683 -> false
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee -> match projectee with | Var _0 -> _0
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee -> match projectee with | Forall -> true | uu____704 -> false
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee -> match projectee with | Exists -> true | uu____715 -> false
type term' =
  | Integer of Prims.string 
  | Real of Prims.string 
  | BoundV of Prims.int 
  | FreeV of (Prims.string * sort * Prims.bool) 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int
  FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string
  FStar_Syntax_Syntax.memo) 
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
  fun projectee ->
    match projectee with | Integer _0 -> true | uu____879 -> false
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Integer _0 -> _0
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Real _0 -> true | uu____902 -> false
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Real _0 -> _0
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | BoundV _0 -> true | uu____925 -> false
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee -> match projectee with | BoundV _0 -> _0
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | FreeV _0 -> true | uu____955 -> false
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee -> match projectee with | FreeV _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | App _0 -> true | uu____1004 -> false
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quant _0 -> true | uu____1065 -> false
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term * Prims.string
      FStar_Syntax_Syntax.memo))
  = fun projectee -> match projectee with | Quant _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Let _0 -> true | uu____1162 -> false
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Labeled _0 -> true | uu____1206 -> false
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LblPos _0 -> true | uu____1251 -> false
let (__proj__LblPos__item___0 : term' -> (term * Prims.string)) =
  fun projectee -> match projectee with | LblPos _0 -> _0
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> tm
let (__proj__Mkterm__item__freevars :
  term ->
    (Prims.string * sort * Prims.bool) Prims.list FStar_Syntax_Syntax.memo)
  =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> freevars
let (__proj__Mkterm__item__rng : term -> FStar_Range.range) =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> rng
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
  fun projectee ->
    match projectee with | Name _0 -> true | uu____1441 -> false
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee ->
    match projectee with | Namespace _0 -> true | uu____1460 -> false
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Namespace _0 -> _0
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee ->
    match projectee with | Tag _0 -> true | uu____1480 -> false
let (__proj__Tag__item___0 : fact_db_id -> Prims.string) =
  fun projectee -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list }
let (__proj__Mkassumption__item__assumption_term : assumption -> term) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_term
let (__proj__Mkassumption__item__assumption_caption : assumption -> caption)
  =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_caption
let (__proj__Mkassumption__item__assumption_name :
  assumption -> Prims.string) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids;_} -> assumption_name
let (__proj__Mkassumption__item__assumption_fact_ids :
  assumption -> fact_db_id Prims.list) =
  fun projectee ->
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
  fun projectee ->
    match projectee with | DefPrelude -> true | uu____1669 -> false
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclFun _0 -> true | uu____1692 -> false
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee -> match projectee with | DeclFun _0 -> _0
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineFun _0 -> true | uu____1757 -> false
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee -> match projectee with | DefineFun _0 -> _0
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Assume _0 -> true | uu____1815 -> false
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Caption _0 -> true | uu____1835 -> false
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Caption _0 -> _0
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____1864 -> false
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Eval _0 -> true | uu____1904 -> false
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee -> match projectee with | Eval _0 -> _0
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Echo _0 -> true | uu____1924 -> false
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Echo _0 -> _0
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RetainAssumptions _0 -> true | uu____1949 -> false
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee -> match projectee with | RetainAssumptions _0 -> _0
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee -> match projectee with | Push -> true | uu____1976 -> false
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____1987 -> false
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckSat -> true | uu____1998 -> false
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetUnsatCore -> true | uu____2009 -> false
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOption _0 -> true | uu____2027 -> false
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | SetOption _0 -> _0
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetStatistics -> true | uu____2063 -> false
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetReasonUnknown -> true | uu____2074 -> false
type decls_elt =
  {
  sym_name: Prims.string FStar_Pervasives_Native.option ;
  key: Prims.string FStar_Pervasives_Native.option ;
  decls: decl Prims.list ;
  a_names: Prims.string Prims.list }
let (__proj__Mkdecls_elt__item__sym_name :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> sym_name
let (__proj__Mkdecls_elt__item__key :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> key
let (__proj__Mkdecls_elt__item__decls : decls_elt -> decl Prims.list) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> decls
let (__proj__Mkdecls_elt__item__a_names :
  decls_elt -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> a_names
type decls_t = decls_elt Prims.list
let (mk_decls :
  Prims.string ->
    Prims.string -> decl Prims.list -> decls_elt Prims.list -> decls_t)
  =
  fun name ->
    fun key ->
      fun decls ->
        fun aux_decls ->
          let uu____2248 =
            let uu____2249 =
              let sm = FStar_Util.smap_create (Prims.of_int (20)) in
              FStar_List.iter
                (fun elt ->
                   FStar_List.iter (fun s -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____2275 -> ()) decls;
              FStar_Util.smap_keys sm in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____2249
            } in
          [uu____2248]
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls ->
    let uu____2289 =
      let uu____2290 =
        FStar_List.collect
          (fun uu___0_2297 ->
             match uu___0_2297 with
             | Assume a -> [a.assumption_name]
             | uu____2304 -> []) decls in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____2290
      } in
    [uu____2289]
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l -> FStar_All.pipe_right l (FStar_List.collect (fun elt -> elt.decls))
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____2341 -> match uu____2341 with | (x, y) -> (x, y, false)
let (fv_name : fv -> Prims.string) =
  fun x ->
    let uu____2361 = x in
    match uu____2361 with | (nm, uu____2364, uu____2365) -> nm
let (fv_sort : fv -> sort) =
  fun x ->
    let uu____2376 = x in
    match uu____2376 with | (uu____2377, sort, uu____2379) -> sort
let (fv_force : fv -> Prims.bool) =
  fun x ->
    let uu____2391 = x in
    match uu____2391 with | (uu____2393, uu____2394, force) -> force
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x ->
    fun y ->
      let uu____2412 = fv_name x in
      let uu____2414 = fv_name y in uu____2412 = uu____2414
let (fvs_subset_of : fvs -> fvs -> Prims.bool) =
  fun x ->
    fun y ->
      let cmp_fv x1 y1 =
        let uu____2441 = fv_name x1 in
        let uu____2443 = fv_name y1 in
        FStar_Util.compare uu____2441 uu____2443 in
      let uu____2445 = FStar_Util.as_set x cmp_fv in
      let uu____2464 = FStar_Util.as_set y cmp_fv in
      FStar_Util.set_is_subset_of uu____2445 uu____2464
let (freevar_eq : term -> term -> Prims.bool) =
  fun x ->
    fun y ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1, FreeV y1) -> fv_eq x1 y1
      | uu____2522 -> false
let (freevar_sort : term -> sort) =
  fun uu___1_2533 ->
    match uu___1_2533 with
    | { tm = FreeV x; freevars = uu____2535; rng = uu____2536;_} -> fv_sort x
    | uu____2557 -> failwith "impossible"
let (fv_of_term : term -> fv) =
  fun uu___2_2564 ->
    match uu___2_2564 with
    | { tm = FreeV fv; freevars = uu____2566; rng = uu____2567;_} -> fv
    | uu____2588 -> failwith "impossible"
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t ->
    match t.tm with
    | Integer uu____2616 -> []
    | Real uu____2626 -> []
    | BoundV uu____2636 -> []
    | FreeV fv when fv_force fv -> []
    | FreeV fv -> [fv]
    | App (uu____2688, tms) -> FStar_List.collect freevars tms
    | Quant (uu____2702, uu____2703, uu____2704, uu____2705, t1, uu____2707)
        -> freevars t1
    | Labeled (t1, uu____2733, uu____2734) -> freevars t1
    | LblPos (t1, uu____2738) -> freevars t1
    | Let (es, body) -> FStar_List.collect freevars (body :: es)
let (free_variables : term -> fvs) =
  fun t ->
    let uu____2761 = FStar_ST.op_Bang t.freevars in
    match uu____2761 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None ->
        let fvs =
          let uu____2859 = freevars t in
          FStar_Util.remove_dups fv_eq uu____2859 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2938 ->
    match uu___3_2938 with | Forall -> "forall" | Exists -> "exists"
let (op_to_string : op -> Prims.string) =
  fun uu___4_2948 ->
    match uu___4_2948 with
    | TrueOp -> "true"
    | FalseOp -> "false"
    | Not -> "not"
    | And -> "and"
    | Or -> "or"
    | Imp -> "implies"
    | Iff -> "iff"
    | Eq -> "="
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="
    | Add -> "+"
    | Sub -> "-"
    | Div -> "div"
    | RealDiv -> "/"
    | Mul -> "*"
    | Minus -> "-"
    | Mod -> "mod"
    | ITE -> "ite"
    | BvAnd -> "bvand"
    | BvXor -> "bvxor"
    | BvOr -> "bvor"
    | BvAdd -> "bvadd"
    | BvSub -> "bvsub"
    | BvShl -> "bvshl"
    | BvShr -> "bvlshr"
    | BvUdiv -> "bvudiv"
    | BvMod -> "bvurem"
    | BvMul -> "bvmul"
    | BvUlt -> "bvult"
    | BvToNat -> "bv2int"
    | BvUext n1 ->
        let uu____2984 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2984
    | NatToBv n1 ->
        let uu____2989 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(_ int2bv %s)" uu____2989
    | Var s -> s
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_3003 ->
    match uu___5_3003 with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____3013 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____3013
let rec (hash_of_term' : term' -> Prims.string) =
  fun t ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____3035 = FStar_Util.string_of_int i in
        Prims.op_Hat "@" uu____3035
    | FreeV x ->
        let uu____3047 = fv_name x in
        let uu____3049 =
          let uu____3051 = let uu____3053 = fv_sort x in strSort uu____3053 in
          Prims.op_Hat ":" uu____3051 in
        Prims.op_Hat uu____3047 uu____3049
    | App (op, tms) ->
        let uu____3061 =
          let uu____3063 = op_to_string op in
          let uu____3065 =
            let uu____3067 =
              let uu____3069 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____3069 (FStar_String.concat " ") in
            Prims.op_Hat uu____3067 ")" in
          Prims.op_Hat uu____3063 uu____3065 in
        Prims.op_Hat "(" uu____3061
    | Labeled (t1, r1, r2) ->
        let uu____3086 = hash_of_term t1 in
        let uu____3088 =
          let uu____3090 = FStar_Range.string_of_range r2 in
          Prims.op_Hat r1 uu____3090 in
        Prims.op_Hat uu____3086 uu____3088
    | LblPos (t1, r) ->
        let uu____3096 =
          let uu____3098 = hash_of_term t1 in
          Prims.op_Hat uu____3098
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")")) in
        Prims.op_Hat "(! " uu____3096
    | Quant (qop, pats, wopt, sorts, body, uu____3108) ->
        let uu____3133 =
          let uu____3135 =
            let uu____3137 =
              let uu____3139 =
                let uu____3141 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____3141 (FStar_String.concat " ") in
              let uu____3151 =
                let uu____3153 =
                  let uu____3155 = hash_of_term body in
                  let uu____3157 =
                    let uu____3159 =
                      let uu____3161 = weightToSmt wopt in
                      let uu____3163 =
                        let uu____3165 =
                          let uu____3167 =
                            let uu____3169 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1 ->
                                      let uu____3188 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____3188
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____3169
                              (FStar_String.concat "; ") in
                          Prims.op_Hat uu____3167 "))" in
                        Prims.op_Hat " " uu____3165 in
                      Prims.op_Hat uu____3161 uu____3163 in
                    Prims.op_Hat " " uu____3159 in
                  Prims.op_Hat uu____3155 uu____3157 in
                Prims.op_Hat ")(! " uu____3153 in
              Prims.op_Hat uu____3139 uu____3151 in
            Prims.op_Hat " (" uu____3137 in
          Prims.op_Hat (qop_to_string qop) uu____3135 in
        Prims.op_Hat "(" uu____3133
    | Let (es, body) ->
        let uu____3215 =
          let uu____3217 =
            let uu____3219 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____3219 (FStar_String.concat " ") in
          let uu____3229 =
            let uu____3231 =
              let uu____3233 = hash_of_term body in
              Prims.op_Hat uu____3233 ")" in
            Prims.op_Hat ") " uu____3231 in
          Prims.op_Hat uu____3217 uu____3229 in
        Prims.op_Hat "(let (" uu____3215
and (hash_of_term : term -> Prims.string) = fun tm -> hash_of_term' tm.tm
let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s -> (s, (Prims.op_Hat s "_proj_0"))
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt"
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool"
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString"
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz ->
    let uu____3294 =
      let uu____3296 = FStar_Util.string_of_int sz in
      Prims.op_Hat "BoxBitVec" uu____3296 in
    mkBoxFunctions uu____3294
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal"
let (isInjective : Prims.string -> Prims.bool) =
  fun s ->
    if (FStar_String.length s) >= (Prims.of_int (3))
    then
      (let uu____3321 =
         FStar_String.substring s Prims.int_zero (Prims.of_int (3)) in
       uu____3321 = "Box") &&
        (let uu____3328 =
           let uu____3330 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c -> c = 46) uu____3330 in
         Prims.op_Negation uu____3328)
    else false
let (mk : term' -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      let uu____3354 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____3354; rng = r }
let (mkTrue : FStar_Range.range -> term) = fun r -> mk (App (TrueOp, [])) r
let (mkFalse : FStar_Range.range -> term) = fun r -> mk (App (FalseOp, [])) r
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____3418 =
        let uu____3419 = FStar_Util.ensure_decimal i in Integer uu____3419 in
      mk uu____3418 r
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____3434 = FStar_Util.string_of_int i in mkInteger uu____3434 r
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i -> fun r -> mk (Real i) r
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i -> fun r -> mk (BoundV i) r
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x -> fun r -> mk (FreeV x) r
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f -> fun r -> mk (App f) r
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____3512 ->
    fun r -> match uu____3512 with | (s, args) -> mk (App ((Var s), args)) r
let (mkNot : term -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      match t.tm with
      | App (TrueOp, uu____3542) -> mkFalse r
      | App (FalseOp, uu____3547) -> mkTrue r
      | uu____3552 -> mkApp' (Not, [t]) r
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____3568 ->
    fun r ->
      match uu____3568 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu____3576), uu____3577) -> t2
           | (uu____3582, App (TrueOp, uu____3583)) -> t1
           | (App (FalseOp, uu____3588), uu____3589) -> mkFalse r
           | (uu____3594, App (FalseOp, uu____3595)) -> mkFalse r
           | (App (And, ts1), App (And, ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____3612, App (And, ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And, ts1), uu____3621) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____3628 -> mkApp' (And, [t1; t2]) r)
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____3648 ->
    fun r ->
      match uu____3648 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu____3656), uu____3657) -> mkTrue r
           | (uu____3662, App (TrueOp, uu____3663)) -> mkTrue r
           | (App (FalseOp, uu____3668), uu____3669) -> t2
           | (uu____3674, App (FalseOp, uu____3675)) -> t1
           | (App (Or, ts1), App (Or, ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____3692, App (Or, ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or, ts1), uu____3701) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____3708 -> mkApp' (Or, [t1; t2]) r)
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____3728 ->
    fun r ->
      match uu____3728 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____3736, App (TrueOp, uu____3737)) -> mkTrue r
           | (App (FalseOp, uu____3742), uu____3743) -> mkTrue r
           | (App (TrueOp, uu____3748), uu____3749) -> t2
           | (uu____3754, App (Imp, t1'::t2'::[])) ->
               let uu____3759 =
                 let uu____3766 =
                   let uu____3769 = mkAnd (t1, t1') r in [uu____3769; t2'] in
                 (Imp, uu____3766) in
               mkApp' uu____3759 r
           | uu____3772 -> mkApp' (Imp, [t1; t2]) r)
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op ->
    fun uu____3797 ->
      fun r -> match uu____3797 with | (t1, t2) -> mkApp' (op, [t1; t2]) r
let (mkMinus : term -> FStar_Range.range -> term) =
  fun t -> fun r -> mkApp' (Minus, [t]) r
let (mkNatToBv : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz -> fun t -> fun r -> mkApp' ((NatToBv sz), [t]) r
let (mkBvUext : Prims.int -> term -> FStar_Range.range -> term) =
  fun sz -> fun t -> fun r -> mkApp' ((BvUext sz), [t]) r
let (mkBvToNat : term -> FStar_Range.range -> term) =
  fun t -> fun r -> mkApp' (BvToNat, [t]) r
let (mkBvAnd : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvAnd
let (mkBvXor : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvXor
let (mkBvOr : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvOr
let (mkBvAdd : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvAdd
let (mkBvSub : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvSub
let (mkBvShl : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____3957 ->
      fun r ->
        match uu____3957 with
        | (t1, t2) ->
            let uu____3966 =
              let uu____3973 =
                let uu____3976 =
                  let uu____3979 = mkNatToBv sz t2 r in [uu____3979] in
                t1 :: uu____3976 in
              (BvShl, uu____3973) in
            mkApp' uu____3966 r
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____4001 ->
      fun r ->
        match uu____4001 with
        | (t1, t2) ->
            let uu____4010 =
              let uu____4017 =
                let uu____4020 =
                  let uu____4023 = mkNatToBv sz t2 r in [uu____4023] in
                t1 :: uu____4020 in
              (BvShr, uu____4017) in
            mkApp' uu____4010 r
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____4045 ->
      fun r ->
        match uu____4045 with
        | (t1, t2) ->
            let uu____4054 =
              let uu____4061 =
                let uu____4064 =
                  let uu____4067 = mkNatToBv sz t2 r in [uu____4067] in
                t1 :: uu____4064 in
              (BvUdiv, uu____4061) in
            mkApp' uu____4054 r
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____4089 ->
      fun r ->
        match uu____4089 with
        | (t1, t2) ->
            let uu____4098 =
              let uu____4105 =
                let uu____4108 =
                  let uu____4111 = mkNatToBv sz t2 r in [uu____4111] in
                t1 :: uu____4108 in
              (BvMod, uu____4105) in
            mkApp' uu____4098 r
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____4133 ->
      fun r ->
        match uu____4133 with
        | (t1, t2) ->
            let uu____4142 =
              let uu____4149 =
                let uu____4152 =
                  let uu____4155 = mkNatToBv sz t2 r in [uu____4155] in
                t1 :: uu____4152 in
              (BvMul, uu____4149) in
            mkApp' uu____4142 r
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____4197 ->
    fun r ->
      match uu____4197 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1, s1::[]), App (Var f2, s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____4216 -> mk_bin_op Eq (t1, t2) r)
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
  fun t -> fun r -> mkApp ("to_real", [t]) r
let (mkITE : (term * term * term) -> FStar_Range.range -> term) =
  fun uu____4381 ->
    fun r ->
      match uu____4381 with
      | (t1, t2, t3) ->
          (match t1.tm with
           | App (TrueOp, uu____4392) -> t2
           | App (FalseOp, uu____4397) -> t3
           | uu____4402 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp, uu____4403), App (TrueOp, uu____4404)) ->
                    mkTrue r
                | (App (TrueOp, uu____4413), uu____4414) ->
                    let uu____4419 =
                      let uu____4424 = mkNot t1 t1.rng in (uu____4424, t3) in
                    mkImp uu____4419 r
                | (uu____4425, App (TrueOp, uu____4426)) -> mkImp (t1, t2) r
                | (uu____4431, uu____4432) -> mkApp' (ITE, [t1; t2; t3]) r))
let (mkCases : term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out -> fun t1 -> mkAnd (out, t1) r) hd1
            tl1
let (check_pattern_ok : term -> term FStar_Pervasives_Native.option) =
  fun t ->
    let rec aux t1 =
      match t1.tm with
      | Integer uu____4488 -> FStar_Pervasives_Native.None
      | Real uu____4490 -> FStar_Pervasives_Native.None
      | BoundV uu____4492 -> FStar_Pervasives_Native.None
      | FreeV uu____4494 -> FStar_Pervasives_Native.None
      | Let (tms, tm) -> aux_l (tm :: tms)
      | App (head1, terms) ->
          let head_ok =
            match head1 with
            | Var uu____4518 -> true
            | TrueOp -> true
            | FalseOp -> true
            | Not -> false
            | And -> false
            | Or -> false
            | Imp -> false
            | Iff -> false
            | Eq -> false
            | LT -> true
            | LTE -> true
            | GT -> true
            | GTE -> true
            | Add -> true
            | Sub -> true
            | Div -> true
            | RealDiv -> true
            | Mul -> true
            | Minus -> true
            | Mod -> true
            | BvAnd -> false
            | BvXor -> false
            | BvOr -> false
            | BvAdd -> false
            | BvSub -> false
            | BvShl -> false
            | BvShr -> false
            | BvUdiv -> false
            | BvMod -> false
            | BvMul -> false
            | BvUlt -> false
            | BvUext uu____4551 -> false
            | NatToBv uu____4554 -> false
            | BvToNat -> false
            | ITE -> false in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2, uu____4565, uu____4566) -> aux t2
      | Quant uu____4569 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____4594 -> FStar_Pervasives_Native.Some t1
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____4609 = aux t1 in
          (match uu____4609 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None -> aux_l ts1) in
    aux t
let rec (print_smt_term : term -> Prims.string) =
  fun t ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | Real r -> FStar_Util.format1 "(Real %s)" r
    | BoundV n1 ->
        let uu____4647 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____4647
    | FreeV fv ->
        let uu____4659 = fv_name fv in
        FStar_Util.format1 "(FreeV %s)" uu____4659
    | App (op, l) ->
        let uu____4668 = op_to_string op in
        let uu____4670 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____4668 uu____4670
    | Labeled (t1, r1, r2) ->
        let uu____4678 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4678
    | LblPos (t1, s) ->
        let uu____4685 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4685
    | Quant (qop, l, uu____4690, uu____4691, t1, uu____4693) ->
        let uu____4718 = print_smt_term_list_list l in
        let uu____4720 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4718
          uu____4720
    | Let (es, body) ->
        let uu____4729 = print_smt_term_list es in
        let uu____4731 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____4729 uu____4731
and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l ->
    let uu____4738 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____4738 (FStar_String.concat " ")
and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l ->
    FStar_List.fold_left
      (fun s ->
         fun l1 ->
           let uu____4765 =
             let uu____4767 =
               let uu____4769 = print_smt_term_list l1 in
               Prims.op_Hat uu____4769 " ] " in
             Prims.op_Hat "; [ " uu____4767 in
           Prims.op_Hat s uu____4765) "" l
let (mkQuantQid :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term *
        Prims.string FStar_Syntax_Syntax.memo) -> term)
  =
  fun r ->
    fun check_pats ->
      fun uu____4814 ->
        match uu____4814 with
        | (qop, pats, wopt, vars, body, qid) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____4895 =
                   FStar_Util.find_map pats1
                     (fun x -> FStar_Util.find_map x check_pattern_ok) in
                 match uu____4895 with
                 | FStar_Pervasives_Native.None -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____4910 =
                         let uu____4916 =
                           let uu____4918 = print_smt_term p in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____4918 in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____4916) in
                       FStar_Errors.log_issue r uu____4910);
                      [])) in
            if (FStar_List.length vars) = Prims.int_zero
            then body
            else
              (match body.tm with
               | App (TrueOp, uu____4929) -> body
               | uu____4934 ->
                   let uu____4935 =
                     let uu____4936 =
                       let uu____4961 = all_pats_ok pats in
                       (qop, uu____4961, wopt, vars, body, qid) in
                     Quant uu____4936 in
                   mk uu____4935 r)
let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r ->
    fun check_pats ->
      fun uu____5013 ->
        match uu____5013 with
        | (qop, pats, wopt, vars, body) ->
            let uu____5057 =
              let uu____5082 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (qop, pats, wopt, vars, body, uu____5082) in
            mkQuantQid r check_pats uu____5057
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____5117 ->
    fun r ->
      match uu____5117 with
      | (es, body) ->
          if (FStar_List.length es) = Prims.int_zero
          then body
          else mk (Let (es, body)) r
let (abstr : fv Prims.list -> term -> term) =
  fun fvs ->
    fun t ->
      let nvars = FStar_List.length fvs in
      let index_of1 fv =
        let uu____5163 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____5163 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some (nvars - (i + Prims.int_one)) in
      let rec aux ix t1 =
        let uu____5190 = FStar_ST.op_Bang t1.freevars in
        match uu____5190 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____5264 ->
            (match t1.tm with
             | Integer uu____5277 -> t1
             | Real uu____5279 -> t1
             | BoundV uu____5281 -> t1
             | FreeV x ->
                 let uu____5292 = index_of1 x in
                 (match uu____5292 with
                  | FStar_Pervasives_Native.None -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op, tms) ->
                 let uu____5306 =
                   let uu____5313 = FStar_List.map (aux ix) tms in
                   (op, uu____5313) in
                 mkApp' uu____5306 t1.rng
             | Labeled (t2, r1, r2) ->
                 let uu____5323 =
                   let uu____5324 =
                     let uu____5332 = aux ix t2 in (uu____5332, r1, r2) in
                   Labeled uu____5324 in
                 mk uu____5323 t2.rng
             | LblPos (t2, r) ->
                 let uu____5338 =
                   let uu____5339 =
                     let uu____5345 = aux ix t2 in (uu____5345, r) in
                   LblPos uu____5339 in
                 mk uu____5338 t2.rng
             | Quant (qop, pats, wopt, vars, body, uu____5352) ->
                 let n1 = FStar_List.length vars in
                 let uu____5378 =
                   let uu____5398 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____5415 = aux (ix + n1) body in
                   (qop, uu____5398, wopt, vars, uu____5415) in
                 mkQuant t1.rng false uu____5378
             | Let (es, body) ->
                 let uu____5432 =
                   FStar_List.fold_left
                     (fun uu____5452 ->
                        fun e ->
                          match uu____5452 with
                          | (ix1, l) ->
                              let uu____5476 =
                                let uu____5479 = aux ix1 e in uu____5479 :: l in
                              ((ix1 + Prims.int_one), uu____5476)) (ix, [])
                     es in
                 (match uu____5432 with
                  | (ix1, es_rev) ->
                      let uu____5495 =
                        let uu____5502 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____5502) in
                      mkLet uu____5495 t1.rng)) in
      aux Prims.int_zero t
let (instQid : Prims.bool -> term Prims.list -> term -> term) =
  fun b ->
    fun tms ->
      fun t ->
        let tms1 = FStar_List.rev tms in
        let n1 = FStar_List.length tms1 in
        let rec aux shift t1 =
          match t1.tm with
          | Integer uu____5545 -> t1
          | Real uu____5547 -> t1
          | FreeV uu____5549 -> t1
          | BoundV i ->
              if (Prims.int_zero <= (i - shift)) && ((i - shift) < n1)
              then FStar_List.nth tms1 (i - shift)
              else t1
          | App (op, tms2) ->
              let uu____5570 =
                let uu____5577 = FStar_List.map (aux shift) tms2 in
                (op, uu____5577) in
              mkApp' uu____5570 t1.rng
          | Labeled (t2, r1, r2) ->
              let uu____5587 =
                let uu____5588 =
                  let uu____5596 = aux shift t2 in (uu____5596, r1, r2) in
                Labeled uu____5588 in
              mk uu____5587 t2.rng
          | LblPos (t2, r) ->
              let uu____5602 =
                let uu____5603 =
                  let uu____5609 = aux shift t2 in (uu____5609, r) in
                LblPos uu____5603 in
              mk uu____5602 t2.rng
          | Quant (qop, pats, wopt, vars, body, qid) ->
              let m = FStar_List.length vars in
              let shift1 = shift + m in
              let qid' =
                if b
                then qid
                else FStar_Util.mk_ref FStar_Pervasives_Native.None in
              let uu____5658 =
                let uu____5683 =
                  FStar_All.pipe_right pats
                    (FStar_List.map (FStar_List.map (aux shift1))) in
                let uu____5700 = aux shift1 body in
                (qop, uu____5683, wopt, vars, uu____5700, qid') in
              mkQuantQid t1.rng false uu____5658
          | Let (es, body) ->
              let uu____5720 =
                FStar_List.fold_left
                  (fun uu____5740 ->
                     fun e ->
                       match uu____5740 with
                       | (ix, es1) ->
                           let uu____5764 =
                             let uu____5767 = aux shift e in uu____5767 ::
                               es1 in
                           ((shift + Prims.int_one), uu____5764)) (shift, [])
                  es in
              (match uu____5720 with
               | (shift1, es_rev) ->
                   let uu____5783 =
                     let uu____5790 = aux shift1 body in
                     ((FStar_List.rev es_rev), uu____5790) in
                   mkLet uu____5783 t1.rng) in
        aux Prims.int_zero t
let (inst : term Prims.list -> term -> term) =
  fun tms -> fun t -> instQid false tms t
let (subst : term -> fv -> term -> term) =
  fun t ->
    fun fv -> fun s -> let uu____5826 = abstr [fv] t in inst [s] uu____5826
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r ->
    fun uu____5856 ->
      match uu____5856 with
      | (qop, pats, wopt, vars, body) ->
          let uu____5899 =
            let uu____5919 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars))) in
            let uu____5936 = FStar_List.map fv_sort vars in
            let uu____5939 = abstr vars body in
            (qop, uu____5919, wopt, uu____5936, uu____5939) in
          mkQuant r true uu____5899
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r ->
    fun uu____5970 ->
      match uu____5970 with
      | (pats, vars, body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r ->
    fun uu____6029 ->
      match uu____6029 with
      | (pats, wopt, sorts, body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r ->
    fun uu____6104 ->
      match uu____6104 with
      | (pats, wopt, vars, body) ->
          mkQuant' r (Forall, pats, wopt, vars, body)
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r ->
    fun uu____6167 ->
      match uu____6167 with
      | (pats, vars, body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____6218 ->
    fun r ->
      match uu____6218 with
      | (bindings, body) ->
          let uu____6244 = FStar_List.split bindings in
          (match uu____6244 with
           | (vars, es) ->
               let uu____6263 =
                 let uu____6270 = abstr vars body in (es, uu____6270) in
               mkLet uu____6263 r)
let (norng : FStar_Range.range) = FStar_Range.dummyRange
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____6292 ->
    match uu____6292 with
    | (nm, vars, s, tm, c) ->
        let uu____6317 =
          let uu____6331 = FStar_List.map fv_sort vars in
          let uu____6334 = abstr vars tm in
          (nm, uu____6331, s, uu____6334, c) in
        DefineFun uu____6317
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort ->
    let uu____6345 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____6345
let (fresh_token :
  FStar_Range.range -> (Prims.string * sort) -> Prims.int -> decl) =
  fun rng ->
    fun uu____6368 ->
      fun id1 ->
        match uu____6368 with
        | (tok_name, sort) ->
            let a_name = Prims.op_Hat "fresh_token_" tok_name in
            let a =
              let uu____6384 =
                let uu____6385 =
                  let uu____6390 = mkInteger' id1 rng in
                  let uu____6391 =
                    let uu____6392 =
                      let uu____6400 = constr_id_of_sort sort in
                      let uu____6402 =
                        let uu____6405 = mkApp (tok_name, []) rng in
                        [uu____6405] in
                      (uu____6400, uu____6402) in
                    mkApp uu____6392 rng in
                  (uu____6390, uu____6391) in
                mkEq uu____6385 rng in
              let uu____6412 = escape a_name in
              {
                assumption_term = uu____6384;
                assumption_caption =
                  (FStar_Pervasives_Native.Some "fresh token");
                assumption_name = uu____6412;
                assumption_fact_ids = []
              } in
            Assume a
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng ->
    fun uu____6438 ->
      match uu____6438 with
      | (name, arg_sorts, sort, id1) ->
          let id2 = FStar_Util.string_of_int id1 in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i ->
                    fun s ->
                      let uu____6478 =
                        let uu____6479 =
                          let uu____6485 =
                            let uu____6487 = FStar_Util.string_of_int i in
                            Prims.op_Hat "x_" uu____6487 in
                          (uu____6485, s) in
                        mk_fv uu____6479 in
                      mkFreeV uu____6478 norng)) in
          let bvar_names = FStar_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let cid_app =
            let uu____6515 =
              let uu____6523 = constr_id_of_sort sort in (uu____6523, [capp]) in
            mkApp uu____6515 norng in
          let a_name = Prims.op_Hat "constructor_distinct_" name in
          let a =
            let uu____6532 =
              let uu____6533 =
                let uu____6544 =
                  let uu____6545 =
                    let uu____6550 = mkInteger id2 norng in
                    (uu____6550, cid_app) in
                  mkEq uu____6545 norng in
                ([[capp]], bvar_names, uu____6544) in
              mkForall rng uu____6533 in
            let uu____6559 = escape a_name in
            {
              assumption_term = uu____6532;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____6559;
              assumption_fact_ids = []
            } in
          Assume a
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng ->
    fun uu____6584 ->
      match uu____6584 with
      | (name, fields, sort) ->
          let n_bvars = FStar_List.length fields in
          let bvar_name i =
            let uu____6617 = FStar_Util.string_of_int i in
            Prims.op_Hat "x_" uu____6617 in
          let bvar_index i = n_bvars - (i + Prims.int_one) in
          let bvar i s =
            let uu____6646 =
              let uu____6647 =
                let uu____6653 = bvar_name i in (uu____6653, s) in
              mk_fv uu____6647 in
            FStar_All.pipe_left mkFreeV uu____6646 in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i ->
                    fun uu____6689 ->
                      match uu____6689 with
                      | (uu____6699, s, uu____6701) ->
                          let uu____6706 = bvar i s in uu____6706 norng)) in
          let bvar_names = FStar_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let uu____6734 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i ->
                    fun uu____6772 ->
                      match uu____6772 with
                      | (name1, s, projectible) ->
                          let cproj_app = mkApp (name1, [capp]) norng in
                          let proj_name =
                            DeclFun
                              (name1, [sort], s,
                                (FStar_Pervasives_Native.Some "Projector")) in
                          if projectible
                          then
                            let a =
                              let uu____6805 =
                                let uu____6806 =
                                  let uu____6817 =
                                    let uu____6818 =
                                      let uu____6823 =
                                        let uu____6824 = bvar i s in
                                        uu____6824 norng in
                                      (cproj_app, uu____6823) in
                                    mkEq uu____6818 norng in
                                  ([[capp]], bvar_names, uu____6817) in
                                mkForall rng uu____6806 in
                              let uu____6837 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1) in
                              {
                                assumption_term = uu____6805;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____6837;
                                assumption_fact_ids = []
                              } in
                            [proj_name; Assume a]
                          else [proj_name])) in
          FStar_All.pipe_right uu____6734 FStar_List.flatten
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng ->
    fun uu____6862 ->
      match uu____6862 with
      | (name, fields, sort, id1, injective) ->
          let injective1 = injective || true in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____6910 ->
                    match uu____6910 with
                    | (uu____6919, sort1, uu____6921) -> sort1)) in
          let cdecl =
            DeclFun
              (name, field_sorts, sort,
                (FStar_Pervasives_Native.Some "Constructor")) in
          let cid = fresh_constructor rng (name, field_sorts, sort, id1) in
          let disc =
            let disc_name = Prims.op_Hat "is-" name in
            let xfv = mk_fv ("x", sort) in
            let xx = mkFreeV xfv norng in
            let disc_eq =
              let uu____6946 =
                let uu____6951 =
                  let uu____6952 =
                    let uu____6960 = constr_id_of_sort sort in
                    (uu____6960, [xx]) in
                  mkApp uu____6952 norng in
                let uu____6965 =
                  let uu____6966 = FStar_Util.string_of_int id1 in
                  mkInteger uu____6966 norng in
                (uu____6951, uu____6965) in
              mkEq uu____6946 norng in
            let uu____6968 =
              let uu____6987 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i ->
                        fun uu____7051 ->
                          match uu____7051 with
                          | (proj, s, projectible) ->
                              if projectible
                              then
                                let uu____7081 = mkApp (proj, [xx]) norng in
                                (uu____7081, [])
                              else
                                (let fi =
                                   let uu____7090 =
                                     let uu____7096 =
                                       let uu____7098 =
                                         FStar_Util.string_of_int i in
                                       Prims.op_Hat "f_" uu____7098 in
                                     (uu____7096, s) in
                                   mk_fv uu____7090 in
                                 let uu____7102 = mkFreeV fi norng in
                                 (uu____7102, [fi])))) in
              FStar_All.pipe_right uu____6987 FStar_List.split in
            match uu____6968 with
            | (proj_terms, ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars in
                let disc_inv_body =
                  let uu____7199 =
                    let uu____7204 = mkApp (name, proj_terms) norng in
                    (xx, uu____7204) in
                  mkEq uu____7199 norng in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____7217 ->
                      mkExists norng ([], ex_vars1, disc_inv_body) in
                let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
                let def =
                  mkDefineFun
                    (disc_name, [xfv], Bool_sort, disc_ax,
                      (FStar_Pervasives_Native.Some
                         "Discriminator definition")) in
                def in
          let projs =
            if injective1
            then injective_constructor rng (name, fields, sort)
            else [] in
          let uu____7252 =
            let uu____7255 =
              let uu____7256 =
                FStar_Util.format1 "<start constructor %s>" name in
              Caption uu____7256 in
            uu____7255 :: cdecl :: cid :: projs in
          let uu____7259 =
            let uu____7262 =
              let uu____7265 =
                let uu____7266 =
                  FStar_Util.format1 "</end constructor %s>" name in
                Caption uu____7266 in
              [uu____7265] in
            FStar_List.append [disc] uu____7262 in
          FStar_List.append uu____7252 uu____7259
let (name_binders_inner :
  Prims.string FStar_Pervasives_Native.option ->
    fv Prims.list ->
      Prims.int ->
        sort Prims.list ->
          (fv Prims.list * Prims.string Prims.list * Prims.int))
  =
  fun prefix_opt ->
    fun outer_names ->
      fun start ->
        fun sorts ->
          let uu____7318 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____7367 ->
                    fun s ->
                      match uu____7367 with
                      | (names1, binders, n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort -> "@x"
                            | uu____7412 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1 in
                          let nm =
                            let uu____7423 = FStar_Util.string_of_int n1 in
                            Prims.op_Hat prefix2 uu____7423 in
                          let names2 =
                            let uu____7428 = mk_fv (nm, s) in uu____7428 ::
                              names1 in
                          let b =
                            let uu____7432 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____7432 in
                          (names2, (b :: binders), (n1 + Prims.int_one)))
                 (outer_names, [], start)) in
          match uu____7318 with
          | (names1, binders, n1) -> (names1, (FStar_List.rev binders), n1)
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts ->
    let uu____7503 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        Prims.int_zero sorts in
    match uu____7503 with
    | (names1, binders, n1) -> ((FStar_List.rev names1), binders)
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  fun print_ranges ->
    fun enclosing_name ->
      fun t ->
        let next_qid =
          let ctr = FStar_Util.mk_ref Prims.int_zero in
          fun depth ->
            let n1 = FStar_ST.op_Bang ctr in
            FStar_Util.incr ctr;
            if n1 = Prims.int_zero
            then enclosing_name
            else
              (let uu____7612 = FStar_Util.string_of_int n1 in
               FStar_Util.format2 "%s.%s" enclosing_name uu____7612) in
        let remove_guard_free pats =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun ps ->
                  FStar_All.pipe_right ps
                    (FStar_List.map
                       (fun tm ->
                          match tm.tm with
                          | App
                              (Var "Prims.guard_free",
                               { tm = BoundV uu____7658;
                                 freevars = uu____7659; rng = uu____7660;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free", p::[]) -> p
                          | uu____7681 -> tm)))) in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + Prims.int_one) in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____7759 = FStar_List.nth names1 i in
              FStar_All.pipe_right uu____7759 fv_name
          | FreeV x when fv_force x ->
              let uu____7770 =
                let uu____7772 = fv_name x in
                Prims.op_Hat uu____7772 " Dummy_value)" in
              Prims.op_Hat "(" uu____7770
          | FreeV x -> fv_name x
          | App (op, []) -> op_to_string op
          | App (op, tms) ->
              let uu____7794 = op_to_string op in
              let uu____7796 =
                let uu____7798 = FStar_List.map (aux1 n1 names1) tms in
                FStar_All.pipe_right uu____7798 (FStar_String.concat "\n") in
              FStar_Util.format2 "(%s %s)" uu____7794 uu____7796
          | Labeled (t2, uu____7810, uu____7811) -> aux1 n1 names1 t2
          | LblPos (t2, s) ->
              let uu____7818 = aux1 n1 names1 t2 in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____7818 s
          | Quant (qop, pats, wopt, sorts, body, qid) ->
              let qidstr =
                let uu____7853 = FStar_ST.op_Bang qid in
                match uu____7853 with
                | FStar_Pervasives_Native.None ->
                    let qid' = next_qid () in
                    (FStar_ST.op_Colon_Equals qid
                       (FStar_Pervasives_Native.Some qid');
                     qid')
                | FStar_Pervasives_Native.Some s -> s in
              let uu____7916 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts in
              (match uu____7916 with
               | (names2, binders, n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ") in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____7969 ->
                         let uu____7974 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2 ->
                                   let uu____7993 =
                                     let uu____7995 =
                                       FStar_List.map
                                         (fun p ->
                                            let uu____8003 = aux1 n2 names2 p in
                                            FStar_Util.format1 "%s"
                                              uu____8003) pats2 in
                                     FStar_String.concat " " uu____7995 in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____7993)) in
                         FStar_All.pipe_right uu____7974
                           (FStar_String.concat "\n") in
                   let uu____8013 =
                     let uu____8017 =
                       let uu____8021 =
                         let uu____8025 = aux1 n2 names2 body in
                         let uu____8027 =
                           let uu____8031 = weightToSmt wopt in
                           [uu____8031; pats_str; qidstr] in
                         uu____8025 :: uu____8027 in
                       binders1 :: uu____8021 in
                     (qop_to_string qop) :: uu____8017 in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____8013)
          | Let (es, body) ->
              let uu____8047 =
                FStar_List.fold_left
                  (fun uu____8080 ->
                     fun e ->
                       match uu____8080 with
                       | (names0, binders, n0) ->
                           let nm =
                             let uu____8123 = FStar_Util.string_of_int n0 in
                             Prims.op_Hat "@lb" uu____8123 in
                           let names01 =
                             let uu____8129 = mk_fv (nm, Term_sort) in
                             uu____8129 :: names0 in
                           let b =
                             let uu____8133 = aux1 n1 names1 e in
                             FStar_Util.format2 "(%s %s)" nm uu____8133 in
                           (names01, (b :: binders), (n0 + Prims.int_one)))
                  (names1, [], n1) es in
              (match uu____8047 with
               | (names2, binders, n2) ->
                   let uu____8167 = aux1 n2 names2 body in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____8167)
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____8183 = FStar_Range.string_of_range t1.rng in
            let uu____8185 = FStar_Range.string_of_use_range t1.rng in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____8183
              uu____8185 s
          else s in
        aux Prims.int_zero Prims.int_zero [] t
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions ->
    fun uu___6_8207 ->
      match uu___6_8207 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____8218 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string) in
            FStar_All.pipe_right uu____8218 (FStar_String.concat " ") in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____8240 -> ""
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions ->
    fun z3options ->
      fun decl ->
        match decl with
        | DefPrelude -> mkPrelude z3options
        | Module (s, decls) ->
            let res =
              let uu____8293 =
                FStar_List.map (declToSmt' print_captions z3options) decls in
              FStar_All.pipe_right uu____8293 (FStar_String.concat "\n") in
            let uu____8303 = FStar_Options.keep_query_captions () in
            if uu____8303
            then
              let uu____8307 =
                FStar_Util.string_of_int (FStar_List.length decls) in
              let uu____8309 =
                FStar_Util.string_of_int (FStar_String.length res) in
              FStar_Util.format5
                "\n;;; Start %s\n%s\n;;; End %s (%s decls; total size %s)" s
                res s uu____8307 uu____8309
            else res
        | Caption c ->
            if print_captions
            then
              let uu____8318 =
                let uu____8320 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s -> Prims.op_Hat "; " (Prims.op_Hat s "\n"))) in
                FStar_All.pipe_right uu____8320 (FStar_String.concat "") in
              Prims.op_Hat "\n" uu____8318
            else ""
        | DeclFun (f, argsorts, retsort, c) ->
            let l = FStar_List.map strSort argsorts in
            let uu____8361 = caption_to_string print_captions c in
            let uu____8363 = strSort retsort in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____8361 f
              (FStar_String.concat " " l) uu____8363
        | DefineFun (f, arg_sorts, retsort, body, c) ->
            let uu____8378 = name_macro_binders arg_sorts in
            (match uu____8378 with
             | (names1, binders) ->
                 let body1 =
                   let uu____8402 =
                     FStar_List.map (fun x -> mkFreeV x norng) names1 in
                   instQid true uu____8402 body in
                 let uu____8408 = caption_to_string print_captions c in
                 let uu____8410 = strSort retsort in
                 let uu____8412 =
                   let uu____8414 = escape f in
                   termToSmt print_captions uu____8414 body1 in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____8408 f (FStar_String.concat " " binders) uu____8410
                   uu____8412)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_8441 ->
                      match uu___7_8441 with
                      | Name n1 ->
                          let uu____8444 = FStar_Ident.text_of_lid n1 in
                          Prims.op_Hat "Name " uu____8444
                      | Namespace ns ->
                          let uu____8448 = FStar_Ident.text_of_lid ns in
                          Prims.op_Hat "Namespace " uu____8448
                      | Tag t -> Prims.op_Hat "Tag " t)) in
            let fids =
              if print_captions
              then
                let uu____8458 =
                  let uu____8460 = fact_ids_to_string a.assumption_fact_ids in
                  FStar_String.concat "; " uu____8460 in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____8458
              else "" in
            let n1 = a.assumption_name in
            let uu____8471 =
              caption_to_string print_captions a.assumption_caption in
            let uu____8473 = termToSmt print_captions n1 a.assumption_term in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____8471
              fids uu____8473 n1
        | Eval t ->
            let uu____8477 = termToSmt print_captions "eval" t in
            FStar_Util.format1 "(eval %s)" uu____8477
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____8484 -> ""
        | CheckSat ->
            "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
        | GetUnsatCore ->
            "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
        | Push -> "(push)"
        | Pop -> "(pop)"
        | SetOption (s, v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
        | GetStatistics ->
            "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
        | GetReasonUnknown ->
            "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and (declToSmt : Prims.string -> decl -> Prims.string) =
  fun z3options ->
    fun decl ->
      let uu____8505 = FStar_Options.keep_query_captions () in
      declToSmt' uu____8505 z3options decl
and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options ->
    let basic =
      Prims.op_Hat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n(declare-fun IsTotFun (Term) Bool)\n\n                ;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))" in
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
        true)] in
    let bcons =
      let uu____8632 =
        let uu____8636 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng)) in
        FStar_All.pipe_right uu____8636
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____8632 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n" in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n" in
    let uu____8663 =
      let uu____8665 =
        let uu____8667 =
          let uu____8669 =
            let uu____8671 = FStar_Options.smtencoding_valid_intro () in
            if uu____8671 then valid_intro else "" in
          let uu____8678 =
            let uu____8680 = FStar_Options.smtencoding_valid_elim () in
            if uu____8680 then valid_elim else "" in
          Prims.op_Hat uu____8669 uu____8678 in
        Prims.op_Hat lex_ordering uu____8667 in
      Prims.op_Hat bcons uu____8665 in
    Prims.op_Hat basic uu____8663
let (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options ->
    fun decls ->
      let uu____8705 = FStar_List.map (declToSmt z3options) decls in
      FStar_All.pipe_right uu____8705 (FStar_String.concat "\n")
let (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options -> fun decl -> declToSmt' false z3options decl
let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz ->
    let uu____8740 =
      let uu____8741 =
        let uu____8743 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____8743 in
      let uu____8752 =
        let uu____8755 =
          let uu____8756 =
            let uu____8758 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____8758 in
          (uu____8756, (BitVec_sort sz), true) in
        [uu____8755] in
      (uu____8741, uu____8752, Term_sort, ((Prims.of_int (12)) + sz), true) in
    FStar_All.pipe_right uu____8740 (constructor_to_decl norng)
let (__range_c : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (mk_Range_const : unit -> term) =
  fun uu____8790 ->
    let i = FStar_ST.op_Bang __range_c in
    (let uu____8815 =
       let uu____8817 = FStar_ST.op_Bang __range_c in
       uu____8817 + Prims.int_one in
     FStar_ST.op_Colon_Equals __range_c uu____8815);
    (let uu____8862 =
       let uu____8870 = let uu____8873 = mkInteger' i norng in [uu____8873] in
       ("Range_const", uu____8870) in
     mkApp uu____8862 norng)
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1 -> fun t2 -> fun r -> mkApp ("Tm_app", [t1; t2]) r
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____8916 =
        let uu____8924 = let uu____8927 = mkInteger' i norng in [uu____8927] in
        ("Tm_uvar", uu____8924) in
      mkApp uu____8916 r
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond ->
    fun u ->
      fun v1 ->
        fun t ->
          match t.tm with
          | App (Var v', t1::[]) when (v1 = v') && cond -> t1
          | uu____8970 -> mkApp (u, [t]) t.rng
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u ->
    fun v1 ->
      fun t ->
        let uu____8994 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____8994 u v1 t
let (boxInt : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun)
      (FStar_Pervasives_Native.snd boxIntFun) t
let (unboxInt : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun)
      (FStar_Pervasives_Native.fst boxIntFun) t
let (boxBool : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun)
      (FStar_Pervasives_Native.snd boxBoolFun) t
let (unboxBool : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun)
      (FStar_Pervasives_Native.fst boxBoolFun) t
let (boxString : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun)
      (FStar_Pervasives_Native.snd boxStringFun) t
let (unboxString : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun)
      (FStar_Pervasives_Native.fst boxStringFun) t
let (boxReal : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxRealFun)
      (FStar_Pervasives_Native.snd boxRealFun) t
let (unboxReal : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxRealFun)
      (FStar_Pervasives_Native.fst boxRealFun) t
let (boxBitVec : Prims.int -> term -> term) =
  fun sz ->
    fun t ->
      let uu____9089 =
        let uu____9091 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____9091 in
      let uu____9100 =
        let uu____9102 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____9102 in
      elim_box true uu____9089 uu____9100 t
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz ->
    fun t ->
      let uu____9125 =
        let uu____9127 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____9127 in
      let uu____9136 =
        let uu____9138 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____9138 in
      elim_box true uu____9125 uu____9136 t
let (boxTerm : sort -> term -> term) =
  fun sort ->
    fun t ->
      match sort with
      | Int_sort -> boxInt t
      | Bool_sort -> boxBool t
      | String_sort -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____9162 -> FStar_Exn.raise FStar_Util.Impos
let (unboxTerm : sort -> term -> term) =
  fun sort ->
    fun t ->
      match sort with
      | Int_sort -> unboxInt t
      | Bool_sort -> unboxBool t
      | String_sort -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____9177 -> FStar_Exn.raise FStar_Util.Impos
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t ->
    match t.tm with
    | App (Var s, t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____9203 = FStar_Util.int_of_string n1 in
             FStar_Pervasives_Native.Some uu____9203
         | uu____9206 -> FStar_Pervasives_Native.None)
    | uu____9208 -> FStar_Pervasives_Native.None
let (mk_PreType : term -> term) = fun t -> mkApp ("PreType", [t]) t.rng
let (mk_Valid : term -> term) =
  fun t ->
    match t.tm with
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Equality", uu____9226::t1::t2::[]);
           freevars = uu____9229; rng = uu____9230;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_disEquality", uu____9249::t1::t2::[]);
           freevars = uu____9252; rng = uu____9253;_}::[])
        -> let uu____9272 = mkEq (t1, t2) norng in mkNot uu____9272 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThanOrEqual", t1::t2::[]);
           freevars = uu____9275; rng = uu____9276;_}::[])
        ->
        let uu____9295 =
          let uu____9300 = unboxInt t1 in
          let uu____9301 = unboxInt t2 in (uu____9300, uu____9301) in
        mkLTE uu____9295 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThan", t1::t2::[]);
           freevars = uu____9304; rng = uu____9305;_}::[])
        ->
        let uu____9324 =
          let uu____9329 = unboxInt t1 in
          let uu____9330 = unboxInt t2 in (uu____9329, uu____9330) in
        mkLT uu____9324 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThanOrEqual", t1::t2::[]);
           freevars = uu____9333; rng = uu____9334;_}::[])
        ->
        let uu____9353 =
          let uu____9358 = unboxInt t1 in
          let uu____9359 = unboxInt t2 in (uu____9358, uu____9359) in
        mkGTE uu____9353 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThan", t1::t2::[]);
           freevars = uu____9362; rng = uu____9363;_}::[])
        ->
        let uu____9382 =
          let uu____9387 = unboxInt t1 in
          let uu____9388 = unboxInt t2 in (uu____9387, uu____9388) in
        mkGT uu____9382 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_AmpAmp", t1::t2::[]);
           freevars = uu____9391; rng = uu____9392;_}::[])
        ->
        let uu____9411 =
          let uu____9416 = unboxBool t1 in
          let uu____9417 = unboxBool t2 in (uu____9416, uu____9417) in
        mkAnd uu____9411 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_BarBar", t1::t2::[]);
           freevars = uu____9420; rng = uu____9421;_}::[])
        ->
        let uu____9440 =
          let uu____9445 = unboxBool t1 in
          let uu____9446 = unboxBool t2 in (uu____9445, uu____9446) in
        mkOr uu____9440 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Negation", t1::[]); freevars = uu____9448;
           rng = uu____9449;_}::[])
        -> let uu____9468 = unboxBool t1 in mkNot uu____9468 t1.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]);
           freevars = uu____9472; rng = uu____9473;_}::[])
        when
        let uu____9492 = getBoxedInteger t0 in FStar_Util.is_some uu____9492
        ->
        let sz =
          let uu____9499 = getBoxedInteger t0 in
          match uu____9499 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9507 -> failwith "impossible" in
        let uu____9513 =
          let uu____9518 = unboxBitVec sz t1 in
          let uu____9519 = unboxBitVec sz t2 in (uu____9518, uu____9519) in
        mkBvUlt uu____9513 t.rng
    | App
        (Var "Prims.equals",
         uu____9520::{ tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]);
                       freevars = uu____9524; rng = uu____9525;_}::uu____9526::[])
        when
        let uu____9545 = getBoxedInteger t0 in FStar_Util.is_some uu____9545
        ->
        let sz =
          let uu____9552 = getBoxedInteger t0 in
          match uu____9552 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____9560 -> failwith "impossible" in
        let uu____9566 =
          let uu____9571 = unboxBitVec sz t1 in
          let uu____9572 = unboxBitVec sz t2 in (uu____9571, uu____9572) in
        mkBvUlt uu____9566 t.rng
    | App (Var "Prims.b2t", t1::[]) ->
        let uu___1424_9577 = unboxBool t1 in
        {
          tm = (uu___1424_9577.tm);
          freevars = (uu___1424_9577.freevars);
          rng = (t.rng)
        }
    | uu____9578 -> mkApp ("Valid", [t]) t.rng
let (mk_HasType : term -> term -> term) =
  fun v1 -> fun t -> mkApp ("HasType", [v1; t]) t.rng
let (mk_HasTypeZ : term -> term -> term) =
  fun v1 -> fun t -> mkApp ("HasTypeZ", [v1; t]) t.rng
let (mk_IsTotFun : term -> term) = fun t -> mkApp ("IsTotFun", [t]) t.rng
let (mk_IsTyped : term -> term) = fun v1 -> mkApp ("IsTyped", [v1]) norng
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f ->
    fun v1 ->
      fun t ->
        let uu____9649 = FStar_Options.unthrottle_inductives () in
        if uu____9649
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let (mk_HasTypeWithFuel :
  term FStar_Pervasives_Native.option -> term -> term -> term) =
  fun f ->
    fun v1 ->
      fun t ->
        match f with
        | FStar_Pervasives_Native.None -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
let (mk_NoHoist : term -> term -> term) =
  fun dummy -> fun b -> mkApp ("NoHoist", [dummy; b]) b.rng
let (mk_Destruct : term -> FStar_Range.range -> term) =
  fun v1 -> mkApp ("Destruct", [v1])
let (mk_Rank : term -> FStar_Range.range -> term) =
  fun x -> mkApp ("Rank", [x])
let (mk_tester : Prims.string -> term -> term) =
  fun n1 -> fun t -> mkApp ((Prims.op_Hat "is-" n1), [t]) t.rng
let (mk_ApplyTF : term -> term -> term) =
  fun t -> fun t' -> mkApp ("ApplyTF", [t; t']) t.rng
let (mk_ApplyTT : term -> term -> FStar_Range.range -> term) =
  fun t -> fun t' -> fun r -> mkApp ("ApplyTT", [t; t']) r
let (kick_partial_app : term -> term) =
  fun t ->
    let uu____9782 =
      let uu____9783 = mkApp ("__uu__PartialApp", []) t.rng in
      mk_ApplyTT uu____9783 t t.rng in
    FStar_All.pipe_right uu____9782 mk_Valid
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____9801 =
        let uu____9809 = let uu____9812 = mkInteger' i norng in [uu____9812] in
        ("FString_const", uu____9809) in
      mkApp uu____9801 r
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1 ->
    fun x2 ->
      fun x3 ->
        fun x4 ->
          fun r ->
            let uu____9843 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r in
            FStar_All.pipe_right uu____9843 mk_Valid
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1 -> fun x2 -> fun x3 -> fun r -> mkApp ("LexCons", [x1; x2; x3]) r
let rec (n_fuel : Prims.int -> term) =
  fun n1 ->
    if n1 = Prims.int_zero
    then mkApp ("ZFuel", []) norng
    else
      (let uu____9890 =
         let uu____9898 =
           let uu____9901 = n_fuel (n1 - Prims.int_one) in [uu____9901] in
         ("SFuel", uu____9898) in
       mkApp uu____9890 norng)
let (fuel_2 : term) = n_fuel (Prims.of_int (2))
let (fuel_100 : term) = n_fuel (Prims.of_int (100))
let (mk_and_opt :
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option ->
      FStar_Range.range -> term FStar_Pervasives_Native.option)
  =
  fun p1 ->
    fun p2 ->
      fun r ->
        match (p1, p2) with
        | (FStar_Pervasives_Native.Some p11, FStar_Pervasives_Native.Some
           p21) ->
            let uu____9949 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____9949
        | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.None) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            FStar_Pervasives_Native.None
let (mk_and_opt_l :
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option)
  =
  fun pl ->
    fun r ->
      FStar_List.fold_right (fun p -> fun out -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
let (mk_and_l : term Prims.list -> FStar_Range.range -> term) =
  fun l ->
    fun r ->
      let uu____10012 = mkTrue r in
      FStar_List.fold_right (fun p1 -> fun p2 -> mkAnd (p1, p2) r) l
        uu____10012
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l ->
    fun r ->
      let uu____10032 = mkFalse r in
      FStar_List.fold_right (fun p1 -> fun p2 -> mkOr (p1, p2) r) l
        uu____10032
let (mk_haseq : term -> term) =
  fun t ->
    let uu____10043 = mkApp ("Prims.hasEq", [t]) t.rng in
    mk_Valid uu____10043
let (dummy_sort : sort) = Sort "Dummy_sort"