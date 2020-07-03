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
    match projectee with | Bool_sort -> true | uu____49 -> false
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Int_sort -> true | uu____55 -> false
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | String_sort -> true | uu____61 -> false
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_sort -> true | uu____67 -> false
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Fuel_sort -> true | uu____73 -> false
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | BitVec_sort _0 -> true | uu____80 -> false
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee -> match projectee with | BitVec_sort _0 -> _0
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Array _0 -> true | uu____97 -> false
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Array _0 -> _0
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrow _0 -> true | uu____126 -> false
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | Sort _0 -> true | uu____151 -> false
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
    | BitVec_sort n ->
        let uu____164 = FStar_Util.string_of_int n in
        FStar_Util.format1 "(_ BitVec %s)" uu____164
    | Array (s1, s2) ->
        let uu____167 = strSort s1 in
        let uu____168 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____167 uu____168
    | Arrow (s1, s2) ->
        let uu____171 = strSort s1 in
        let uu____172 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____171 uu____172
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
  fun projectee -> match projectee with | TrueOp -> true | uu____194 -> false
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee ->
    match projectee with | FalseOp -> true | uu____200 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____206 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____212 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____218 -> false
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee -> match projectee with | Imp -> true | uu____224 -> false
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee -> match projectee with | Iff -> true | uu____230 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____236 -> false
let (uu___is_LT : op -> Prims.bool) =
  fun projectee -> match projectee with | LT -> true | uu____242 -> false
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee -> match projectee with | LTE -> true | uu____248 -> false
let (uu___is_GT : op -> Prims.bool) =
  fun projectee -> match projectee with | GT -> true | uu____254 -> false
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee -> match projectee with | GTE -> true | uu____260 -> false
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____266 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____272 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____278 -> false
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee ->
    match projectee with | RealDiv -> true | uu____284 -> false
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee -> match projectee with | Mul -> true | uu____290 -> false
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee -> match projectee with | Minus -> true | uu____296 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____302 -> false
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAnd -> true | uu____308 -> false
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BvXor -> true | uu____314 -> false
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvOr -> true | uu____320 -> false
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAdd -> true | uu____326 -> false
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee -> match projectee with | BvSub -> true | uu____332 -> false
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShl -> true | uu____338 -> false
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShr -> true | uu____344 -> false
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUdiv -> true | uu____350 -> false
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMod -> true | uu____356 -> false
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMul -> true | uu____362 -> false
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUlt -> true | uu____368 -> false
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BvUext _0 -> true | uu____375 -> false
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | BvUext _0 -> _0
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee ->
    match projectee with | NatToBv _0 -> true | uu____388 -> false
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | NatToBv _0 -> _0
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BvToNat -> true | uu____400 -> false
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee -> match projectee with | ITE -> true | uu____406 -> false
let (uu___is_Var : op -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu____413 -> false
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee -> match projectee with | Var _0 -> _0
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee -> match projectee with | Forall -> true | uu____425 -> false
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee -> match projectee with | Exists -> true | uu____431 -> false
type term' =
  | Integer of Prims.string 
  | String of Prims.string 
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
  fun projectee ->
    match projectee with | Integer _0 -> true | uu____561 -> false
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Integer _0 -> _0
let (uu___is_String : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____574 -> false
let (__proj__String__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Real _0 -> true | uu____587 -> false
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Real _0 -> _0
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | BoundV _0 -> true | uu____600 -> false
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee -> match projectee with | BoundV _0 -> _0
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | FreeV _0 -> true | uu____619 -> false
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee -> match projectee with | FreeV _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu____656 -> false
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quant _0 -> true | uu____705 -> false
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee -> match projectee with | Quant _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu____778 -> false
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Labeled _0 -> true | uu____815 -> false
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LblPos _0 -> true | uu____850 -> false
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
    match projectee with | Name _0 -> true | uu____1006 -> false
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee ->
    match projectee with | Namespace _0 -> true | uu____1019 -> false
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Namespace _0 -> _0
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee ->
    match projectee with | Tag _0 -> true | uu____1032 -> false
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
    match projectee with | DefPrelude -> true | uu____1193 -> false
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclFun _0 -> true | uu____1210 -> false
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee -> match projectee with | DeclFun _0 -> _0
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineFun _0 -> true | uu____1265 -> false
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee -> match projectee with | DefineFun _0 -> _0
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Assume _0 -> true | uu____1314 -> false
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Caption _0 -> true | uu____1327 -> false
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Caption _0 -> _0
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____1346 -> false
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Eval _0 -> true | uu____1377 -> false
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee -> match projectee with | Eval _0 -> _0
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Echo _0 -> true | uu____1390 -> false
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Echo _0 -> _0
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RetainAssumptions _0 -> true | uu____1405 -> false
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee -> match projectee with | RetainAssumptions _0 -> _0
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee -> match projectee with | Push -> true | uu____1423 -> false
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____1429 -> false
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckSat -> true | uu____1435 -> false
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetUnsatCore -> true | uu____1441 -> false
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOption _0 -> true | uu____1452 -> false
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | SetOption _0 -> _0
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetStatistics -> true | uu____1476 -> false
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetReasonUnknown -> true | uu____1482 -> false
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
          let uu____1625 =
            let uu____1626 =
              let sm = FStar_Util.smap_create (Prims.of_int (20)) in
              FStar_List.iter
                (fun elt ->
                   FStar_List.iter (fun s -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____1642 -> ()) decls;
              FStar_Util.smap_keys sm in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____1626
            } in
          [uu____1625]
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls ->
    let uu____1652 =
      let uu____1653 =
        FStar_List.collect
          (fun uu___0_1658 ->
             match uu___0_1658 with
             | Assume a -> [a.assumption_name]
             | uu____1662 -> []) decls in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____1653
      } in
    [uu____1652]
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l -> FStar_All.pipe_right l (FStar_List.collect (fun elt -> elt.decls))
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____1692 -> match uu____1692 with | (x, y) -> (x, y, false)
let (fv_name : fv -> Prims.string) =
  fun x ->
    let uu____1704 = x in
    match uu____1704 with | (nm, uu____1706, uu____1707) -> nm
let (fv_sort : fv -> sort) =
  fun x ->
    let uu____1713 = x in
    match uu____1713 with | (uu____1714, sort1, uu____1716) -> sort1
let (fv_force : fv -> Prims.bool) =
  fun x ->
    let uu____1722 = x in
    match uu____1722 with | (uu____1723, uu____1724, force) -> force
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x ->
    fun y ->
      let uu____1736 = fv_name x in
      let uu____1737 = fv_name y in uu____1736 = uu____1737
let (fvs_subset_of : fvs -> fvs -> Prims.bool) =
  fun x ->
    fun y ->
      let cmp_fv x1 y1 =
        let uu____1759 = fv_name x1 in
        let uu____1760 = fv_name y1 in
        FStar_Util.compare uu____1759 uu____1760 in
      let uu____1761 = FStar_Util.as_set x cmp_fv in
      let uu____1776 = FStar_Util.as_set y cmp_fv in
      FStar_Util.set_is_subset_of uu____1761 uu____1776
let (freevar_eq : term -> term -> Prims.bool) =
  fun x ->
    fun y ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1, FreeV y1) -> fv_eq x1 y1
      | uu____1821 -> false
let (freevar_sort : term -> sort) =
  fun uu___1_1830 ->
    match uu___1_1830 with
    | { tm = FreeV x; freevars = uu____1832; rng = uu____1833;_} -> fv_sort x
    | uu____1850 -> failwith "impossible"
let (fv_of_term : term -> fv) =
  fun uu___2_1855 ->
    match uu___2_1855 with
    | { tm = FreeV fv1; freevars = uu____1857; rng = uu____1858;_} -> fv1
    | uu____1875 -> failwith "impossible"
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t ->
    match t.tm with
    | Integer uu____1897 -> []
    | String uu____1904 -> []
    | Real uu____1911 -> []
    | BoundV uu____1918 -> []
    | FreeV fv1 when fv_force fv1 -> []
    | FreeV fv1 -> [fv1]
    | App (uu____1957, tms) -> FStar_List.collect freevars tms
    | Quant (uu____1969, uu____1970, uu____1971, uu____1972, t1) ->
        freevars t1
    | Labeled (t1, uu____1991, uu____1992) -> freevars t1
    | LblPos (t1, uu____1994) -> freevars t1
    | Let (es, body) -> FStar_List.collect freevars (body :: es)
let (free_variables : term -> fvs) =
  fun t ->
    let uu____2012 = FStar_ST.op_Bang t.freevars in
    match uu____2012 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None ->
        let fvs1 =
          let uu____2083 = freevars t in
          FStar_Util.remove_dups fv_eq uu____2083 in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs1);
         fvs1)
let (qop_to_string : qop -> Prims.string) =
  fun uu___3_2137 ->
    match uu___3_2137 with | Forall -> "forall" | Exists -> "exists"
let (op_to_string : op -> Prims.string) =
  fun uu___4_2142 ->
    match uu___4_2142 with
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
    | BvUext n ->
        let uu____2144 = FStar_Util.string_of_int n in
        FStar_Util.format1 "(_ zero_extend %s)" uu____2144
    | NatToBv n ->
        let uu____2146 = FStar_Util.string_of_int n in
        FStar_Util.format1 "(_ int2bv %s)" uu____2146
    | Var s -> s
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___5_2154 ->
    match uu___5_2154 with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____2158 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____2158
let rec (hash_of_term' : term' -> Prims.string) =
  fun t ->
    match t with
    | Integer i -> i
    | String s -> s
    | Real r -> r
    | BoundV i ->
        let uu____2172 = FStar_Util.string_of_int i in
        Prims.op_Hat "@" uu____2172
    | FreeV x ->
        let uu____2180 = fv_name x in
        let uu____2181 =
          let uu____2182 = let uu____2183 = fv_sort x in strSort uu____2183 in
          Prims.op_Hat ":" uu____2182 in
        Prims.op_Hat uu____2180 uu____2181
    | App (op1, tms) ->
        let uu____2190 =
          let uu____2191 = op_to_string op1 in
          let uu____2192 =
            let uu____2193 =
              let uu____2194 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____2194 (FStar_String.concat " ") in
            Prims.op_Hat uu____2193 ")" in
          Prims.op_Hat uu____2191 uu____2192 in
        Prims.op_Hat "(" uu____2190
    | Labeled (t1, r1, r2) ->
        let uu____2202 = hash_of_term t1 in
        let uu____2203 =
          let uu____2204 = FStar_Range.string_of_range r2 in
          Prims.op_Hat r1 uu____2204 in
        Prims.op_Hat uu____2202 uu____2203
    | LblPos (t1, r) ->
        let uu____2207 =
          let uu____2208 = hash_of_term t1 in
          Prims.op_Hat uu____2208
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")")) in
        Prims.op_Hat "(! " uu____2207
    | Quant (qop1, pats, wopt, sorts, body) ->
        let uu____2230 =
          let uu____2231 =
            let uu____2232 =
              let uu____2233 =
                let uu____2234 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____2234 (FStar_String.concat " ") in
              let uu____2239 =
                let uu____2240 =
                  let uu____2241 = hash_of_term body in
                  let uu____2242 =
                    let uu____2243 =
                      let uu____2244 = weightToSmt wopt in
                      let uu____2245 =
                        let uu____2246 =
                          let uu____2247 =
                            let uu____2248 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1 ->
                                      let uu____2264 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____2264
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____2248
                              (FStar_String.concat "; ") in
                          Prims.op_Hat uu____2247 "))" in
                        Prims.op_Hat " " uu____2246 in
                      Prims.op_Hat uu____2244 uu____2245 in
                    Prims.op_Hat " " uu____2243 in
                  Prims.op_Hat uu____2241 uu____2242 in
                Prims.op_Hat ")(! " uu____2240 in
              Prims.op_Hat uu____2233 uu____2239 in
            Prims.op_Hat " (" uu____2232 in
          Prims.op_Hat (qop_to_string qop1) uu____2231 in
        Prims.op_Hat "(" uu____2230
    | Let (es, body) ->
        let uu____2277 =
          let uu____2278 =
            let uu____2279 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____2279 (FStar_String.concat " ") in
          let uu____2284 =
            let uu____2285 =
              let uu____2286 = hash_of_term body in
              Prims.op_Hat uu____2286 ")" in
            Prims.op_Hat ") " uu____2285 in
          Prims.op_Hat uu____2278 uu____2284 in
        Prims.op_Hat "(let (" uu____2277
and (hash_of_term : term -> Prims.string) = fun tm -> hash_of_term' tm.tm
let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s -> (s, (Prims.op_Hat s "_proj_0"))
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt"
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool"
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString"
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz ->
    let uu____2318 =
      let uu____2319 = FStar_Util.string_of_int sz in
      Prims.op_Hat "BoxBitVec" uu____2319 in
    mkBoxFunctions uu____2318
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal"
let (isInjective : Prims.string -> Prims.bool) =
  fun s ->
    if (FStar_String.length s) >= (Prims.of_int (3))
    then
      (let uu____2331 =
         FStar_String.substring s Prims.int_zero (Prims.of_int (3)) in
       uu____2331 = "Box") &&
        (let uu____2333 =
           let uu____2334 = FStar_String.list_of_string s in
           FStar_List.existsML (fun c -> c = 46) uu____2334 in
         Prims.op_Negation uu____2333)
    else false
let (mk : term' -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      let uu____2350 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____2350; rng = r }
let (mkTrue : FStar_Range.range -> term) = fun r -> mk (App (TrueOp, [])) r
let (mkFalse : FStar_Range.range -> term) = fun r -> mk (App (FalseOp, [])) r
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____2403 =
        let uu____2404 = FStar_Util.ensure_decimal i in Integer uu____2404 in
      mk uu____2403 r
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____2415 = FStar_Util.string_of_int i in mkInteger uu____2415 r
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i -> fun r -> mk (Real i) r
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i -> fun r -> mk (BoundV i) r
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x -> fun r -> mk (FreeV x) r
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f -> fun r -> mk (App f) r
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____2482 ->
    fun r -> match uu____2482 with | (s, args) -> mk (App ((Var s), args)) r
let (mkNot : term -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      match t.tm with
      | App (TrueOp, uu____2508) -> mkFalse r
      | App (FalseOp, uu____2513) -> mkTrue r
      | uu____2518 -> mkApp' (Not, [t]) r
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____2533 ->
    fun r ->
      match uu____2533 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu____2541), uu____2542) -> t2
           | (uu____2547, App (TrueOp, uu____2548)) -> t1
           | (App (FalseOp, uu____2553), uu____2554) -> mkFalse r
           | (uu____2559, App (FalseOp, uu____2560)) -> mkFalse r
           | (App (And, ts1), App (And, ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____2577, App (And, ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And, ts1), uu____2586) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____2593 -> mkApp' (And, [t1; t2]) r)
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____2612 ->
    fun r ->
      match uu____2612 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu____2620), uu____2621) -> mkTrue r
           | (uu____2626, App (TrueOp, uu____2627)) -> mkTrue r
           | (App (FalseOp, uu____2632), uu____2633) -> t2
           | (uu____2638, App (FalseOp, uu____2639)) -> t1
           | (App (Or, ts1), App (Or, ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____2656, App (Or, ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or, ts1), uu____2665) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____2672 -> mkApp' (Or, [t1; t2]) r)
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____2691 ->
    fun r ->
      match uu____2691 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____2699, App (TrueOp, uu____2700)) -> mkTrue r
           | (App (FalseOp, uu____2705), uu____2706) -> mkTrue r
           | (App (TrueOp, uu____2711), uu____2712) -> t2
           | (uu____2717, App (Imp, t1'::t2'::[])) ->
               let uu____2722 =
                 let uu____2729 =
                   let uu____2732 = mkAnd (t1, t1') r in [uu____2732; t2'] in
                 (Imp, uu____2729) in
               mkApp' uu____2722 r
           | uu____2735 -> mkApp' (Imp, [t1; t2]) r)
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op1 ->
    fun uu____2759 ->
      fun r -> match uu____2759 with | (t1, t2) -> mkApp' (op1, [t1; t2]) r
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
    fun uu____2904 ->
      fun r ->
        match uu____2904 with
        | (t1, t2) ->
            let uu____2912 =
              let uu____2919 =
                let uu____2922 =
                  let uu____2925 = mkNatToBv sz t2 r in [uu____2925] in
                t1 :: uu____2922 in
              (BvShl, uu____2919) in
            mkApp' uu____2912 r
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____2945 ->
      fun r ->
        match uu____2945 with
        | (t1, t2) ->
            let uu____2953 =
              let uu____2960 =
                let uu____2963 =
                  let uu____2966 = mkNatToBv sz t2 r in [uu____2966] in
                t1 :: uu____2963 in
              (BvShr, uu____2960) in
            mkApp' uu____2953 r
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____2986 ->
      fun r ->
        match uu____2986 with
        | (t1, t2) ->
            let uu____2994 =
              let uu____3001 =
                let uu____3004 =
                  let uu____3007 = mkNatToBv sz t2 r in [uu____3007] in
                t1 :: uu____3004 in
              (BvUdiv, uu____3001) in
            mkApp' uu____2994 r
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____3027 ->
      fun r ->
        match uu____3027 with
        | (t1, t2) ->
            let uu____3035 =
              let uu____3042 =
                let uu____3045 =
                  let uu____3048 = mkNatToBv sz t2 r in [uu____3048] in
                t1 :: uu____3045 in
              (BvMod, uu____3042) in
            mkApp' uu____3035 r
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz ->
    fun uu____3068 ->
      fun r ->
        match uu____3068 with
        | (t1, t2) ->
            let uu____3076 =
              let uu____3083 =
                let uu____3086 =
                  let uu____3089 = mkNatToBv sz t2 r in [uu____3089] in
                t1 :: uu____3086 in
              (BvMul, uu____3083) in
            mkApp' uu____3076 r
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____3128 ->
    fun r ->
      match uu____3128 with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1, s1::[]), App (Var f2, s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____3144 -> mk_bin_op Eq (t1, t2) r)
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
  fun uu____3295 ->
    fun r ->
      match uu____3295 with
      | (t1, t2, t3) ->
          (match t1.tm with
           | App (TrueOp, uu____3306) -> t2
           | App (FalseOp, uu____3311) -> t3
           | uu____3316 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp, uu____3317), App (TrueOp, uu____3318)) ->
                    mkTrue r
                | (App (TrueOp, uu____3327), uu____3328) ->
                    let uu____3333 =
                      let uu____3338 = mkNot t1 t1.rng in (uu____3338, t3) in
                    mkImp uu____3333 r
                | (uu____3339, App (TrueOp, uu____3340)) -> mkImp (t1, t2) r
                | (uu____3345, uu____3346) -> mkApp' (ITE, [t1; t2; t3]) r))
let (mkCases : term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun r ->
      match t with
      | [] -> failwith "Impos"
      | hd::tl ->
          FStar_List.fold_left (fun out -> fun t1 -> mkAnd (out, t1) r) hd tl
let (check_pattern_ok : term -> term FStar_Pervasives_Native.option) =
  fun t ->
    let rec aux t1 =
      match t1.tm with
      | Integer uu____3399 -> FStar_Pervasives_Native.None
      | String uu____3400 -> FStar_Pervasives_Native.None
      | Real uu____3401 -> FStar_Pervasives_Native.None
      | BoundV uu____3402 -> FStar_Pervasives_Native.None
      | FreeV uu____3403 -> FStar_Pervasives_Native.None
      | Let (tms, tm) -> aux_l (tm :: tms)
      | App (head, terms) ->
          let head_ok =
            match head with
            | Var uu____3423 -> true
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
            | BvUext uu____3424 -> false
            | NatToBv uu____3425 -> false
            | BvToNat -> false
            | ITE -> false in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2, uu____3430, uu____3431) -> aux t2
      | Quant uu____3432 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____3451 -> FStar_Pervasives_Native.Some t1
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____3465 = aux t1 in
          (match uu____3465 with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None -> aux_l ts1) in
    aux t
let rec (print_smt_term : term -> Prims.string) =
  fun t ->
    match t.tm with
    | Integer n -> FStar_Util.format1 "(Integer %s)" n
    | String s -> FStar_Util.format1 "(String %s)" s
    | Real r -> FStar_Util.format1 "(Real %s)" r
    | BoundV n ->
        let uu____3494 = FStar_Util.string_of_int n in
        FStar_Util.format1 "(BoundV %s)" uu____3494
    | FreeV fv1 ->
        let uu____3502 = fv_name fv1 in
        FStar_Util.format1 "(FreeV %s)" uu____3502
    | App (op1, l) ->
        let uu____3509 = op_to_string op1 in
        let uu____3510 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" uu____3509 uu____3510
    | Labeled (t1, r1, r2) ->
        let uu____3514 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3514
    | LblPos (t1, s) ->
        let uu____3517 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3517
    | Quant (qop1, l, uu____3520, uu____3521, t1) ->
        let uu____3539 = print_smt_term_list_list l in
        let uu____3540 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop1) uu____3539
          uu____3540
    | Let (es, body) ->
        let uu____3547 = print_smt_term_list es in
        let uu____3548 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3547 uu____3548
and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l ->
    let uu____3552 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3552 (FStar_String.concat " ")
and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l ->
    FStar_List.fold_left
      (fun s ->
         fun l1 ->
           let uu____3571 =
             let uu____3572 =
               let uu____3573 = print_smt_term_list l1 in
               Prims.op_Hat uu____3573 " ] " in
             Prims.op_Hat "; [ " uu____3572 in
           Prims.op_Hat s uu____3571) "" l
let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r ->
    fun check_pats ->
      fun uu____3606 ->
        match uu____3606 with
        | (qop1, pats, wopt, vars, body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____3669 =
                   FStar_Util.find_map pats1
                     (fun x -> FStar_Util.find_map x check_pattern_ok) in
                 match uu____3669 with
                 | FStar_Pervasives_Native.None -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____3684 =
                         let uu____3689 =
                           let uu____3690 = print_smt_term p in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____3690 in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____3689) in
                       FStar_Errors.log_issue r uu____3684);
                      [])) in
            if (FStar_List.length vars) = Prims.int_zero
            then body
            else
              (match body.tm with
               | App (TrueOp, uu____3694) -> body
               | uu____3699 ->
                   let uu____3700 =
                     let uu____3701 =
                       let uu____3720 = all_pats_ok pats in
                       (qop1, uu____3720, wopt, vars, body) in
                     Quant uu____3701 in
                   mk uu____3700 r)
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____3747 ->
    fun r ->
      match uu____3747 with
      | (es, body) ->
          if (FStar_List.length es) = Prims.int_zero
          then body
          else mk (Let (es, body)) r
let (abstr : fv Prims.list -> term -> term) =
  fun fvs1 ->
    fun t ->
      let nvars = FStar_List.length fvs1 in
      let index_of fv1 =
        let uu____3787 = FStar_Util.try_find_index (fv_eq fv1) fvs1 in
        match uu____3787 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some (nvars - (i + Prims.int_one)) in
      let rec aux ix t1 =
        let uu____3804 = FStar_ST.op_Bang t1.freevars in
        match uu____3804 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____3855 ->
            (match t1.tm with
             | Integer uu____3866 -> t1
             | String uu____3867 -> t1
             | Real uu____3868 -> t1
             | BoundV uu____3869 -> t1
             | FreeV x ->
                 let uu____3877 = index_of x in
                 (match uu____3877 with
                  | FStar_Pervasives_Native.None -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op1, tms) ->
                 let uu____3887 =
                   let uu____3894 = FStar_List.map (aux ix) tms in
                   (op1, uu____3894) in
                 mkApp' uu____3887 t1.rng
             | Labeled (t2, r1, r2) ->
                 let uu____3902 =
                   let uu____3903 =
                     let uu____3910 = aux ix t2 in (uu____3910, r1, r2) in
                   Labeled uu____3903 in
                 mk uu____3902 t2.rng
             | LblPos (t2, r) ->
                 let uu____3913 =
                   let uu____3914 =
                     let uu____3919 = aux ix t2 in (uu____3919, r) in
                   LblPos uu____3914 in
                 mk uu____3913 t2.rng
             | Quant (qop1, pats, wopt, vars, body) ->
                 let n = FStar_List.length vars in
                 let uu____3942 =
                   let uu____3961 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n)))) in
                   let uu____3978 = aux (ix + n) body in
                   (qop1, uu____3961, wopt, vars, uu____3978) in
                 mkQuant t1.rng false uu____3942
             | Let (es, body) ->
                 let uu____3993 =
                   FStar_List.fold_left
                     (fun uu____4011 ->
                        fun e ->
                          match uu____4011 with
                          | (ix1, l) ->
                              let uu____4031 =
                                let uu____4034 = aux ix1 e in uu____4034 :: l in
                              ((ix1 + Prims.int_one), uu____4031)) (ix, [])
                     es in
                 (match uu____3993 with
                  | (ix1, es_rev) ->
                      let uu____4045 =
                        let uu____4052 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____4052) in
                      mkLet uu____4045 t1.rng)) in
      aux Prims.int_zero t
let (inst : term Prims.list -> term -> term) =
  fun tms ->
    fun t ->
      let tms1 = FStar_List.rev tms in
      let n = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____4084 -> t1
        | String uu____4085 -> t1
        | Real uu____4086 -> t1
        | FreeV uu____4087 -> t1
        | BoundV i ->
            if (Prims.int_zero <= (i - shift)) && ((i - shift) < n)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op1, tms2) ->
            let uu____4102 =
              let uu____4109 = FStar_List.map (aux shift) tms2 in
              (op1, uu____4109) in
            mkApp' uu____4102 t1.rng
        | Labeled (t2, r1, r2) ->
            let uu____4117 =
              let uu____4118 =
                let uu____4125 = aux shift t2 in (uu____4125, r1, r2) in
              Labeled uu____4118 in
            mk uu____4117 t2.rng
        | LblPos (t2, r) ->
            let uu____4128 =
              let uu____4129 =
                let uu____4134 = aux shift t2 in (uu____4134, r) in
              LblPos uu____4129 in
            mk uu____4128 t2.rng
        | Quant (qop1, pats, wopt, vars, body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____4158 =
              let uu____4177 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____4194 = aux shift1 body in
              (qop1, uu____4177, wopt, vars, uu____4194) in
            mkQuant t1.rng false uu____4158
        | Let (es, body) ->
            let uu____4209 =
              FStar_List.fold_left
                (fun uu____4227 ->
                   fun e ->
                     match uu____4227 with
                     | (ix, es1) ->
                         let uu____4247 =
                           let uu____4250 = aux shift e in uu____4250 :: es1 in
                         ((shift + Prims.int_one), uu____4247)) (shift, [])
                es in
            (match uu____4209 with
             | (shift1, es_rev) ->
                 let uu____4261 =
                   let uu____4268 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____4268) in
                 mkLet uu____4261 t1.rng) in
      aux Prims.int_zero t
let (subst : term -> fv -> term -> term) =
  fun t ->
    fun fv1 -> fun s -> let uu____4286 = abstr [fv1] t in inst [s] uu____4286
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r ->
    fun uu____4314 ->
      match uu____4314 with
      | (qop1, pats, wopt, vars, body) ->
          let uu____4354 =
            let uu____4373 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars))) in
            let uu____4390 = FStar_List.map fv_sort vars in
            let uu____4393 = abstr vars body in
            (qop1, uu____4373, wopt, uu____4390, uu____4393) in
          mkQuant r true uu____4354
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r ->
    fun uu____4421 ->
      match uu____4421 with
      | (pats, vars, body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r ->
    fun uu____4476 ->
      match uu____4476 with
      | (pats, wopt, sorts, body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r ->
    fun uu____4544 ->
      match uu____4544 with
      | (pats, wopt, vars, body) ->
          mkQuant' r (Forall, pats, wopt, vars, body)
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r ->
    fun uu____4602 ->
      match uu____4602 with
      | (pats, vars, body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____4650 ->
    fun r ->
      match uu____4650 with
      | (bindings, body) ->
          let uu____4676 = FStar_List.split bindings in
          (match uu____4676 with
           | (vars, es) ->
               let uu____4695 =
                 let uu____4702 = abstr vars body in (es, uu____4702) in
               mkLet uu____4695 r)
let (norng : FStar_Range.range) = FStar_Range.dummyRange
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____4721 ->
    match uu____4721 with
    | (nm, vars, s, tm, c) ->
        let uu____4743 =
          let uu____4756 = FStar_List.map fv_sort vars in
          let uu____4759 = abstr vars tm in
          (nm, uu____4756, s, uu____4759, c) in
        DefineFun uu____4743
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort1 ->
    let uu____4767 = strSort sort1 in
    FStar_Util.format1 "%s_constr_id" uu____4767
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____4780 ->
    fun id ->
      match uu____4780 with
      | (tok_name, sort1) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name in
          let a =
            let uu____4790 =
              let uu____4791 =
                let uu____4796 = mkInteger' id norng in
                let uu____4797 =
                  let uu____4798 =
                    let uu____4805 = constr_id_of_sort sort1 in
                    let uu____4806 =
                      let uu____4809 = mkApp (tok_name, []) norng in
                      [uu____4809] in
                    (uu____4805, uu____4806) in
                  mkApp uu____4798 norng in
                (uu____4796, uu____4797) in
              mkEq uu____4791 norng in
            let uu____4814 = escape a_name in
            {
              assumption_term = uu____4790;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____4814;
              assumption_fact_ids = []
            } in
          Assume a
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng ->
    fun uu____4834 ->
      match uu____4834 with
      | (name, arg_sorts, sort1, id) ->
          let id1 = FStar_Util.string_of_int id in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i ->
                    fun s ->
                      let uu____4866 =
                        let uu____4867 =
                          let uu____4872 =
                            let uu____4873 = FStar_Util.string_of_int i in
                            Prims.op_Hat "x_" uu____4873 in
                          (uu____4872, s) in
                        mk_fv uu____4867 in
                      mkFreeV uu____4866 norng)) in
          let bvar_names = FStar_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let cid_app =
            let uu____4893 =
              let uu____4900 = constr_id_of_sort sort1 in
              (uu____4900, [capp]) in
            mkApp uu____4893 norng in
          let a_name = Prims.op_Hat "constructor_distinct_" name in
          let a =
            let uu____4905 =
              let uu____4906 =
                let uu____4917 =
                  let uu____4918 =
                    let uu____4923 = mkInteger id1 norng in
                    (uu____4923, cid_app) in
                  mkEq uu____4918 norng in
                ([[capp]], bvar_names, uu____4917) in
              mkForall rng uu____4906 in
            let uu____4932 = escape a_name in
            {
              assumption_term = uu____4905;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____4932;
              assumption_fact_ids = []
            } in
          Assume a
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng ->
    fun uu____4952 ->
      match uu____4952 with
      | (name, fields, sort1) ->
          let n_bvars = FStar_List.length fields in
          let bvar_name i =
            let uu____4979 = FStar_Util.string_of_int i in
            Prims.op_Hat "x_" uu____4979 in
          let bvar_index i = n_bvars - (i + Prims.int_one) in
          let bvar i s =
            let uu____5000 =
              let uu____5001 =
                let uu____5006 = bvar_name i in (uu____5006, s) in
              mk_fv uu____5001 in
            FStar_All.pipe_left mkFreeV uu____5000 in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i ->
                    fun uu____5036 ->
                      match uu____5036 with
                      | (uu____5043, s, uu____5045) ->
                          let uu____5046 = bvar i s in uu____5046 norng)) in
          let bvar_names = FStar_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let uu____5069 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i ->
                    fun uu____5103 ->
                      match uu____5103 with
                      | (name1, s, projectible) ->
                          let cproj_app = mkApp (name1, [capp]) norng in
                          let proj_name =
                            DeclFun
                              (name1, [sort1], s,
                                (FStar_Pervasives_Native.Some "Projector")) in
                          if projectible
                          then
                            let a =
                              let uu____5124 =
                                let uu____5125 =
                                  let uu____5136 =
                                    let uu____5137 =
                                      let uu____5142 =
                                        let uu____5143 = bvar i s in
                                        uu____5143 norng in
                                      (cproj_app, uu____5142) in
                                    mkEq uu____5137 norng in
                                  ([[capp]], bvar_names, uu____5136) in
                                mkForall rng uu____5125 in
                              let uu____5156 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1) in
                              {
                                assumption_term = uu____5124;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____5156;
                                assumption_fact_ids = []
                              } in
                            [proj_name; Assume a]
                          else [proj_name])) in
          FStar_All.pipe_right uu____5069 FStar_List.flatten
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng ->
    fun uu____5175 ->
      match uu____5175 with
      | (name, fields, sort1, id, injective) ->
          let injective1 = injective || true in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____5211 ->
                    match uu____5211 with
                    | (uu____5218, sort2, uu____5220) -> sort2)) in
          let cdecl =
            DeclFun
              (name, field_sorts, sort1,
                (FStar_Pervasives_Native.Some "Constructor")) in
          let cid = fresh_constructor rng (name, field_sorts, sort1, id) in
          let disc =
            let disc_name = Prims.op_Hat "is-" name in
            let xfv = mk_fv ("x", sort1) in
            let xx = mkFreeV xfv norng in
            let disc_eq =
              let uu____5232 =
                let uu____5237 =
                  let uu____5238 =
                    let uu____5245 = constr_id_of_sort sort1 in
                    (uu____5245, [xx]) in
                  mkApp uu____5238 norng in
                let uu____5248 =
                  let uu____5249 = FStar_Util.string_of_int id in
                  mkInteger uu____5249 norng in
                (uu____5237, uu____5248) in
              mkEq uu____5232 norng in
            let uu____5250 =
              let uu____5267 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i ->
                        fun uu____5323 ->
                          match uu____5323 with
                          | (proj, s, projectible) ->
                              if projectible
                              then
                                let uu____5345 = mkApp (proj, [xx]) norng in
                                (uu____5345, [])
                              else
                                (let fi =
                                   let uu____5352 =
                                     let uu____5357 =
                                       let uu____5358 =
                                         FStar_Util.string_of_int i in
                                       Prims.op_Hat "f_" uu____5358 in
                                     (uu____5357, s) in
                                   mk_fv uu____5352 in
                                 let uu____5359 = mkFreeV fi norng in
                                 (uu____5359, [fi])))) in
              FStar_All.pipe_right uu____5267 FStar_List.split in
            match uu____5250 with
            | (proj_terms, ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars in
                let disc_inv_body =
                  let uu____5442 =
                    let uu____5447 = mkApp (name, proj_terms) norng in
                    (xx, uu____5447) in
                  mkEq uu____5442 norng in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____5457 ->
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
            then injective_constructor rng (name, fields, sort1)
            else [] in
          let uu____5484 =
            let uu____5487 =
              let uu____5488 =
                FStar_Util.format1 "<start constructor %s>" name in
              Caption uu____5488 in
            uu____5487 :: cdecl :: cid :: projs in
          let uu____5489 =
            let uu____5492 =
              let uu____5495 =
                let uu____5496 =
                  FStar_Util.format1 "</end constructor %s>" name in
                Caption uu____5496 in
              [uu____5495] in
            FStar_List.append [disc] uu____5492 in
          FStar_List.append uu____5484 uu____5489
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
          let uu____5539 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____5582 ->
                    fun s ->
                      match uu____5582 with
                      | (names, binders1, n) ->
                          let prefix =
                            match s with
                            | Term_sort -> "@x"
                            | uu____5616 -> "@u" in
                          let prefix1 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None -> prefix
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix in
                          let nm =
                            let uu____5620 = FStar_Util.string_of_int n in
                            Prims.op_Hat prefix1 uu____5620 in
                          let names1 =
                            let uu____5624 = mk_fv (nm, s) in uu____5624 ::
                              names in
                          let b =
                            let uu____5626 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____5626 in
                          (names1, (b :: binders1), (n + Prims.int_one)))
                 (outer_names, [], start)) in
          match uu____5539 with
          | (names, binders1, n) -> (names, (FStar_List.rev binders1), n)
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts ->
    let uu____5677 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        Prims.int_zero sorts in
    match uu____5677 with
    | (names, binders1, n) -> ((FStar_List.rev names), binders1)
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  let string_id_counter = FStar_Util.mk_ref Prims.int_zero in
  let string_cache = FStar_Util.smap_create (Prims.of_int (20)) in
  fun print_ranges ->
    fun enclosing_name ->
      fun t ->
        let next_qid =
          let ctr = FStar_Util.mk_ref Prims.int_zero in
          fun depth ->
            let n = FStar_ST.op_Bang ctr in
            FStar_Util.incr ctr;
            if n = Prims.int_zero
            then enclosing_name
            else
              (let uu____5750 = FStar_Util.string_of_int n in
               FStar_Util.format2 "%s.%s" enclosing_name uu____5750) in
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
                               { tm = BoundV uu____5794;
                                 freevars = uu____5795; rng = uu____5796;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free", p::[]) -> p
                          | uu____5812 -> tm)))) in
        let rec aux' depth n names t1 =
          let aux1 = aux (depth + Prims.int_one) in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | String s ->
              let id_opt = FStar_Util.smap_try_find string_cache s in
              (match id_opt with
               | FStar_Pervasives_Native.Some id -> id
               | FStar_Pervasives_Native.None ->
                   let id =
                     let uu____5880 = FStar_ST.op_Bang string_id_counter in
                     FStar_All.pipe_right uu____5880 FStar_Util.string_of_int in
                   (FStar_Util.incr string_id_counter;
                    FStar_Util.smap_add string_cache s id;
                    id))
          | BoundV i ->
              let uu____5890 = FStar_List.nth names i in
              FStar_All.pipe_right uu____5890 fv_name
          | FreeV x when fv_force x ->
              let uu____5898 =
                let uu____5899 = fv_name x in
                Prims.op_Hat uu____5899 " Dummy_value)" in
              Prims.op_Hat "(" uu____5898
          | FreeV x -> fv_name x
          | App (op1, []) -> op_to_string op1
          | App (op1, tms) ->
              let uu____5916 = op_to_string op1 in
              let uu____5917 =
                let uu____5918 = FStar_List.map (aux1 n names) tms in
                FStar_All.pipe_right uu____5918 (FStar_String.concat "\n") in
              FStar_Util.format2 "(%s %s)" uu____5916 uu____5917
          | Labeled (t2, uu____5924, uu____5925) -> aux1 n names t2
          | LblPos (t2, s) ->
              let uu____5928 = aux1 n names t2 in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____5928 s
          | Quant (qop1, pats, wopt, sorts, body) ->
              let qid = next_qid () in
              let uu____5951 =
                name_binders_inner FStar_Pervasives_Native.None names n sorts in
              (match uu____5951 with
               | (names1, binders1, n1) ->
                   let binders2 =
                     FStar_All.pipe_right binders1 (FStar_String.concat " ") in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____5988 ->
                         let uu____5993 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2 ->
                                   let uu____6009 =
                                     let uu____6010 =
                                       FStar_List.map
                                         (fun p ->
                                            let uu____6016 = aux1 n1 names1 p in
                                            FStar_Util.format1 "%s"
                                              uu____6016) pats2 in
                                     FStar_String.concat " " uu____6010 in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____6009)) in
                         FStar_All.pipe_right uu____5993
                           (FStar_String.concat "\n") in
                   let uu____6019 =
                     let uu____6022 =
                       let uu____6025 =
                         let uu____6028 = aux1 n1 names1 body in
                         let uu____6029 =
                           let uu____6032 = weightToSmt wopt in
                           [uu____6032; pats_str; qid] in
                         uu____6028 :: uu____6029 in
                       binders2 :: uu____6025 in
                     (qop_to_string qop1) :: uu____6022 in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____6019)
          | Let (es, body) ->
              let uu____6039 =
                FStar_List.fold_left
                  (fun uu____6068 ->
                     fun e ->
                       match uu____6068 with
                       | (names0, binders1, n0) ->
                           let nm =
                             let uu____6102 = FStar_Util.string_of_int n0 in
                             Prims.op_Hat "@lb" uu____6102 in
                           let names01 =
                             let uu____6106 = mk_fv (nm, Term_sort) in
                             uu____6106 :: names0 in
                           let b =
                             let uu____6108 = aux1 n names e in
                             FStar_Util.format2 "(%s %s)" nm uu____6108 in
                           (names01, (b :: binders1), (n0 + Prims.int_one)))
                  (names, [], n) es in
              (match uu____6039 with
               | (names1, binders1, n1) ->
                   let uu____6128 = aux1 n1 names1 body in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders1) uu____6128)
        and aux depth n names t1 =
          let s = aux' depth n names t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____6136 = FStar_Range.string_of_range t1.rng in
            let uu____6137 = FStar_Range.string_of_use_range t1.rng in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____6136
              uu____6137 s
          else s in
        aux Prims.int_zero Prims.int_zero [] t
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions ->
    fun uu___6_6150 ->
      match uu___6_6150 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____6155 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string) in
            FStar_All.pipe_right uu____6155 (FStar_String.concat " ") in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____6164 -> ""
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions ->
    fun z3options ->
      fun decl1 ->
        match decl1 with
        | DefPrelude -> mkPrelude z3options
        | Module (s, decls) ->
            let res =
              let uu____6201 =
                FStar_List.map (declToSmt' print_captions z3options) decls in
              FStar_All.pipe_right uu____6201 (FStar_String.concat "\n") in
            let uu____6206 = FStar_Options.keep_query_captions () in
            if uu____6206
            then
              let uu____6207 =
                FStar_Util.string_of_int (FStar_List.length decls) in
              let uu____6208 =
                FStar_Util.string_of_int (FStar_String.length res) in
              FStar_Util.format5
                "\n;;; Start %s\n%s\n;;; End %s (%s decls; total size %s)" s
                res s uu____6207 uu____6208
            else res
        | Caption c ->
            if print_captions
            then
              let uu____6211 =
                let uu____6212 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s -> Prims.op_Hat "; " (Prims.op_Hat s "\n"))) in
                FStar_All.pipe_right uu____6212 (FStar_String.concat "") in
              Prims.op_Hat "\n" uu____6211
            else ""
        | DeclFun (f, argsorts, retsort, c) ->
            let l = FStar_List.map strSort argsorts in
            let uu____6235 = caption_to_string print_captions c in
            let uu____6236 = strSort retsort in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____6235 f
              (FStar_String.concat " " l) uu____6236
        | DefineFun (f, arg_sorts, retsort, body, c) ->
            let uu____6246 = name_macro_binders arg_sorts in
            (match uu____6246 with
             | (names, binders1) ->
                 let body1 =
                   let uu____6266 =
                     FStar_List.map (fun x -> mkFreeV x norng) names in
                   inst uu____6266 body in
                 let uu____6271 = caption_to_string print_captions c in
                 let uu____6272 = strSort retsort in
                 let uu____6273 =
                   let uu____6274 = escape f in
                   termToSmt print_captions uu____6274 body1 in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____6271 f (FStar_String.concat " " binders1) uu____6272
                   uu____6273)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___7_6295 ->
                      match uu___7_6295 with
                      | Name n ->
                          let uu____6297 = FStar_Ident.string_of_lid n in
                          Prims.op_Hat "Name " uu____6297
                      | Namespace ns ->
                          let uu____6299 = FStar_Ident.string_of_lid ns in
                          Prims.op_Hat "Namespace " uu____6299
                      | Tag t -> Prims.op_Hat "Tag " t)) in
            let fids =
              if print_captions
              then
                let uu____6302 =
                  let uu____6303 = fact_ids_to_string a.assumption_fact_ids in
                  FStar_String.concat "; " uu____6303 in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____6302
              else "" in
            let n = a.assumption_name in
            let uu____6308 =
              caption_to_string print_captions a.assumption_caption in
            let uu____6309 = termToSmt print_captions n a.assumption_term in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____6308
              fids uu____6309 n
        | Eval t ->
            let uu____6311 = termToSmt print_captions "eval" t in
            FStar_Util.format1 "(eval %s)" uu____6311
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____6313 -> ""
        | CheckSat ->
            "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
        | GetUnsatCore ->
            "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
        | Push -> "(push)"
        | Pop -> "(pop)"
        | SetOption (s, v) -> FStar_Util.format2 "(set-option :%s %s)" s v
        | GetStatistics ->
            "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
        | GetReasonUnknown ->
            "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and (declToSmt : Prims.string -> decl -> Prims.string) =
  fun z3options ->
    fun decl1 ->
      let uu____6320 = FStar_Options.keep_query_captions () in
      declToSmt' uu____6320 z3options decl1
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
      let uu____6343 =
        let uu____6346 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng)) in
        FStar_All.pipe_right uu____6346
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____6343 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n" in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n" in
    let uu____6362 =
      let uu____6363 =
        let uu____6364 =
          let uu____6365 =
            let uu____6366 = FStar_Options.smtencoding_valid_intro () in
            if uu____6366 then valid_intro else "" in
          let uu____6368 =
            let uu____6369 = FStar_Options.smtencoding_valid_elim () in
            if uu____6369 then valid_elim else "" in
          Prims.op_Hat uu____6365 uu____6368 in
        Prims.op_Hat lex_ordering uu____6364 in
      Prims.op_Hat bcons uu____6363 in
    Prims.op_Hat basic uu____6362
let (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options ->
    fun decls ->
      let uu____6385 = FStar_List.map (declToSmt z3options) decls in
      FStar_All.pipe_right uu____6385 (FStar_String.concat "\n")
let (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options -> fun decl1 -> declToSmt' false z3options decl1
let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz ->
    let uu____6407 =
      let uu____6408 =
        let uu____6409 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6409 in
      let uu____6414 =
        let uu____6417 =
          let uu____6418 =
            let uu____6419 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu____6419 in
          (uu____6418, (BitVec_sort sz), true) in
        [uu____6417] in
      (uu____6408, uu____6414, Term_sort, ((Prims.of_int (12)) + sz), true) in
    FStar_All.pipe_right uu____6407 (constructor_to_decl norng)
let (__range_c : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (mk_Range_const : unit -> term) =
  fun uu____6434 ->
    let i = FStar_ST.op_Bang __range_c in
    (let uu____6443 =
       let uu____6444 = FStar_ST.op_Bang __range_c in
       uu____6444 + Prims.int_one in
     FStar_ST.op_Colon_Equals __range_c uu____6443);
    (let uu____6457 =
       let uu____6464 = let uu____6467 = mkInteger' i norng in [uu____6467] in
       ("Range_const", uu____6464) in
     mkApp uu____6457 norng)
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1 -> fun t2 -> fun r -> mkApp ("Tm_app", [t1; t2]) r
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i ->
    fun r ->
      let uu____6499 =
        let uu____6506 = let uu____6509 = mkInteger' i norng in [uu____6509] in
        ("Tm_uvar", uu____6506) in
      mkApp uu____6499 r
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond ->
    fun u ->
      fun v ->
        fun t ->
          match t.tm with
          | App (Var v', t1::[]) when (v = v') && cond -> t1
          | uu____6538 -> mkApp (u, [t]) t.rng
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u ->
    fun v ->
      fun t ->
        let uu____6556 = FStar_Options.smtencoding_elim_box () in
        elim_box uu____6556 u v t
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
      let uu____6607 =
        let uu____6608 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6608 in
      let uu____6613 =
        let uu____6614 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6614 in
      elim_box true uu____6607 uu____6613 t
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz ->
    fun t ->
      let uu____6629 =
        let uu____6630 = boxBitVecFun sz in
        FStar_Pervasives_Native.snd uu____6630 in
      let uu____6635 =
        let uu____6636 = boxBitVecFun sz in
        FStar_Pervasives_Native.fst uu____6636 in
      elim_box true uu____6629 uu____6635 t
let (boxTerm : sort -> term -> term) =
  fun sort1 ->
    fun t ->
      match sort1 with
      | Int_sort -> boxInt t
      | Bool_sort -> boxBool t
      | String_sort -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____6652 -> FStar_Exn.raise FStar_Util.Impos
let (unboxTerm : sort -> term -> term) =
  fun sort1 ->
    fun t ->
      match sort1 with
      | Int_sort -> unboxInt t
      | Bool_sort -> unboxBool t
      | String_sort -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____6664 -> FStar_Exn.raise FStar_Util.Impos
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t ->
    match t.tm with
    | App (Var s, t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n ->
             let uu____6681 = FStar_Util.int_of_string n in
             FStar_Pervasives_Native.Some uu____6681
         | uu____6682 -> FStar_Pervasives_Native.None)
    | uu____6683 -> FStar_Pervasives_Native.None
let (mk_PreType : term -> term) = fun t -> mkApp ("PreType", [t]) t.rng
let (mk_Valid : term -> term) =
  fun t ->
    match t.tm with
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Equality", uu____6696::t1::t2::[]);
           freevars = uu____6699; rng = uu____6700;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_disEquality", uu____6715::t1::t2::[]);
           freevars = uu____6718; rng = uu____6719;_}::[])
        -> let uu____6734 = mkEq (t1, t2) norng in mkNot uu____6734 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThanOrEqual", t1::t2::[]);
           freevars = uu____6737; rng = uu____6738;_}::[])
        ->
        let uu____6753 =
          let uu____6758 = unboxInt t1 in
          let uu____6759 = unboxInt t2 in (uu____6758, uu____6759) in
        mkLTE uu____6753 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThan", t1::t2::[]);
           freevars = uu____6762; rng = uu____6763;_}::[])
        ->
        let uu____6778 =
          let uu____6783 = unboxInt t1 in
          let uu____6784 = unboxInt t2 in (uu____6783, uu____6784) in
        mkLT uu____6778 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThanOrEqual", t1::t2::[]);
           freevars = uu____6787; rng = uu____6788;_}::[])
        ->
        let uu____6803 =
          let uu____6808 = unboxInt t1 in
          let uu____6809 = unboxInt t2 in (uu____6808, uu____6809) in
        mkGTE uu____6803 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThan", t1::t2::[]);
           freevars = uu____6812; rng = uu____6813;_}::[])
        ->
        let uu____6828 =
          let uu____6833 = unboxInt t1 in
          let uu____6834 = unboxInt t2 in (uu____6833, uu____6834) in
        mkGT uu____6828 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_AmpAmp", t1::t2::[]);
           freevars = uu____6837; rng = uu____6838;_}::[])
        ->
        let uu____6853 =
          let uu____6858 = unboxBool t1 in
          let uu____6859 = unboxBool t2 in (uu____6858, uu____6859) in
        mkAnd uu____6853 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_BarBar", t1::t2::[]);
           freevars = uu____6862; rng = uu____6863;_}::[])
        ->
        let uu____6878 =
          let uu____6883 = unboxBool t1 in
          let uu____6884 = unboxBool t2 in (uu____6883, uu____6884) in
        mkOr uu____6878 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Negation", t1::[]); freevars = uu____6886;
           rng = uu____6887;_}::[])
        -> let uu____6902 = unboxBool t1 in mkNot uu____6902 t1.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]);
           freevars = uu____6906; rng = uu____6907;_}::[])
        when
        let uu____6922 = getBoxedInteger t0 in FStar_Util.is_some uu____6922
        ->
        let sz =
          let uu____6926 = getBoxedInteger t0 in
          match uu____6926 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6930 -> failwith "impossible" in
        let uu____6933 =
          let uu____6938 = unboxBitVec sz t1 in
          let uu____6939 = unboxBitVec sz t2 in (uu____6938, uu____6939) in
        mkBvUlt uu____6933 t.rng
    | App
        (Var "Prims.equals",
         uu____6940::{ tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]);
                       freevars = uu____6944; rng = uu____6945;_}::uu____6946::[])
        when
        let uu____6961 = getBoxedInteger t0 in FStar_Util.is_some uu____6961
        ->
        let sz =
          let uu____6965 = getBoxedInteger t0 in
          match uu____6965 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____6969 -> failwith "impossible" in
        let uu____6972 =
          let uu____6977 = unboxBitVec sz t1 in
          let uu____6978 = unboxBitVec sz t2 in (uu____6977, uu____6978) in
        mkBvUlt uu____6972 t.rng
    | App (Var "Prims.b2t", t1::[]) ->
        let uu___1422_6982 = unboxBool t1 in
        {
          tm = (uu___1422_6982.tm);
          freevars = (uu___1422_6982.freevars);
          rng = (t.rng)
        }
    | uu____6983 -> mkApp ("Valid", [t]) t.rng
let (mk_HasType : term -> term -> term) =
  fun v -> fun t -> mkApp ("HasType", [v; t]) t.rng
let (mk_HasTypeZ : term -> term -> term) =
  fun v -> fun t -> mkApp ("HasTypeZ", [v; t]) t.rng
let (mk_IsTotFun : term -> term) = fun t -> mkApp ("IsTotFun", [t]) t.rng
let (mk_IsTyped : term -> term) = fun v -> mkApp ("IsTyped", [v]) norng
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f ->
    fun v ->
      fun t ->
        let uu____7039 = FStar_Options.unthrottle_inductives () in
        if uu____7039
        then mk_HasType v t
        else mkApp ("HasTypeFuel", [f; v; t]) t.rng
let (mk_HasTypeWithFuel :
  term FStar_Pervasives_Native.option -> term -> term -> term) =
  fun f ->
    fun v ->
      fun t ->
        match f with
        | FStar_Pervasives_Native.None -> mk_HasType v t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v t
let (mk_NoHoist : term -> term -> term) =
  fun dummy -> fun b -> mkApp ("NoHoist", [dummy; b]) b.rng
let (mk_Destruct : term -> FStar_Range.range -> term) =
  fun v -> mkApp ("Destruct", [v])
let (mk_Rank : term -> FStar_Range.range -> term) =
  fun x -> mkApp ("Rank", [x])
let (mk_tester : Prims.string -> term -> term) =
  fun n -> fun t -> mkApp ((Prims.op_Hat "is-" n), [t]) t.rng
let (mk_ApplyTF : term -> term -> term) =
  fun t -> fun t' -> mkApp ("ApplyTF", [t; t']) t.rng
let (mk_ApplyTT : term -> term -> FStar_Range.range -> term) =
  fun t -> fun t' -> fun r -> mkApp ("ApplyTT", [t; t']) r
let (kick_partial_app : term -> term) =
  fun t ->
    let uu____7145 =
      let uu____7146 = mkApp ("__uu__PartialApp", []) t.rng in
      mk_ApplyTT uu____7146 t t.rng in
    FStar_All.pipe_right uu____7145 mk_Valid
let (mk_String_const : Prims.string -> FStar_Range.range -> term) =
  fun s ->
    fun r ->
      let uu____7159 =
        let uu____7166 = let uu____7169 = mk (String s) r in [uu____7169] in
        ("FString_const", uu____7166) in
      mkApp uu____7159 r
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1 ->
    fun x2 ->
      fun x3 ->
        fun x4 ->
          fun r ->
            let uu____7197 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r in
            FStar_All.pipe_right uu____7197 mk_Valid
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1 -> fun x2 -> fun x3 -> fun r -> mkApp ("LexCons", [x1; x2; x3]) r
let rec (n_fuel : Prims.int -> term) =
  fun n ->
    if n = Prims.int_zero
    then mkApp ("ZFuel", []) norng
    else
      (let uu____7230 =
         let uu____7237 =
           let uu____7240 = n_fuel (n - Prims.int_one) in [uu____7240] in
         ("SFuel", uu____7237) in
       mkApp uu____7230 norng)
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
            let uu____7280 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____7280
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
      let uu____7341 = mkTrue r in
      FStar_List.fold_right (fun p1 -> fun p2 -> mkAnd (p1, p2) r) l
        uu____7341
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l ->
    fun r ->
      let uu____7360 = mkFalse r in
      FStar_List.fold_right (fun p1 -> fun p2 -> mkOr (p1, p2) r) l
        uu____7360
let (mk_haseq : term -> term) =
  fun t ->
    let uu____7370 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____7370
let (dummy_sort : sort) = Sort "Dummy_sort"