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
    match projectee with | Bool_sort  -> true | uu____47319 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47330 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47341 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47352 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47363 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47376 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47403 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47439 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47472 -> false
  
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
        let uu____47500 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47500
    | Array (s1,s2) ->
        let uu____47505 = strSort s1  in
        let uu____47507 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47505 uu____47507
    | Arrow (s1,s2) ->
        let uu____47512 = strSort s1  in
        let uu____47514 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47512 uu____47514
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
    match projectee with | TrueOp  -> true | uu____47546 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47557 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47568 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47579 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47590 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47601 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47612 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47623 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47634 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47645 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47656 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47667 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47678 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47689 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47700 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47711 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47722 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47733 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47744 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47755 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47766 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47777 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47788 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47799 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47810 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47821 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47832 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47843 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47854 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47865 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47878 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47902 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____47924 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____47935 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____47948 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____47970 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____47981 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48141 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48165 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48189 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48220 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48270 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48327 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48410 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48455 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48501 -> false
  
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
    match projectee with | Name _0 -> true | uu____48725 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48745 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48766 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____48956 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____48979 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49045 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49104 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49125 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49155 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49196 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49217 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49243 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49271 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49282 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49293 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49304 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49322 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49359 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49370 -> false
  
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
          let uu____49544 =
            let uu____49545 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49571 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49545
            }  in
          [uu____49544]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49585 =
      let uu____49586 =
        FStar_List.collect
          (fun uu___402_49593  ->
             match uu___402_49593 with
             | Assume a -> [a.assumption_name]
             | uu____49600 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49586
      }  in
    [uu____49585]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49637  -> match uu____49637 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49657 = x  in
    match uu____49657 with | (nm,uu____49660,uu____49661) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49672 = x  in
    match uu____49672 with | (uu____49673,sort,uu____49675) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49687 = x  in
    match uu____49687 with | (uu____49689,uu____49690,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49708 = fv_name x  in
      let uu____49710 = fv_name y  in uu____49708 = uu____49710
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49744 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49755  ->
    match uu___403_49755 with
    | { tm = FreeV x; freevars = uu____49757; rng = uu____49758;_} ->
        fv_sort x
    | uu____49779 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49786  ->
    match uu___404_49786 with
    | { tm = FreeV fv; freevars = uu____49788; rng = uu____49789;_} -> fv
    | uu____49810 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49838 -> []
    | Real uu____49848 -> []
    | BoundV uu____49858 -> []
    | FreeV fv -> [fv]
    | App (uu____49893,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49907,uu____49908,uu____49909,uu____49910,t1) ->
        freevars t1
    | Labeled (t1,uu____49931,uu____49932) -> freevars t1
    | LblPos (t1,uu____49936) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____49959 = FStar_ST.op_Bang t.freevars  in
    match uu____49959 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50057 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50057  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50136  ->
    match uu___405_50136 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50146  ->
    match uu___406_50146 with
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
        let uu____50182 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50182
    | NatToBv n1 ->
        let uu____50187 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50187
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50201  ->
    match uu___407_50201 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50211 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50211
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50233 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50233
    | FreeV x ->
        let uu____50245 = fv_name x  in
        let uu____50247 =
          let uu____50249 =
            let uu____50251 = fv_sort x  in strSort uu____50251  in
          Prims.op_Hat ":" uu____50249  in
        Prims.op_Hat uu____50245 uu____50247
    | App (op,tms) ->
        let uu____50259 =
          let uu____50261 = op_to_string op  in
          let uu____50263 =
            let uu____50265 =
              let uu____50267 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50267 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50265 ")"  in
          Prims.op_Hat uu____50261 uu____50263  in
        Prims.op_Hat "(" uu____50259
    | Labeled (t1,r1,r2) ->
        let uu____50284 = hash_of_term t1  in
        let uu____50286 =
          let uu____50288 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50288  in
        Prims.op_Hat uu____50284 uu____50286
    | LblPos (t1,r) ->
        let uu____50294 =
          let uu____50296 = hash_of_term t1  in
          Prims.op_Hat uu____50296
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50294
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50324 =
          let uu____50326 =
            let uu____50328 =
              let uu____50330 =
                let uu____50332 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50332 (FStar_String.concat " ")
                 in
              let uu____50342 =
                let uu____50344 =
                  let uu____50346 = hash_of_term body  in
                  let uu____50348 =
                    let uu____50350 =
                      let uu____50352 = weightToSmt wopt  in
                      let uu____50354 =
                        let uu____50356 =
                          let uu____50358 =
                            let uu____50360 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50379 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50379
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50360
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50358 "))"  in
                        Prims.op_Hat " " uu____50356  in
                      Prims.op_Hat uu____50352 uu____50354  in
                    Prims.op_Hat " " uu____50350  in
                  Prims.op_Hat uu____50346 uu____50348  in
                Prims.op_Hat ")(! " uu____50344  in
              Prims.op_Hat uu____50330 uu____50342  in
            Prims.op_Hat " (" uu____50328  in
          Prims.op_Hat (qop_to_string qop) uu____50326  in
        Prims.op_Hat "(" uu____50324
    | Let (es,body) ->
        let uu____50406 =
          let uu____50408 =
            let uu____50410 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50410 (FStar_String.concat " ")  in
          let uu____50420 =
            let uu____50422 =
              let uu____50424 = hash_of_term body  in
              Prims.op_Hat uu____50424 ")"  in
            Prims.op_Hat ") " uu____50422  in
          Prims.op_Hat uu____50408 uu____50420  in
        Prims.op_Hat "(let (" uu____50406

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50485 =
      let uu____50487 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50487  in
    mkBoxFunctions uu____50485
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50512 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50512 = "Box") &&
        (let uu____50519 =
           let uu____50521 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50521  in
         Prims.op_Negation uu____50519)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50545 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50545; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50631 =
        let uu____50632 = FStar_Util.ensure_decimal i  in Integer uu____50632
         in
      mk uu____50631 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50647 = FStar_Util.string_of_int i  in
      mkInteger uu____50647 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50725  ->
    fun r  -> match uu____50725 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50755) -> mkFalse r
      | App (FalseOp ,uu____50760) -> mkTrue r
      | uu____50765 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50781  ->
    fun r  ->
      match uu____50781 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50789),uu____50790) -> t2
           | (uu____50795,App (TrueOp ,uu____50796)) -> t1
           | (App (FalseOp ,uu____50801),uu____50802) -> mkFalse r
           | (uu____50807,App (FalseOp ,uu____50808)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50825,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50834) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50841 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50861  ->
    fun r  ->
      match uu____50861 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50869),uu____50870) -> mkTrue r
           | (uu____50875,App (TrueOp ,uu____50876)) -> mkTrue r
           | (App (FalseOp ,uu____50881),uu____50882) -> t2
           | (uu____50887,App (FalseOp ,uu____50888)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50905,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50914) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____50921 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____50941  ->
    fun r  ->
      match uu____50941 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____50949,App (TrueOp ,uu____50950)) -> mkTrue r
           | (App (FalseOp ,uu____50955),uu____50956) -> mkTrue r
           | (App (TrueOp ,uu____50961),uu____50962) -> t2
           | (uu____50967,App (Imp ,t1'::t2'::[])) ->
               let uu____50972 =
                 let uu____50979 =
                   let uu____50982 = mkAnd (t1, t1') r  in [uu____50982; t2']
                    in
                 (Imp, uu____50979)  in
               mkApp' uu____50972 r
           | uu____50985 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51010  ->
      fun r  -> match uu____51010 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51170  ->
      fun r  ->
        match uu____51170 with
        | (t1,t2) ->
            let uu____51179 =
              let uu____51186 =
                let uu____51189 =
                  let uu____51192 = mkNatToBv sz t2 r  in [uu____51192]  in
                t1 :: uu____51189  in
              (BvShl, uu____51186)  in
            mkApp' uu____51179 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51214  ->
      fun r  ->
        match uu____51214 with
        | (t1,t2) ->
            let uu____51223 =
              let uu____51230 =
                let uu____51233 =
                  let uu____51236 = mkNatToBv sz t2 r  in [uu____51236]  in
                t1 :: uu____51233  in
              (BvShr, uu____51230)  in
            mkApp' uu____51223 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51258  ->
      fun r  ->
        match uu____51258 with
        | (t1,t2) ->
            let uu____51267 =
              let uu____51274 =
                let uu____51277 =
                  let uu____51280 = mkNatToBv sz t2 r  in [uu____51280]  in
                t1 :: uu____51277  in
              (BvUdiv, uu____51274)  in
            mkApp' uu____51267 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51302  ->
      fun r  ->
        match uu____51302 with
        | (t1,t2) ->
            let uu____51311 =
              let uu____51318 =
                let uu____51321 =
                  let uu____51324 = mkNatToBv sz t2 r  in [uu____51324]  in
                t1 :: uu____51321  in
              (BvMod, uu____51318)  in
            mkApp' uu____51311 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51346  ->
      fun r  ->
        match uu____51346 with
        | (t1,t2) ->
            let uu____51355 =
              let uu____51362 =
                let uu____51365 =
                  let uu____51368 = mkNatToBv sz t2 r  in [uu____51368]  in
                t1 :: uu____51365  in
              (BvMul, uu____51362)  in
            mkApp' uu____51355 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51410  ->
    fun r  ->
      match uu____51410 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51429 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51594  ->
    fun r  ->
      match uu____51594 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51605) -> t2
           | App (FalseOp ,uu____51610) -> t3
           | uu____51615 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51616),App (TrueOp ,uu____51617)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51626),uu____51627) ->
                    let uu____51632 =
                      let uu____51637 = mkNot t1 t1.rng  in (uu____51637, t3)
                       in
                    mkImp uu____51632 r
                | (uu____51638,App (TrueOp ,uu____51639)) -> mkImp (t1, t2) r
                | (uu____51644,uu____51645) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51701 -> FStar_Pervasives_Native.None
      | Real uu____51703 -> FStar_Pervasives_Native.None
      | BoundV uu____51705 -> FStar_Pervasives_Native.None
      | FreeV uu____51707 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51731 -> true
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
            | BvUext uu____51764 -> false
            | NatToBv uu____51767 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51778,uu____51779) -> aux t2
      | Quant uu____51782 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51802 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51817 = aux t1  in
          (match uu____51817 with
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
        let uu____51855 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51855
    | FreeV fv ->
        let uu____51867 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51867
    | App (op,l) ->
        let uu____51876 = op_to_string op  in
        let uu____51878 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51876 uu____51878
    | Labeled (t1,r1,r2) ->
        let uu____51886 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51886
    | LblPos (t1,s) ->
        let uu____51893 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51893
    | Quant (qop,l,uu____51898,uu____51899,t1) ->
        let uu____51919 = print_smt_term_list_list l  in
        let uu____51921 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51919
          uu____51921
    | Let (es,body) ->
        let uu____51930 = print_smt_term_list es  in
        let uu____51932 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____51930 uu____51932

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____51939 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____51939 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____51966 =
             let uu____51968 =
               let uu____51970 = print_smt_term_list l1  in
               Prims.op_Hat uu____51970 " ] "  in
             Prims.op_Hat "; [ " uu____51968  in
           Prims.op_Hat s uu____51966) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52010  ->
        match uu____52010 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52079 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52079 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52094 =
                         let uu____52100 =
                           let uu____52102 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52102
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____52100)
                          in
                       FStar_Errors.log_issue r uu____52094);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52113) -> body
               | uu____52118 ->
                   let uu____52119 =
                     let uu____52120 =
                       let uu____52140 = all_pats_ok pats  in
                       (qop, uu____52140, wopt, vars, body)  in
                     Quant uu____52120  in
                   mk uu____52119 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52169  ->
    fun r  ->
      match uu____52169 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52215 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52215 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52248 = FStar_ST.op_Bang t1.freevars  in
        match uu____52248 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52322 ->
            (match t1.tm with
             | Integer uu____52335 -> t1
             | Real uu____52337 -> t1
             | BoundV uu____52339 -> t1
             | FreeV x ->
                 let uu____52350 = index_of1 x  in
                 (match uu____52350 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52364 =
                   let uu____52371 = FStar_List.map (aux ix) tms  in
                   (op, uu____52371)  in
                 mkApp' uu____52364 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52381 =
                   let uu____52382 =
                     let uu____52390 = aux ix t2  in (uu____52390, r1, r2)
                      in
                   Labeled uu____52382  in
                 mk uu____52381 t2.rng
             | LblPos (t2,r) ->
                 let uu____52396 =
                   let uu____52397 =
                     let uu____52403 = aux ix t2  in (uu____52403, r)  in
                   LblPos uu____52397  in
                 mk uu____52396 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52429 =
                   let uu____52449 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52470 = aux (ix + n1) body  in
                   (qop, uu____52449, wopt, vars, uu____52470)  in
                 mkQuant t1.rng false uu____52429
             | Let (es,body) ->
                 let uu____52491 =
                   FStar_List.fold_left
                     (fun uu____52511  ->
                        fun e  ->
                          match uu____52511 with
                          | (ix1,l) ->
                              let uu____52535 =
                                let uu____52538 = aux ix1 e  in uu____52538
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52535))
                     (ix, []) es
                    in
                 (match uu____52491 with
                  | (ix1,es_rev) ->
                      let uu____52554 =
                        let uu____52561 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52561)  in
                      mkLet uu____52554 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52597 -> t1
        | Real uu____52599 -> t1
        | FreeV uu____52601 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52626 =
              let uu____52633 = FStar_List.map (aux shift) tms2  in
              (op, uu____52633)  in
            mkApp' uu____52626 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52643 =
              let uu____52644 =
                let uu____52652 = aux shift t2  in (uu____52652, r1, r2)  in
              Labeled uu____52644  in
            mk uu____52643 t2.rng
        | LblPos (t2,r) ->
            let uu____52658 =
              let uu____52659 =
                let uu____52665 = aux shift t2  in (uu____52665, r)  in
              LblPos uu____52659  in
            mk uu____52658 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52697 =
              let uu____52717 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52734 = aux shift1 body  in
              (qop, uu____52717, wopt, vars, uu____52734)  in
            mkQuant t1.rng false uu____52697
        | Let (es,body) ->
            let uu____52751 =
              FStar_List.fold_left
                (fun uu____52771  ->
                   fun e  ->
                     match uu____52771 with
                     | (ix,es1) ->
                         let uu____52795 =
                           let uu____52798 = aux shift e  in uu____52798 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52795))
                (shift, []) es
               in
            (match uu____52751 with
             | (shift1,es_rev) ->
                 let uu____52814 =
                   let uu____52821 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52821)  in
                 mkLet uu____52814 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52841 = abstr [fv] t  in inst [s] uu____52841
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52871  ->
      match uu____52871 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52914 =
            let uu____52934 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____52951 = FStar_List.map fv_sort vars  in
            let uu____52954 = abstr vars body  in
            (qop, uu____52934, wopt, uu____52951, uu____52954)  in
          mkQuant r true uu____52914
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____52985  ->
      match uu____52985 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53044  ->
      match uu____53044 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53119  ->
      match uu____53119 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53182  ->
      match uu____53182 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53233  ->
    fun r  ->
      match uu____53233 with
      | (bindings,body) ->
          let uu____53259 = FStar_List.split bindings  in
          (match uu____53259 with
           | (vars,es) ->
               let uu____53278 =
                 let uu____53285 = abstr vars body  in (es, uu____53285)  in
               mkLet uu____53278 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53307  ->
    match uu____53307 with
    | (nm,vars,s,tm,c) ->
        let uu____53332 =
          let uu____53346 = FStar_List.map fv_sort vars  in
          let uu____53349 = abstr vars tm  in
          (nm, uu____53346, s, uu____53349, c)  in
        DefineFun uu____53332
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53360 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53360
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53378  ->
    fun id1  ->
      match uu____53378 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53394 =
              let uu____53395 =
                let uu____53400 = mkInteger' id1 norng  in
                let uu____53401 =
                  let uu____53402 =
                    let uu____53410 = constr_id_of_sort sort  in
                    let uu____53412 =
                      let uu____53415 = mkApp (tok_name, []) norng  in
                      [uu____53415]  in
                    (uu____53410, uu____53412)  in
                  mkApp uu____53402 norng  in
                (uu____53400, uu____53401)  in
              mkEq uu____53395 norng  in
            let uu____53422 = escape a_name  in
            {
              assumption_term = uu____53394;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53422;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53448  ->
      match uu____53448 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53488 =
                        let uu____53489 =
                          let uu____53495 =
                            let uu____53497 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53497  in
                          (uu____53495, s)  in
                        mk_fv uu____53489  in
                      mkFreeV uu____53488 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53525 =
              let uu____53533 = constr_id_of_sort sort  in
              (uu____53533, [capp])  in
            mkApp uu____53525 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53542 =
              let uu____53543 =
                let uu____53554 =
                  let uu____53555 =
                    let uu____53560 = mkInteger id2 norng  in
                    (uu____53560, cid_app)  in
                  mkEq uu____53555 norng  in
                ([[capp]], bvar_names, uu____53554)  in
              mkForall rng uu____53543  in
            let uu____53569 = escape a_name  in
            {
              assumption_term = uu____53542;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53569;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53594  ->
      match uu____53594 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53627 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53627  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53662 =
              let uu____53663 =
                let uu____53669 = bvar_name i  in (uu____53669, s)  in
              mk_fv uu____53663  in
            FStar_All.pipe_left mkFreeV uu____53662  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53705  ->
                      match uu____53705 with
                      | (uu____53715,s,uu____53717) ->
                          let uu____53722 = bvar i s  in uu____53722 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53750 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53788  ->
                      match uu____53788 with
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
                              let uu____53821 =
                                let uu____53822 =
                                  let uu____53833 =
                                    let uu____53834 =
                                      let uu____53839 =
                                        let uu____53840 = bvar i s  in
                                        uu____53840 norng  in
                                      (cproj_app, uu____53839)  in
                                    mkEq uu____53834 norng  in
                                  ([[capp]], bvar_names, uu____53833)  in
                                mkForall rng uu____53822  in
                              let uu____53853 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53821;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53853;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53750 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53878  ->
      match uu____53878 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____53926  ->
                    match uu____53926 with
                    | (uu____53935,sort1,uu____53937) -> sort1))
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
              let uu____53962 =
                let uu____53967 =
                  let uu____53968 =
                    let uu____53976 = constr_id_of_sort sort  in
                    (uu____53976, [xx])  in
                  mkApp uu____53968 norng  in
                let uu____53981 =
                  let uu____53982 = FStar_Util.string_of_int id1  in
                  mkInteger uu____53982 norng  in
                (uu____53967, uu____53981)  in
              mkEq uu____53962 norng  in
            let uu____53984 =
              let uu____54003 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54067  ->
                          match uu____54067 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54097 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54097, [])
                              else
                                (let fi =
                                   let uu____54106 =
                                     let uu____54112 =
                                       let uu____54114 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54114  in
                                     (uu____54112, s)  in
                                   mk_fv uu____54106  in
                                 let uu____54118 = mkFreeV fi norng  in
                                 (uu____54118, [fi]))))
                 in
              FStar_All.pipe_right uu____54003 FStar_List.split  in
            match uu____53984 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54215 =
                    let uu____54220 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54220)  in
                  mkEq uu____54215 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54233 ->
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
          let uu____54268 =
            let uu____54271 =
              let uu____54272 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54272  in
            uu____54271 :: cdecl :: cid :: projs  in
          let uu____54275 =
            let uu____54278 =
              let uu____54281 =
                let uu____54282 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54282  in
              [uu____54281]  in
            FStar_List.append [disc] uu____54278  in
          FStar_List.append uu____54268 uu____54275
  
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
          let uu____54334 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54383  ->
                    fun s  ->
                      match uu____54383 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54428 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54439 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54439  in
                          let names2 =
                            let uu____54444 = mk_fv (nm, s)  in uu____54444
                              :: names1
                             in
                          let b =
                            let uu____54448 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54448  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54334 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54519 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54519 with
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
              (let uu____54683 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54683)
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
                               "Prims.guard_free",{ tm = BoundV uu____54729;
                                                    freevars = uu____54730;
                                                    rng = uu____54731;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54752 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54830 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54830 fv_name
          | FreeV x when fv_force x ->
              let uu____54841 =
                let uu____54843 = fv_name x  in
                Prims.op_Hat uu____54843 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54841
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54865 = op_to_string op  in
              let uu____54867 =
                let uu____54869 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54869 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54865 uu____54867
          | Labeled (t2,uu____54881,uu____54882) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54889 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54889 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54917 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54917 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____54970 ->
                         let uu____54975 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____54994 =
                                     let uu____54996 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55004 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55004) pats2
                                        in
                                     FStar_String.concat " " uu____54996  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____54994))
                            in
                         FStar_All.pipe_right uu____54975
                           (FStar_String.concat "\n")
                      in
                   let uu____55014 =
                     let uu____55018 =
                       let uu____55022 =
                         let uu____55026 = aux1 n2 names2 body  in
                         let uu____55028 =
                           let uu____55032 = weightToSmt wopt  in
                           [uu____55032; pats_str; qid]  in
                         uu____55026 :: uu____55028  in
                       binders1 :: uu____55022  in
                     (qop_to_string qop) :: uu____55018  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55014)
          | Let (es,body) ->
              let uu____55048 =
                FStar_List.fold_left
                  (fun uu____55081  ->
                     fun e  ->
                       match uu____55081 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55124 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55124  in
                           let names01 =
                             let uu____55130 = mk_fv (nm, Term_sort)  in
                             uu____55130 :: names0  in
                           let b =
                             let uu____55134 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55134  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55048 with
               | (names2,binders,n2) ->
                   let uu____55168 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55168)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55184 = FStar_Range.string_of_range t1.rng  in
            let uu____55186 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55184
              uu____55186 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55208  ->
      match uu___408_55208 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55219 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55219 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55241 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55316 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55316 (FStar_String.concat "\n")  in
            let uu____55326 = FStar_Options.keep_query_captions ()  in
            if uu____55326
            then
              let uu____55330 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55332 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55330 uu____55332
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55341 =
                let uu____55343 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55343 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55341
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55384 = caption_to_string print_captions c  in
            let uu____55386 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55384 f
              (FStar_String.concat " " l) uu____55386
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55401 = name_macro_binders arg_sorts  in
            (match uu____55401 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55425 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55425 body  in
                 let uu____55430 = caption_to_string print_captions c  in
                 let uu____55432 = strSort retsort  in
                 let uu____55434 =
                   let uu____55436 = escape f  in
                   termToSmt print_captions uu____55436 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55430 f (FStar_String.concat " " binders)
                   uu____55432 uu____55434)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55463  ->
                      match uu___409_55463 with
                      | Name n1 ->
                          let uu____55466 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55466
                      | Namespace ns ->
                          let uu____55470 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55470
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55480 =
                  let uu____55482 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55482  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55480
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55493 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55495 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55493
              fids uu____55495 n1
        | Eval t ->
            let uu____55499 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55499
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55506 -> ""
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
      let uu____55527 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55527 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55538 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55538 (FStar_String.concat "\n")

and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options  ->
    let basic =
      Prims.op_Hat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (iff (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))"
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
      let uu____55673 =
        let uu____55677 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55677
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55673 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55708 =
      let uu____55709 =
        let uu____55711 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55711  in
      let uu____55720 =
        let uu____55723 =
          let uu____55724 =
            let uu____55726 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55726  in
          (uu____55724, (BitVec_sort sz), true)  in
        [uu____55723]  in
      (uu____55709, uu____55720, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55708 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55769  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55794 =
       let uu____55796 = FStar_ST.op_Bang __range_c  in
       uu____55796 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55794);
    (let uu____55841 =
       let uu____55849 =
         let uu____55852 = mkInteger' i norng  in [uu____55852]  in
       ("Range_const", uu____55849)  in
     mkApp uu____55841 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55895 =
        let uu____55903 =
          let uu____55906 = mkInteger' i norng  in [uu____55906]  in
        ("Tm_uvar", uu____55903)  in
      mkApp uu____55895 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____55949 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____55973 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____55973 u v1 t
  
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
      let uu____56068 =
        let uu____56070 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56070  in
      let uu____56079 =
        let uu____56081 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56081  in
      elim_box true uu____56068 uu____56079 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56104 =
        let uu____56106 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56106  in
      let uu____56115 =
        let uu____56117 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56117  in
      elim_box true uu____56104 uu____56115 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56141 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56156 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56182 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56182
         | uu____56185 -> FStar_Pervasives_Native.None)
    | uu____56187 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56205::t1::t2::[]);
                       freevars = uu____56208; rng = uu____56209;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56228::t1::t2::[]);
                       freevars = uu____56231; rng = uu____56232;_}::[])
        -> let uu____56251 = mkEq (t1, t2) norng  in mkNot uu____56251 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56254; rng = uu____56255;_}::[])
        ->
        let uu____56274 =
          let uu____56279 = unboxInt t1  in
          let uu____56280 = unboxInt t2  in (uu____56279, uu____56280)  in
        mkLTE uu____56274 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56283; rng = uu____56284;_}::[])
        ->
        let uu____56303 =
          let uu____56308 = unboxInt t1  in
          let uu____56309 = unboxInt t2  in (uu____56308, uu____56309)  in
        mkLT uu____56303 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56312; rng = uu____56313;_}::[])
        ->
        let uu____56332 =
          let uu____56337 = unboxInt t1  in
          let uu____56338 = unboxInt t2  in (uu____56337, uu____56338)  in
        mkGTE uu____56332 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56341; rng = uu____56342;_}::[])
        ->
        let uu____56361 =
          let uu____56366 = unboxInt t1  in
          let uu____56367 = unboxInt t2  in (uu____56366, uu____56367)  in
        mkGT uu____56361 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56370; rng = uu____56371;_}::[])
        ->
        let uu____56390 =
          let uu____56395 = unboxBool t1  in
          let uu____56396 = unboxBool t2  in (uu____56395, uu____56396)  in
        mkAnd uu____56390 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56399; rng = uu____56400;_}::[])
        ->
        let uu____56419 =
          let uu____56424 = unboxBool t1  in
          let uu____56425 = unboxBool t2  in (uu____56424, uu____56425)  in
        mkOr uu____56419 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56427; rng = uu____56428;_}::[])
        -> let uu____56447 = unboxBool t1  in mkNot uu____56447 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56451; rng = uu____56452;_}::[])
        when
        let uu____56471 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56471 ->
        let sz =
          let uu____56478 = getBoxedInteger t0  in
          match uu____56478 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56486 -> failwith "impossible"  in
        let uu____56492 =
          let uu____56497 = unboxBitVec sz t1  in
          let uu____56498 = unboxBitVec sz t2  in (uu____56497, uu____56498)
           in
        mkBvUlt uu____56492 t.rng
    | App
        (Var
         "Prims.equals",uu____56499::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56503;
                                       rng = uu____56504;_}::uu____56505::[])
        when
        let uu____56524 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56524 ->
        let sz =
          let uu____56531 = getBoxedInteger t0  in
          match uu____56531 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56539 -> failwith "impossible"  in
        let uu____56545 =
          let uu____56550 = unboxBitVec sz t1  in
          let uu____56551 = unboxBitVec sz t2  in (uu____56550, uu____56551)
           in
        mkBvUlt uu____56545 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56556 = unboxBool t1  in
        {
          tm = (uu___1789_56556.tm);
          freevars = (uu___1789_56556.freevars);
          rng = (t.rng)
        }
    | uu____56557 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56618 = FStar_Options.unthrottle_inductives ()  in
        if uu____56618
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
    let uu____56751 =
      let uu____56752 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56752 t t.rng  in
    FStar_All.pipe_right uu____56751 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56770 =
        let uu____56778 =
          let uu____56781 = mkInteger' i norng  in [uu____56781]  in
        ("FString_const", uu____56778)  in
      mkApp uu____56770 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56812 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56812 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56859 =
         let uu____56867 =
           let uu____56870 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56870]  in
         ("SFuel", uu____56867)  in
       mkApp uu____56859 norng)
  
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
            let uu____56918 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56918
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
      let uu____56981 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____56981
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57001 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57001
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57012 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57012
  
let (dummy_sort : sort) = Sort "Dummy_sort" 