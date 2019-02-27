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
    match projectee with | Bool_sort  -> true | uu____47324 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47335 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47346 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47357 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47368 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47381 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47408 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47444 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47477 -> false
  
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
        let uu____47505 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47505
    | Array (s1,s2) ->
        let uu____47510 = strSort s1  in
        let uu____47512 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47510 uu____47512
    | Arrow (s1,s2) ->
        let uu____47517 = strSort s1  in
        let uu____47519 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47517 uu____47519
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
    match projectee with | TrueOp  -> true | uu____47551 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47562 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47573 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47584 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47595 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47606 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47617 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47628 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47639 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47650 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47661 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47672 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47683 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47694 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47705 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47716 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47727 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47738 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47749 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47760 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47771 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47782 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47793 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47804 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47815 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47826 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47837 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47848 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47859 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47870 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47883 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47907 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____47929 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____47940 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____47953 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____47975 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____47986 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48146 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48170 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48194 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48225 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48275 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48332 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48415 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48460 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48506 -> false
  
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
    match projectee with | Name _0 -> true | uu____48730 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48750 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48771 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____48961 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____48984 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49050 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49109 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49130 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49160 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49201 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49222 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49248 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49276 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49287 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49298 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49309 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49327 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49364 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49375 -> false
  
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
          let uu____49549 =
            let uu____49550 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49576 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49550
            }  in
          [uu____49549]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49590 =
      let uu____49591 =
        FStar_List.collect
          (fun uu___402_49598  ->
             match uu___402_49598 with
             | Assume a -> [a.assumption_name]
             | uu____49605 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49591
      }  in
    [uu____49590]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49642  -> match uu____49642 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49662 = x  in
    match uu____49662 with | (nm,uu____49665,uu____49666) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49677 = x  in
    match uu____49677 with | (uu____49678,sort,uu____49680) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49692 = x  in
    match uu____49692 with | (uu____49694,uu____49695,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49713 = fv_name x  in
      let uu____49715 = fv_name y  in uu____49713 = uu____49715
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49749 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49760  ->
    match uu___403_49760 with
    | { tm = FreeV x; freevars = uu____49762; rng = uu____49763;_} ->
        fv_sort x
    | uu____49784 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49791  ->
    match uu___404_49791 with
    | { tm = FreeV fv; freevars = uu____49793; rng = uu____49794;_} -> fv
    | uu____49815 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49843 -> []
    | Real uu____49853 -> []
    | BoundV uu____49863 -> []
    | FreeV fv -> [fv]
    | App (uu____49898,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49912,uu____49913,uu____49914,uu____49915,t1) ->
        freevars t1
    | Labeled (t1,uu____49936,uu____49937) -> freevars t1
    | LblPos (t1,uu____49941) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____49964 = FStar_ST.op_Bang t.freevars  in
    match uu____49964 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50062 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50062  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50141  ->
    match uu___405_50141 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50151  ->
    match uu___406_50151 with
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
        let uu____50187 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50187
    | NatToBv n1 ->
        let uu____50192 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50192
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50206  ->
    match uu___407_50206 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50216 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50216
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50238 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50238
    | FreeV x ->
        let uu____50250 = fv_name x  in
        let uu____50252 =
          let uu____50254 =
            let uu____50256 = fv_sort x  in strSort uu____50256  in
          Prims.op_Hat ":" uu____50254  in
        Prims.op_Hat uu____50250 uu____50252
    | App (op,tms) ->
        let uu____50264 =
          let uu____50266 = op_to_string op  in
          let uu____50268 =
            let uu____50270 =
              let uu____50272 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50272 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50270 ")"  in
          Prims.op_Hat uu____50266 uu____50268  in
        Prims.op_Hat "(" uu____50264
    | Labeled (t1,r1,r2) ->
        let uu____50289 = hash_of_term t1  in
        let uu____50291 =
          let uu____50293 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50293  in
        Prims.op_Hat uu____50289 uu____50291
    | LblPos (t1,r) ->
        let uu____50299 =
          let uu____50301 = hash_of_term t1  in
          Prims.op_Hat uu____50301
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50299
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50329 =
          let uu____50331 =
            let uu____50333 =
              let uu____50335 =
                let uu____50337 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50337 (FStar_String.concat " ")
                 in
              let uu____50347 =
                let uu____50349 =
                  let uu____50351 = hash_of_term body  in
                  let uu____50353 =
                    let uu____50355 =
                      let uu____50357 = weightToSmt wopt  in
                      let uu____50359 =
                        let uu____50361 =
                          let uu____50363 =
                            let uu____50365 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50384 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50384
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50365
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50363 "))"  in
                        Prims.op_Hat " " uu____50361  in
                      Prims.op_Hat uu____50357 uu____50359  in
                    Prims.op_Hat " " uu____50355  in
                  Prims.op_Hat uu____50351 uu____50353  in
                Prims.op_Hat ")(! " uu____50349  in
              Prims.op_Hat uu____50335 uu____50347  in
            Prims.op_Hat " (" uu____50333  in
          Prims.op_Hat (qop_to_string qop) uu____50331  in
        Prims.op_Hat "(" uu____50329
    | Let (es,body) ->
        let uu____50411 =
          let uu____50413 =
            let uu____50415 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50415 (FStar_String.concat " ")  in
          let uu____50425 =
            let uu____50427 =
              let uu____50429 = hash_of_term body  in
              Prims.op_Hat uu____50429 ")"  in
            Prims.op_Hat ") " uu____50427  in
          Prims.op_Hat uu____50413 uu____50425  in
        Prims.op_Hat "(let (" uu____50411

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50490 =
      let uu____50492 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50492  in
    mkBoxFunctions uu____50490
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50517 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50517 = "Box") &&
        (let uu____50524 =
           let uu____50526 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50526  in
         Prims.op_Negation uu____50524)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50550 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50550; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50636 =
        let uu____50637 = FStar_Util.ensure_decimal i  in Integer uu____50637
         in
      mk uu____50636 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50652 = FStar_Util.string_of_int i  in
      mkInteger uu____50652 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50730  ->
    fun r  -> match uu____50730 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50760) -> mkFalse r
      | App (FalseOp ,uu____50765) -> mkTrue r
      | uu____50770 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50786  ->
    fun r  ->
      match uu____50786 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50794),uu____50795) -> t2
           | (uu____50800,App (TrueOp ,uu____50801)) -> t1
           | (App (FalseOp ,uu____50806),uu____50807) -> mkFalse r
           | (uu____50812,App (FalseOp ,uu____50813)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50830,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50839) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50846 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50866  ->
    fun r  ->
      match uu____50866 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50874),uu____50875) -> mkTrue r
           | (uu____50880,App (TrueOp ,uu____50881)) -> mkTrue r
           | (App (FalseOp ,uu____50886),uu____50887) -> t2
           | (uu____50892,App (FalseOp ,uu____50893)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50910,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50919) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____50926 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____50946  ->
    fun r  ->
      match uu____50946 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____50954,App (TrueOp ,uu____50955)) -> mkTrue r
           | (App (FalseOp ,uu____50960),uu____50961) -> mkTrue r
           | (App (TrueOp ,uu____50966),uu____50967) -> t2
           | (uu____50972,App (Imp ,t1'::t2'::[])) ->
               let uu____50977 =
                 let uu____50984 =
                   let uu____50987 = mkAnd (t1, t1') r  in [uu____50987; t2']
                    in
                 (Imp, uu____50984)  in
               mkApp' uu____50977 r
           | uu____50990 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51015  ->
      fun r  -> match uu____51015 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51175  ->
      fun r  ->
        match uu____51175 with
        | (t1,t2) ->
            let uu____51184 =
              let uu____51191 =
                let uu____51194 =
                  let uu____51197 = mkNatToBv sz t2 r  in [uu____51197]  in
                t1 :: uu____51194  in
              (BvShl, uu____51191)  in
            mkApp' uu____51184 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51219  ->
      fun r  ->
        match uu____51219 with
        | (t1,t2) ->
            let uu____51228 =
              let uu____51235 =
                let uu____51238 =
                  let uu____51241 = mkNatToBv sz t2 r  in [uu____51241]  in
                t1 :: uu____51238  in
              (BvShr, uu____51235)  in
            mkApp' uu____51228 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51263  ->
      fun r  ->
        match uu____51263 with
        | (t1,t2) ->
            let uu____51272 =
              let uu____51279 =
                let uu____51282 =
                  let uu____51285 = mkNatToBv sz t2 r  in [uu____51285]  in
                t1 :: uu____51282  in
              (BvUdiv, uu____51279)  in
            mkApp' uu____51272 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51307  ->
      fun r  ->
        match uu____51307 with
        | (t1,t2) ->
            let uu____51316 =
              let uu____51323 =
                let uu____51326 =
                  let uu____51329 = mkNatToBv sz t2 r  in [uu____51329]  in
                t1 :: uu____51326  in
              (BvMod, uu____51323)  in
            mkApp' uu____51316 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51351  ->
      fun r  ->
        match uu____51351 with
        | (t1,t2) ->
            let uu____51360 =
              let uu____51367 =
                let uu____51370 =
                  let uu____51373 = mkNatToBv sz t2 r  in [uu____51373]  in
                t1 :: uu____51370  in
              (BvMul, uu____51367)  in
            mkApp' uu____51360 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51415  ->
    fun r  ->
      match uu____51415 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51434 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51599  ->
    fun r  ->
      match uu____51599 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51610) -> t2
           | App (FalseOp ,uu____51615) -> t3
           | uu____51620 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51621),App (TrueOp ,uu____51622)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51631),uu____51632) ->
                    let uu____51637 =
                      let uu____51642 = mkNot t1 t1.rng  in (uu____51642, t3)
                       in
                    mkImp uu____51637 r
                | (uu____51643,App (TrueOp ,uu____51644)) -> mkImp (t1, t2) r
                | (uu____51649,uu____51650) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51706 -> FStar_Pervasives_Native.None
      | Real uu____51708 -> FStar_Pervasives_Native.None
      | BoundV uu____51710 -> FStar_Pervasives_Native.None
      | FreeV uu____51712 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51736 -> true
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
            | BvUext uu____51769 -> false
            | NatToBv uu____51772 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51783,uu____51784) -> aux t2
      | Quant uu____51787 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51807 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51822 = aux t1  in
          (match uu____51822 with
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
        let uu____51860 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51860
    | FreeV fv ->
        let uu____51872 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51872
    | App (op,l) ->
        let uu____51881 = op_to_string op  in
        let uu____51883 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51881 uu____51883
    | Labeled (t1,r1,r2) ->
        let uu____51891 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51891
    | LblPos (t1,s) ->
        let uu____51898 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51898
    | Quant (qop,l,uu____51903,uu____51904,t1) ->
        let uu____51924 = print_smt_term_list_list l  in
        let uu____51926 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51924
          uu____51926
    | Let (es,body) ->
        let uu____51935 = print_smt_term_list es  in
        let uu____51937 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____51935 uu____51937

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____51944 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____51944 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____51971 =
             let uu____51973 =
               let uu____51975 = print_smt_term_list l1  in
               Prims.op_Hat uu____51975 " ] "  in
             Prims.op_Hat "; [ " uu____51973  in
           Prims.op_Hat s uu____51971) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52015  ->
        match uu____52015 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52084 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52084 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52099 =
                         let uu____52105 =
                           let uu____52107 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52107
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____52105)
                          in
                       FStar_Errors.log_issue r uu____52099);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52118) -> body
               | uu____52123 ->
                   let uu____52124 =
                     let uu____52125 =
                       let uu____52145 = all_pats_ok pats  in
                       (qop, uu____52145, wopt, vars, body)  in
                     Quant uu____52125  in
                   mk uu____52124 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52174  ->
    fun r  ->
      match uu____52174 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52220 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52220 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52253 = FStar_ST.op_Bang t1.freevars  in
        match uu____52253 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52327 ->
            (match t1.tm with
             | Integer uu____52340 -> t1
             | Real uu____52342 -> t1
             | BoundV uu____52344 -> t1
             | FreeV x ->
                 let uu____52355 = index_of1 x  in
                 (match uu____52355 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52369 =
                   let uu____52376 = FStar_List.map (aux ix) tms  in
                   (op, uu____52376)  in
                 mkApp' uu____52369 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52386 =
                   let uu____52387 =
                     let uu____52395 = aux ix t2  in (uu____52395, r1, r2)
                      in
                   Labeled uu____52387  in
                 mk uu____52386 t2.rng
             | LblPos (t2,r) ->
                 let uu____52401 =
                   let uu____52402 =
                     let uu____52408 = aux ix t2  in (uu____52408, r)  in
                   LblPos uu____52402  in
                 mk uu____52401 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52434 =
                   let uu____52454 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52475 = aux (ix + n1) body  in
                   (qop, uu____52454, wopt, vars, uu____52475)  in
                 mkQuant t1.rng false uu____52434
             | Let (es,body) ->
                 let uu____52496 =
                   FStar_List.fold_left
                     (fun uu____52516  ->
                        fun e  ->
                          match uu____52516 with
                          | (ix1,l) ->
                              let uu____52540 =
                                let uu____52543 = aux ix1 e  in uu____52543
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52540))
                     (ix, []) es
                    in
                 (match uu____52496 with
                  | (ix1,es_rev) ->
                      let uu____52559 =
                        let uu____52566 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52566)  in
                      mkLet uu____52559 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52602 -> t1
        | Real uu____52604 -> t1
        | FreeV uu____52606 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52631 =
              let uu____52638 = FStar_List.map (aux shift) tms2  in
              (op, uu____52638)  in
            mkApp' uu____52631 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52648 =
              let uu____52649 =
                let uu____52657 = aux shift t2  in (uu____52657, r1, r2)  in
              Labeled uu____52649  in
            mk uu____52648 t2.rng
        | LblPos (t2,r) ->
            let uu____52663 =
              let uu____52664 =
                let uu____52670 = aux shift t2  in (uu____52670, r)  in
              LblPos uu____52664  in
            mk uu____52663 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52702 =
              let uu____52722 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52739 = aux shift1 body  in
              (qop, uu____52722, wopt, vars, uu____52739)  in
            mkQuant t1.rng false uu____52702
        | Let (es,body) ->
            let uu____52756 =
              FStar_List.fold_left
                (fun uu____52776  ->
                   fun e  ->
                     match uu____52776 with
                     | (ix,es1) ->
                         let uu____52800 =
                           let uu____52803 = aux shift e  in uu____52803 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52800))
                (shift, []) es
               in
            (match uu____52756 with
             | (shift1,es_rev) ->
                 let uu____52819 =
                   let uu____52826 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52826)  in
                 mkLet uu____52819 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52846 = abstr [fv] t  in inst [s] uu____52846
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52876  ->
      match uu____52876 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52919 =
            let uu____52939 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____52956 = FStar_List.map fv_sort vars  in
            let uu____52959 = abstr vars body  in
            (qop, uu____52939, wopt, uu____52956, uu____52959)  in
          mkQuant r true uu____52919
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____52990  ->
      match uu____52990 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53049  ->
      match uu____53049 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53124  ->
      match uu____53124 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53187  ->
      match uu____53187 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53238  ->
    fun r  ->
      match uu____53238 with
      | (bindings,body) ->
          let uu____53264 = FStar_List.split bindings  in
          (match uu____53264 with
           | (vars,es) ->
               let uu____53283 =
                 let uu____53290 = abstr vars body  in (es, uu____53290)  in
               mkLet uu____53283 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53312  ->
    match uu____53312 with
    | (nm,vars,s,tm,c) ->
        let uu____53337 =
          let uu____53351 = FStar_List.map fv_sort vars  in
          let uu____53354 = abstr vars tm  in
          (nm, uu____53351, s, uu____53354, c)  in
        DefineFun uu____53337
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53365 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53365
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53383  ->
    fun id1  ->
      match uu____53383 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53399 =
              let uu____53400 =
                let uu____53405 = mkInteger' id1 norng  in
                let uu____53406 =
                  let uu____53407 =
                    let uu____53415 = constr_id_of_sort sort  in
                    let uu____53417 =
                      let uu____53420 = mkApp (tok_name, []) norng  in
                      [uu____53420]  in
                    (uu____53415, uu____53417)  in
                  mkApp uu____53407 norng  in
                (uu____53405, uu____53406)  in
              mkEq uu____53400 norng  in
            let uu____53427 = escape a_name  in
            {
              assumption_term = uu____53399;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53427;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53453  ->
      match uu____53453 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53493 =
                        let uu____53494 =
                          let uu____53500 =
                            let uu____53502 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53502  in
                          (uu____53500, s)  in
                        mk_fv uu____53494  in
                      mkFreeV uu____53493 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53530 =
              let uu____53538 = constr_id_of_sort sort  in
              (uu____53538, [capp])  in
            mkApp uu____53530 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53547 =
              let uu____53548 =
                let uu____53559 =
                  let uu____53560 =
                    let uu____53565 = mkInteger id2 norng  in
                    (uu____53565, cid_app)  in
                  mkEq uu____53560 norng  in
                ([[capp]], bvar_names, uu____53559)  in
              mkForall rng uu____53548  in
            let uu____53574 = escape a_name  in
            {
              assumption_term = uu____53547;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53574;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53599  ->
      match uu____53599 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53632 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53632  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53667 =
              let uu____53668 =
                let uu____53674 = bvar_name i  in (uu____53674, s)  in
              mk_fv uu____53668  in
            FStar_All.pipe_left mkFreeV uu____53667  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53710  ->
                      match uu____53710 with
                      | (uu____53720,s,uu____53722) ->
                          let uu____53727 = bvar i s  in uu____53727 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53755 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53793  ->
                      match uu____53793 with
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
                              let uu____53826 =
                                let uu____53827 =
                                  let uu____53838 =
                                    let uu____53839 =
                                      let uu____53844 =
                                        let uu____53845 = bvar i s  in
                                        uu____53845 norng  in
                                      (cproj_app, uu____53844)  in
                                    mkEq uu____53839 norng  in
                                  ([[capp]], bvar_names, uu____53838)  in
                                mkForall rng uu____53827  in
                              let uu____53858 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53826;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53858;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53755 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53883  ->
      match uu____53883 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____53931  ->
                    match uu____53931 with
                    | (uu____53940,sort1,uu____53942) -> sort1))
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
              let uu____53967 =
                let uu____53972 =
                  let uu____53973 =
                    let uu____53981 = constr_id_of_sort sort  in
                    (uu____53981, [xx])  in
                  mkApp uu____53973 norng  in
                let uu____53986 =
                  let uu____53987 = FStar_Util.string_of_int id1  in
                  mkInteger uu____53987 norng  in
                (uu____53972, uu____53986)  in
              mkEq uu____53967 norng  in
            let uu____53989 =
              let uu____54008 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54072  ->
                          match uu____54072 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54102 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54102, [])
                              else
                                (let fi =
                                   let uu____54111 =
                                     let uu____54117 =
                                       let uu____54119 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54119  in
                                     (uu____54117, s)  in
                                   mk_fv uu____54111  in
                                 let uu____54123 = mkFreeV fi norng  in
                                 (uu____54123, [fi]))))
                 in
              FStar_All.pipe_right uu____54008 FStar_List.split  in
            match uu____53989 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54220 =
                    let uu____54225 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54225)  in
                  mkEq uu____54220 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54238 ->
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
          let uu____54273 =
            let uu____54276 =
              let uu____54277 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54277  in
            uu____54276 :: cdecl :: cid :: projs  in
          let uu____54280 =
            let uu____54283 =
              let uu____54286 =
                let uu____54287 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54287  in
              [uu____54286]  in
            FStar_List.append [disc] uu____54283  in
          FStar_List.append uu____54273 uu____54280
  
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
          let uu____54339 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54388  ->
                    fun s  ->
                      match uu____54388 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54433 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54444 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54444  in
                          let names2 =
                            let uu____54449 = mk_fv (nm, s)  in uu____54449
                              :: names1
                             in
                          let b =
                            let uu____54453 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54453  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54339 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54524 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54524 with
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
              (let uu____54688 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54688)
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
                               "Prims.guard_free",{ tm = BoundV uu____54734;
                                                    freevars = uu____54735;
                                                    rng = uu____54736;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54757 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54835 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54835 fv_name
          | FreeV x when fv_force x ->
              let uu____54846 =
                let uu____54848 = fv_name x  in
                Prims.op_Hat uu____54848 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54846
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54870 = op_to_string op  in
              let uu____54872 =
                let uu____54874 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54874 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54870 uu____54872
          | Labeled (t2,uu____54886,uu____54887) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54894 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54894 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54922 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54922 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____54975 ->
                         let uu____54980 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____54999 =
                                     let uu____55001 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55009 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55009) pats2
                                        in
                                     FStar_String.concat " " uu____55001  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____54999))
                            in
                         FStar_All.pipe_right uu____54980
                           (FStar_String.concat "\n")
                      in
                   let uu____55019 =
                     let uu____55023 =
                       let uu____55027 =
                         let uu____55031 = aux1 n2 names2 body  in
                         let uu____55033 =
                           let uu____55037 = weightToSmt wopt  in
                           [uu____55037; pats_str; qid]  in
                         uu____55031 :: uu____55033  in
                       binders1 :: uu____55027  in
                     (qop_to_string qop) :: uu____55023  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55019)
          | Let (es,body) ->
              let uu____55053 =
                FStar_List.fold_left
                  (fun uu____55086  ->
                     fun e  ->
                       match uu____55086 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55129 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55129  in
                           let names01 =
                             let uu____55135 = mk_fv (nm, Term_sort)  in
                             uu____55135 :: names0  in
                           let b =
                             let uu____55139 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55139  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55053 with
               | (names2,binders,n2) ->
                   let uu____55173 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55173)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55189 = FStar_Range.string_of_range t1.rng  in
            let uu____55191 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55189
              uu____55191 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55213  ->
      match uu___408_55213 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55224 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55224 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55246 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55321 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55321 (FStar_String.concat "\n")  in
            let uu____55331 = FStar_Options.keep_query_captions ()  in
            if uu____55331
            then
              let uu____55335 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55337 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55335 uu____55337
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55346 =
                let uu____55348 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55348 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55346
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55389 = caption_to_string print_captions c  in
            let uu____55391 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55389 f
              (FStar_String.concat " " l) uu____55391
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55406 = name_macro_binders arg_sorts  in
            (match uu____55406 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55430 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55430 body  in
                 let uu____55435 = caption_to_string print_captions c  in
                 let uu____55437 = strSort retsort  in
                 let uu____55439 =
                   let uu____55441 = escape f  in
                   termToSmt print_captions uu____55441 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55435 f (FStar_String.concat " " binders)
                   uu____55437 uu____55439)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55468  ->
                      match uu___409_55468 with
                      | Name n1 ->
                          let uu____55471 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55471
                      | Namespace ns ->
                          let uu____55475 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55475
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55485 =
                  let uu____55487 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55487  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55485
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55498 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55500 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55498
              fids uu____55500 n1
        | Eval t ->
            let uu____55504 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55504
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55511 -> ""
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
      let uu____55532 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55532 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55543 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55543 (FStar_String.concat "\n")

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
      let uu____55678 =
        let uu____55682 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55682
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55678 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55713 =
      let uu____55714 =
        let uu____55716 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55716  in
      let uu____55725 =
        let uu____55728 =
          let uu____55729 =
            let uu____55731 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55731  in
          (uu____55729, (BitVec_sort sz), true)  in
        [uu____55728]  in
      (uu____55714, uu____55725, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55713 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55774  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55799 =
       let uu____55801 = FStar_ST.op_Bang __range_c  in
       uu____55801 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55799);
    (let uu____55846 =
       let uu____55854 =
         let uu____55857 = mkInteger' i norng  in [uu____55857]  in
       ("Range_const", uu____55854)  in
     mkApp uu____55846 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55900 =
        let uu____55908 =
          let uu____55911 = mkInteger' i norng  in [uu____55911]  in
        ("Tm_uvar", uu____55908)  in
      mkApp uu____55900 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____55954 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____55978 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____55978 u v1 t
  
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
      let uu____56073 =
        let uu____56075 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56075  in
      let uu____56084 =
        let uu____56086 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56086  in
      elim_box true uu____56073 uu____56084 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56109 =
        let uu____56111 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56111  in
      let uu____56120 =
        let uu____56122 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56122  in
      elim_box true uu____56109 uu____56120 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56146 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56161 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56187 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56187
         | uu____56190 -> FStar_Pervasives_Native.None)
    | uu____56192 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56210::t1::t2::[]);
                       freevars = uu____56213; rng = uu____56214;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56233::t1::t2::[]);
                       freevars = uu____56236; rng = uu____56237;_}::[])
        -> let uu____56256 = mkEq (t1, t2) norng  in mkNot uu____56256 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56259; rng = uu____56260;_}::[])
        ->
        let uu____56279 =
          let uu____56284 = unboxInt t1  in
          let uu____56285 = unboxInt t2  in (uu____56284, uu____56285)  in
        mkLTE uu____56279 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56288; rng = uu____56289;_}::[])
        ->
        let uu____56308 =
          let uu____56313 = unboxInt t1  in
          let uu____56314 = unboxInt t2  in (uu____56313, uu____56314)  in
        mkLT uu____56308 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56317; rng = uu____56318;_}::[])
        ->
        let uu____56337 =
          let uu____56342 = unboxInt t1  in
          let uu____56343 = unboxInt t2  in (uu____56342, uu____56343)  in
        mkGTE uu____56337 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56346; rng = uu____56347;_}::[])
        ->
        let uu____56366 =
          let uu____56371 = unboxInt t1  in
          let uu____56372 = unboxInt t2  in (uu____56371, uu____56372)  in
        mkGT uu____56366 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56375; rng = uu____56376;_}::[])
        ->
        let uu____56395 =
          let uu____56400 = unboxBool t1  in
          let uu____56401 = unboxBool t2  in (uu____56400, uu____56401)  in
        mkAnd uu____56395 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56404; rng = uu____56405;_}::[])
        ->
        let uu____56424 =
          let uu____56429 = unboxBool t1  in
          let uu____56430 = unboxBool t2  in (uu____56429, uu____56430)  in
        mkOr uu____56424 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56432; rng = uu____56433;_}::[])
        -> let uu____56452 = unboxBool t1  in mkNot uu____56452 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56456; rng = uu____56457;_}::[])
        when
        let uu____56476 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56476 ->
        let sz =
          let uu____56483 = getBoxedInteger t0  in
          match uu____56483 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56491 -> failwith "impossible"  in
        let uu____56497 =
          let uu____56502 = unboxBitVec sz t1  in
          let uu____56503 = unboxBitVec sz t2  in (uu____56502, uu____56503)
           in
        mkBvUlt uu____56497 t.rng
    | App
        (Var
         "Prims.equals",uu____56504::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56508;
                                       rng = uu____56509;_}::uu____56510::[])
        when
        let uu____56529 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56529 ->
        let sz =
          let uu____56536 = getBoxedInteger t0  in
          match uu____56536 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56544 -> failwith "impossible"  in
        let uu____56550 =
          let uu____56555 = unboxBitVec sz t1  in
          let uu____56556 = unboxBitVec sz t2  in (uu____56555, uu____56556)
           in
        mkBvUlt uu____56550 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56561 = unboxBool t1  in
        {
          tm = (uu___1789_56561.tm);
          freevars = (uu___1789_56561.freevars);
          rng = (t.rng)
        }
    | uu____56562 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56623 = FStar_Options.unthrottle_inductives ()  in
        if uu____56623
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
    let uu____56756 =
      let uu____56757 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56757 t t.rng  in
    FStar_All.pipe_right uu____56756 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56775 =
        let uu____56783 =
          let uu____56786 = mkInteger' i norng  in [uu____56786]  in
        ("FString_const", uu____56783)  in
      mkApp uu____56775 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56817 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56817 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56864 =
         let uu____56872 =
           let uu____56875 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56875]  in
         ("SFuel", uu____56872)  in
       mkApp uu____56864 norng)
  
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
            let uu____56923 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56923
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
      let uu____56986 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____56986
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57006 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57006
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57017 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57017
  
let (dummy_sort : sort) = Sort "Dummy_sort" 