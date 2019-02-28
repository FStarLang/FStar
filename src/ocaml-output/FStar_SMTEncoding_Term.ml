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
    match projectee with | Bool_sort  -> true | uu____47393 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47404 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47415 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47426 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47437 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47450 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47477 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47513 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47546 -> false
  
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
        let uu____47574 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47574
    | Array (s1,s2) ->
        let uu____47579 = strSort s1  in
        let uu____47581 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47579 uu____47581
    | Arrow (s1,s2) ->
        let uu____47586 = strSort s1  in
        let uu____47588 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47586 uu____47588
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
    match projectee with | TrueOp  -> true | uu____47620 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47631 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47642 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47653 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47664 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47675 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47686 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47697 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47708 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47719 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47730 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47741 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47752 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47763 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47774 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47785 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47796 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47807 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47818 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47829 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47840 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47851 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47862 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47873 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47884 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47895 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47906 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47917 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47928 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47939 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47952 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47976 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____47998 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____48009 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____48022 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____48044 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____48055 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48215 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48239 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48263 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48294 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48344 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48401 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48484 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48529 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48575 -> false
  
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
    match projectee with | Name _0 -> true | uu____48799 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48819 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48840 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____49030 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____49053 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49119 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49178 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49199 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49229 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49270 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49291 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49317 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49345 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49356 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49367 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49378 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49396 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49433 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49444 -> false
  
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
          let uu____49618 =
            let uu____49619 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49645 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49619
            }  in
          [uu____49618]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49659 =
      let uu____49660 =
        FStar_List.collect
          (fun uu___402_49667  ->
             match uu___402_49667 with
             | Assume a -> [a.assumption_name]
             | uu____49674 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49660
      }  in
    [uu____49659]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49711  -> match uu____49711 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49731 = x  in
    match uu____49731 with | (nm,uu____49734,uu____49735) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49746 = x  in
    match uu____49746 with | (uu____49747,sort,uu____49749) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49761 = x  in
    match uu____49761 with | (uu____49763,uu____49764,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49782 = fv_name x  in
      let uu____49784 = fv_name y  in uu____49782 = uu____49784
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49818 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49829  ->
    match uu___403_49829 with
    | { tm = FreeV x; freevars = uu____49831; rng = uu____49832;_} ->
        fv_sort x
    | uu____49853 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49860  ->
    match uu___404_49860 with
    | { tm = FreeV fv; freevars = uu____49862; rng = uu____49863;_} -> fv
    | uu____49884 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49912 -> []
    | Real uu____49922 -> []
    | BoundV uu____49932 -> []
    | FreeV fv -> [fv]
    | App (uu____49967,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49981,uu____49982,uu____49983,uu____49984,t1) ->
        freevars t1
    | Labeled (t1,uu____50005,uu____50006) -> freevars t1
    | LblPos (t1,uu____50010) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____50033 = FStar_ST.op_Bang t.freevars  in
    match uu____50033 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50131 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50131  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50210  ->
    match uu___405_50210 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50220  ->
    match uu___406_50220 with
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
        let uu____50256 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50256
    | NatToBv n1 ->
        let uu____50261 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50261
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50275  ->
    match uu___407_50275 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50285 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50285
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50307 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50307
    | FreeV x ->
        let uu____50319 = fv_name x  in
        let uu____50321 =
          let uu____50323 =
            let uu____50325 = fv_sort x  in strSort uu____50325  in
          Prims.op_Hat ":" uu____50323  in
        Prims.op_Hat uu____50319 uu____50321
    | App (op,tms) ->
        let uu____50333 =
          let uu____50335 = op_to_string op  in
          let uu____50337 =
            let uu____50339 =
              let uu____50341 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50341 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50339 ")"  in
          Prims.op_Hat uu____50335 uu____50337  in
        Prims.op_Hat "(" uu____50333
    | Labeled (t1,r1,r2) ->
        let uu____50358 = hash_of_term t1  in
        let uu____50360 =
          let uu____50362 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50362  in
        Prims.op_Hat uu____50358 uu____50360
    | LblPos (t1,r) ->
        let uu____50368 =
          let uu____50370 = hash_of_term t1  in
          Prims.op_Hat uu____50370
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50368
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50398 =
          let uu____50400 =
            let uu____50402 =
              let uu____50404 =
                let uu____50406 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50406 (FStar_String.concat " ")
                 in
              let uu____50416 =
                let uu____50418 =
                  let uu____50420 = hash_of_term body  in
                  let uu____50422 =
                    let uu____50424 =
                      let uu____50426 = weightToSmt wopt  in
                      let uu____50428 =
                        let uu____50430 =
                          let uu____50432 =
                            let uu____50434 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50453 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50453
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50434
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50432 "))"  in
                        Prims.op_Hat " " uu____50430  in
                      Prims.op_Hat uu____50426 uu____50428  in
                    Prims.op_Hat " " uu____50424  in
                  Prims.op_Hat uu____50420 uu____50422  in
                Prims.op_Hat ")(! " uu____50418  in
              Prims.op_Hat uu____50404 uu____50416  in
            Prims.op_Hat " (" uu____50402  in
          Prims.op_Hat (qop_to_string qop) uu____50400  in
        Prims.op_Hat "(" uu____50398
    | Let (es,body) ->
        let uu____50480 =
          let uu____50482 =
            let uu____50484 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50484 (FStar_String.concat " ")  in
          let uu____50494 =
            let uu____50496 =
              let uu____50498 = hash_of_term body  in
              Prims.op_Hat uu____50498 ")"  in
            Prims.op_Hat ") " uu____50496  in
          Prims.op_Hat uu____50482 uu____50494  in
        Prims.op_Hat "(let (" uu____50480

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50559 =
      let uu____50561 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50561  in
    mkBoxFunctions uu____50559
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50586 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50586 = "Box") &&
        (let uu____50593 =
           let uu____50595 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50595  in
         Prims.op_Negation uu____50593)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50619 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50619; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50705 =
        let uu____50706 = FStar_Util.ensure_decimal i  in Integer uu____50706
         in
      mk uu____50705 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50721 = FStar_Util.string_of_int i  in
      mkInteger uu____50721 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50799  ->
    fun r  -> match uu____50799 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50829) -> mkFalse r
      | App (FalseOp ,uu____50834) -> mkTrue r
      | uu____50839 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50855  ->
    fun r  ->
      match uu____50855 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50863),uu____50864) -> t2
           | (uu____50869,App (TrueOp ,uu____50870)) -> t1
           | (App (FalseOp ,uu____50875),uu____50876) -> mkFalse r
           | (uu____50881,App (FalseOp ,uu____50882)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50899,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50908) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50915 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50935  ->
    fun r  ->
      match uu____50935 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50943),uu____50944) -> mkTrue r
           | (uu____50949,App (TrueOp ,uu____50950)) -> mkTrue r
           | (App (FalseOp ,uu____50955),uu____50956) -> t2
           | (uu____50961,App (FalseOp ,uu____50962)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50979,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50988) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____50995 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____51015  ->
    fun r  ->
      match uu____51015 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____51023,App (TrueOp ,uu____51024)) -> mkTrue r
           | (App (FalseOp ,uu____51029),uu____51030) -> mkTrue r
           | (App (TrueOp ,uu____51035),uu____51036) -> t2
           | (uu____51041,App (Imp ,t1'::t2'::[])) ->
               let uu____51046 =
                 let uu____51053 =
                   let uu____51056 = mkAnd (t1, t1') r  in [uu____51056; t2']
                    in
                 (Imp, uu____51053)  in
               mkApp' uu____51046 r
           | uu____51059 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51084  ->
      fun r  -> match uu____51084 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51244  ->
      fun r  ->
        match uu____51244 with
        | (t1,t2) ->
            let uu____51253 =
              let uu____51260 =
                let uu____51263 =
                  let uu____51266 = mkNatToBv sz t2 r  in [uu____51266]  in
                t1 :: uu____51263  in
              (BvShl, uu____51260)  in
            mkApp' uu____51253 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51288  ->
      fun r  ->
        match uu____51288 with
        | (t1,t2) ->
            let uu____51297 =
              let uu____51304 =
                let uu____51307 =
                  let uu____51310 = mkNatToBv sz t2 r  in [uu____51310]  in
                t1 :: uu____51307  in
              (BvShr, uu____51304)  in
            mkApp' uu____51297 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51332  ->
      fun r  ->
        match uu____51332 with
        | (t1,t2) ->
            let uu____51341 =
              let uu____51348 =
                let uu____51351 =
                  let uu____51354 = mkNatToBv sz t2 r  in [uu____51354]  in
                t1 :: uu____51351  in
              (BvUdiv, uu____51348)  in
            mkApp' uu____51341 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51376  ->
      fun r  ->
        match uu____51376 with
        | (t1,t2) ->
            let uu____51385 =
              let uu____51392 =
                let uu____51395 =
                  let uu____51398 = mkNatToBv sz t2 r  in [uu____51398]  in
                t1 :: uu____51395  in
              (BvMod, uu____51392)  in
            mkApp' uu____51385 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51420  ->
      fun r  ->
        match uu____51420 with
        | (t1,t2) ->
            let uu____51429 =
              let uu____51436 =
                let uu____51439 =
                  let uu____51442 = mkNatToBv sz t2 r  in [uu____51442]  in
                t1 :: uu____51439  in
              (BvMul, uu____51436)  in
            mkApp' uu____51429 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51484  ->
    fun r  ->
      match uu____51484 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51503 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51668  ->
    fun r  ->
      match uu____51668 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51679) -> t2
           | App (FalseOp ,uu____51684) -> t3
           | uu____51689 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51690),App (TrueOp ,uu____51691)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51700),uu____51701) ->
                    let uu____51706 =
                      let uu____51711 = mkNot t1 t1.rng  in (uu____51711, t3)
                       in
                    mkImp uu____51706 r
                | (uu____51712,App (TrueOp ,uu____51713)) -> mkImp (t1, t2) r
                | (uu____51718,uu____51719) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51775 -> FStar_Pervasives_Native.None
      | Real uu____51777 -> FStar_Pervasives_Native.None
      | BoundV uu____51779 -> FStar_Pervasives_Native.None
      | FreeV uu____51781 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51805 -> true
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
            | BvUext uu____51838 -> false
            | NatToBv uu____51841 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51852,uu____51853) -> aux t2
      | Quant uu____51856 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51876 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51891 = aux t1  in
          (match uu____51891 with
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
        let uu____51929 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51929
    | FreeV fv ->
        let uu____51941 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51941
    | App (op,l) ->
        let uu____51950 = op_to_string op  in
        let uu____51952 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51950 uu____51952
    | Labeled (t1,r1,r2) ->
        let uu____51960 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51960
    | LblPos (t1,s) ->
        let uu____51967 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51967
    | Quant (qop,l,uu____51972,uu____51973,t1) ->
        let uu____51993 = print_smt_term_list_list l  in
        let uu____51995 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51993
          uu____51995
    | Let (es,body) ->
        let uu____52004 = print_smt_term_list es  in
        let uu____52006 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____52004 uu____52006

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____52013 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____52013 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____52040 =
             let uu____52042 =
               let uu____52044 = print_smt_term_list l1  in
               Prims.op_Hat uu____52044 " ] "  in
             Prims.op_Hat "; [ " uu____52042  in
           Prims.op_Hat s uu____52040) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52084  ->
        match uu____52084 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52153 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52153 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52168 =
                         let uu____52174 =
                           let uu____52176 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52176
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____52174)
                          in
                       FStar_Errors.log_issue r uu____52168);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52187) -> body
               | uu____52192 ->
                   let uu____52193 =
                     let uu____52194 =
                       let uu____52214 = all_pats_ok pats  in
                       (qop, uu____52214, wopt, vars, body)  in
                     Quant uu____52194  in
                   mk uu____52193 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52243  ->
    fun r  ->
      match uu____52243 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52289 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52289 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52322 = FStar_ST.op_Bang t1.freevars  in
        match uu____52322 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52396 ->
            (match t1.tm with
             | Integer uu____52409 -> t1
             | Real uu____52411 -> t1
             | BoundV uu____52413 -> t1
             | FreeV x ->
                 let uu____52424 = index_of1 x  in
                 (match uu____52424 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52438 =
                   let uu____52445 = FStar_List.map (aux ix) tms  in
                   (op, uu____52445)  in
                 mkApp' uu____52438 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52455 =
                   let uu____52456 =
                     let uu____52464 = aux ix t2  in (uu____52464, r1, r2)
                      in
                   Labeled uu____52456  in
                 mk uu____52455 t2.rng
             | LblPos (t2,r) ->
                 let uu____52470 =
                   let uu____52471 =
                     let uu____52477 = aux ix t2  in (uu____52477, r)  in
                   LblPos uu____52471  in
                 mk uu____52470 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52503 =
                   let uu____52523 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52544 = aux (ix + n1) body  in
                   (qop, uu____52523, wopt, vars, uu____52544)  in
                 mkQuant t1.rng false uu____52503
             | Let (es,body) ->
                 let uu____52565 =
                   FStar_List.fold_left
                     (fun uu____52585  ->
                        fun e  ->
                          match uu____52585 with
                          | (ix1,l) ->
                              let uu____52609 =
                                let uu____52612 = aux ix1 e  in uu____52612
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52609))
                     (ix, []) es
                    in
                 (match uu____52565 with
                  | (ix1,es_rev) ->
                      let uu____52628 =
                        let uu____52635 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52635)  in
                      mkLet uu____52628 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52671 -> t1
        | Real uu____52673 -> t1
        | FreeV uu____52675 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52700 =
              let uu____52707 = FStar_List.map (aux shift) tms2  in
              (op, uu____52707)  in
            mkApp' uu____52700 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52717 =
              let uu____52718 =
                let uu____52726 = aux shift t2  in (uu____52726, r1, r2)  in
              Labeled uu____52718  in
            mk uu____52717 t2.rng
        | LblPos (t2,r) ->
            let uu____52732 =
              let uu____52733 =
                let uu____52739 = aux shift t2  in (uu____52739, r)  in
              LblPos uu____52733  in
            mk uu____52732 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52771 =
              let uu____52791 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52808 = aux shift1 body  in
              (qop, uu____52791, wopt, vars, uu____52808)  in
            mkQuant t1.rng false uu____52771
        | Let (es,body) ->
            let uu____52825 =
              FStar_List.fold_left
                (fun uu____52845  ->
                   fun e  ->
                     match uu____52845 with
                     | (ix,es1) ->
                         let uu____52869 =
                           let uu____52872 = aux shift e  in uu____52872 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52869))
                (shift, []) es
               in
            (match uu____52825 with
             | (shift1,es_rev) ->
                 let uu____52888 =
                   let uu____52895 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52895)  in
                 mkLet uu____52888 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52915 = abstr [fv] t  in inst [s] uu____52915
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52945  ->
      match uu____52945 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52988 =
            let uu____53008 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____53025 = FStar_List.map fv_sort vars  in
            let uu____53028 = abstr vars body  in
            (qop, uu____53008, wopt, uu____53025, uu____53028)  in
          mkQuant r true uu____52988
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53059  ->
      match uu____53059 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53118  ->
      match uu____53118 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53193  ->
      match uu____53193 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53256  ->
      match uu____53256 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53307  ->
    fun r  ->
      match uu____53307 with
      | (bindings,body) ->
          let uu____53333 = FStar_List.split bindings  in
          (match uu____53333 with
           | (vars,es) ->
               let uu____53352 =
                 let uu____53359 = abstr vars body  in (es, uu____53359)  in
               mkLet uu____53352 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53381  ->
    match uu____53381 with
    | (nm,vars,s,tm,c) ->
        let uu____53406 =
          let uu____53420 = FStar_List.map fv_sort vars  in
          let uu____53423 = abstr vars tm  in
          (nm, uu____53420, s, uu____53423, c)  in
        DefineFun uu____53406
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53434 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53434
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53452  ->
    fun id1  ->
      match uu____53452 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53468 =
              let uu____53469 =
                let uu____53474 = mkInteger' id1 norng  in
                let uu____53475 =
                  let uu____53476 =
                    let uu____53484 = constr_id_of_sort sort  in
                    let uu____53486 =
                      let uu____53489 = mkApp (tok_name, []) norng  in
                      [uu____53489]  in
                    (uu____53484, uu____53486)  in
                  mkApp uu____53476 norng  in
                (uu____53474, uu____53475)  in
              mkEq uu____53469 norng  in
            let uu____53496 = escape a_name  in
            {
              assumption_term = uu____53468;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53496;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53522  ->
      match uu____53522 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53562 =
                        let uu____53563 =
                          let uu____53569 =
                            let uu____53571 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53571  in
                          (uu____53569, s)  in
                        mk_fv uu____53563  in
                      mkFreeV uu____53562 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53599 =
              let uu____53607 = constr_id_of_sort sort  in
              (uu____53607, [capp])  in
            mkApp uu____53599 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53616 =
              let uu____53617 =
                let uu____53628 =
                  let uu____53629 =
                    let uu____53634 = mkInteger id2 norng  in
                    (uu____53634, cid_app)  in
                  mkEq uu____53629 norng  in
                ([[capp]], bvar_names, uu____53628)  in
              mkForall rng uu____53617  in
            let uu____53643 = escape a_name  in
            {
              assumption_term = uu____53616;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53643;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53668  ->
      match uu____53668 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53701 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53701  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53736 =
              let uu____53737 =
                let uu____53743 = bvar_name i  in (uu____53743, s)  in
              mk_fv uu____53737  in
            FStar_All.pipe_left mkFreeV uu____53736  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53779  ->
                      match uu____53779 with
                      | (uu____53789,s,uu____53791) ->
                          let uu____53796 = bvar i s  in uu____53796 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53824 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53862  ->
                      match uu____53862 with
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
                              let uu____53895 =
                                let uu____53896 =
                                  let uu____53907 =
                                    let uu____53908 =
                                      let uu____53913 =
                                        let uu____53914 = bvar i s  in
                                        uu____53914 norng  in
                                      (cproj_app, uu____53913)  in
                                    mkEq uu____53908 norng  in
                                  ([[capp]], bvar_names, uu____53907)  in
                                mkForall rng uu____53896  in
                              let uu____53927 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53895;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53927;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53824 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53952  ->
      match uu____53952 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____54000  ->
                    match uu____54000 with
                    | (uu____54009,sort1,uu____54011) -> sort1))
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
              let uu____54036 =
                let uu____54041 =
                  let uu____54042 =
                    let uu____54050 = constr_id_of_sort sort  in
                    (uu____54050, [xx])  in
                  mkApp uu____54042 norng  in
                let uu____54055 =
                  let uu____54056 = FStar_Util.string_of_int id1  in
                  mkInteger uu____54056 norng  in
                (uu____54041, uu____54055)  in
              mkEq uu____54036 norng  in
            let uu____54058 =
              let uu____54077 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54141  ->
                          match uu____54141 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54171 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54171, [])
                              else
                                (let fi =
                                   let uu____54180 =
                                     let uu____54186 =
                                       let uu____54188 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54188  in
                                     (uu____54186, s)  in
                                   mk_fv uu____54180  in
                                 let uu____54192 = mkFreeV fi norng  in
                                 (uu____54192, [fi]))))
                 in
              FStar_All.pipe_right uu____54077 FStar_List.split  in
            match uu____54058 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54289 =
                    let uu____54294 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54294)  in
                  mkEq uu____54289 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54307 ->
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
          let uu____54342 =
            let uu____54345 =
              let uu____54346 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54346  in
            uu____54345 :: cdecl :: cid :: projs  in
          let uu____54349 =
            let uu____54352 =
              let uu____54355 =
                let uu____54356 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54356  in
              [uu____54355]  in
            FStar_List.append [disc] uu____54352  in
          FStar_List.append uu____54342 uu____54349
  
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
          let uu____54408 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54457  ->
                    fun s  ->
                      match uu____54457 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54502 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54513 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54513  in
                          let names2 =
                            let uu____54518 = mk_fv (nm, s)  in uu____54518
                              :: names1
                             in
                          let b =
                            let uu____54522 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54522  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54408 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54593 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54593 with
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
              (let uu____54757 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54757)
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
                               "Prims.guard_free",{ tm = BoundV uu____54803;
                                                    freevars = uu____54804;
                                                    rng = uu____54805;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54826 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54904 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54904 fv_name
          | FreeV x when fv_force x ->
              let uu____54915 =
                let uu____54917 = fv_name x  in
                Prims.op_Hat uu____54917 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54915
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54939 = op_to_string op  in
              let uu____54941 =
                let uu____54943 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54943 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54939 uu____54941
          | Labeled (t2,uu____54955,uu____54956) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54963 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54963 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54991 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54991 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____55044 ->
                         let uu____55049 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____55068 =
                                     let uu____55070 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55078 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55078) pats2
                                        in
                                     FStar_String.concat " " uu____55070  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____55068))
                            in
                         FStar_All.pipe_right uu____55049
                           (FStar_String.concat "\n")
                      in
                   let uu____55088 =
                     let uu____55092 =
                       let uu____55096 =
                         let uu____55100 = aux1 n2 names2 body  in
                         let uu____55102 =
                           let uu____55106 = weightToSmt wopt  in
                           [uu____55106; pats_str; qid]  in
                         uu____55100 :: uu____55102  in
                       binders1 :: uu____55096  in
                     (qop_to_string qop) :: uu____55092  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55088)
          | Let (es,body) ->
              let uu____55122 =
                FStar_List.fold_left
                  (fun uu____55155  ->
                     fun e  ->
                       match uu____55155 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55198 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55198  in
                           let names01 =
                             let uu____55204 = mk_fv (nm, Term_sort)  in
                             uu____55204 :: names0  in
                           let b =
                             let uu____55208 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55208  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55122 with
               | (names2,binders,n2) ->
                   let uu____55242 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55242)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55258 = FStar_Range.string_of_range t1.rng  in
            let uu____55260 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55258
              uu____55260 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55282  ->
      match uu___408_55282 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55293 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55293 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55315 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55390 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55390 (FStar_String.concat "\n")  in
            let uu____55400 = FStar_Options.keep_query_captions ()  in
            if uu____55400
            then
              let uu____55404 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55406 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55404 uu____55406
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55415 =
                let uu____55417 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55417 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55415
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55458 = caption_to_string print_captions c  in
            let uu____55460 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55458 f
              (FStar_String.concat " " l) uu____55460
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55475 = name_macro_binders arg_sorts  in
            (match uu____55475 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55499 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55499 body  in
                 let uu____55504 = caption_to_string print_captions c  in
                 let uu____55506 = strSort retsort  in
                 let uu____55508 =
                   let uu____55510 = escape f  in
                   termToSmt print_captions uu____55510 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55504 f (FStar_String.concat " " binders)
                   uu____55506 uu____55508)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55537  ->
                      match uu___409_55537 with
                      | Name n1 ->
                          let uu____55540 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55540
                      | Namespace ns ->
                          let uu____55544 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55544
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55554 =
                  let uu____55556 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55556  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55554
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55567 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55569 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55567
              fids uu____55569 n1
        | Eval t ->
            let uu____55573 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55573
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55580 -> ""
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
      let uu____55601 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55601 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55612 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55612 (FStar_String.concat "\n")

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
      let uu____55747 =
        let uu____55751 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55751
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55747 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55782 =
      let uu____55783 =
        let uu____55785 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55785  in
      let uu____55794 =
        let uu____55797 =
          let uu____55798 =
            let uu____55800 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55800  in
          (uu____55798, (BitVec_sort sz), true)  in
        [uu____55797]  in
      (uu____55783, uu____55794, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55782 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55843  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55868 =
       let uu____55870 = FStar_ST.op_Bang __range_c  in
       uu____55870 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55868);
    (let uu____55915 =
       let uu____55923 =
         let uu____55926 = mkInteger' i norng  in [uu____55926]  in
       ("Range_const", uu____55923)  in
     mkApp uu____55915 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55969 =
        let uu____55977 =
          let uu____55980 = mkInteger' i norng  in [uu____55980]  in
        ("Tm_uvar", uu____55977)  in
      mkApp uu____55969 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____56023 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____56047 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____56047 u v1 t
  
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
      let uu____56142 =
        let uu____56144 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56144  in
      let uu____56153 =
        let uu____56155 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56155  in
      elim_box true uu____56142 uu____56153 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56178 =
        let uu____56180 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56180  in
      let uu____56189 =
        let uu____56191 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56191  in
      elim_box true uu____56178 uu____56189 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56215 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56230 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56256 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56256
         | uu____56259 -> FStar_Pervasives_Native.None)
    | uu____56261 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56279::t1::t2::[]);
                       freevars = uu____56282; rng = uu____56283;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56302::t1::t2::[]);
                       freevars = uu____56305; rng = uu____56306;_}::[])
        -> let uu____56325 = mkEq (t1, t2) norng  in mkNot uu____56325 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56328; rng = uu____56329;_}::[])
        ->
        let uu____56348 =
          let uu____56353 = unboxInt t1  in
          let uu____56354 = unboxInt t2  in (uu____56353, uu____56354)  in
        mkLTE uu____56348 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56357; rng = uu____56358;_}::[])
        ->
        let uu____56377 =
          let uu____56382 = unboxInt t1  in
          let uu____56383 = unboxInt t2  in (uu____56382, uu____56383)  in
        mkLT uu____56377 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56386; rng = uu____56387;_}::[])
        ->
        let uu____56406 =
          let uu____56411 = unboxInt t1  in
          let uu____56412 = unboxInt t2  in (uu____56411, uu____56412)  in
        mkGTE uu____56406 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56415; rng = uu____56416;_}::[])
        ->
        let uu____56435 =
          let uu____56440 = unboxInt t1  in
          let uu____56441 = unboxInt t2  in (uu____56440, uu____56441)  in
        mkGT uu____56435 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56444; rng = uu____56445;_}::[])
        ->
        let uu____56464 =
          let uu____56469 = unboxBool t1  in
          let uu____56470 = unboxBool t2  in (uu____56469, uu____56470)  in
        mkAnd uu____56464 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56473; rng = uu____56474;_}::[])
        ->
        let uu____56493 =
          let uu____56498 = unboxBool t1  in
          let uu____56499 = unboxBool t2  in (uu____56498, uu____56499)  in
        mkOr uu____56493 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56501; rng = uu____56502;_}::[])
        -> let uu____56521 = unboxBool t1  in mkNot uu____56521 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56525; rng = uu____56526;_}::[])
        when
        let uu____56545 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56545 ->
        let sz =
          let uu____56552 = getBoxedInteger t0  in
          match uu____56552 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56560 -> failwith "impossible"  in
        let uu____56566 =
          let uu____56571 = unboxBitVec sz t1  in
          let uu____56572 = unboxBitVec sz t2  in (uu____56571, uu____56572)
           in
        mkBvUlt uu____56566 t.rng
    | App
        (Var
         "Prims.equals",uu____56573::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56577;
                                       rng = uu____56578;_}::uu____56579::[])
        when
        let uu____56598 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56598 ->
        let sz =
          let uu____56605 = getBoxedInteger t0  in
          match uu____56605 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56613 -> failwith "impossible"  in
        let uu____56619 =
          let uu____56624 = unboxBitVec sz t1  in
          let uu____56625 = unboxBitVec sz t2  in (uu____56624, uu____56625)
           in
        mkBvUlt uu____56619 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56630 = unboxBool t1  in
        {
          tm = (uu___1789_56630.tm);
          freevars = (uu___1789_56630.freevars);
          rng = (t.rng)
        }
    | uu____56631 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56692 = FStar_Options.unthrottle_inductives ()  in
        if uu____56692
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
    let uu____56825 =
      let uu____56826 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56826 t t.rng  in
    FStar_All.pipe_right uu____56825 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56844 =
        let uu____56852 =
          let uu____56855 = mkInteger' i norng  in [uu____56855]  in
        ("FString_const", uu____56852)  in
      mkApp uu____56844 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56886 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56886 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56933 =
         let uu____56941 =
           let uu____56944 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56944]  in
         ("SFuel", uu____56941)  in
       mkApp uu____56933 norng)
  
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
            let uu____56992 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56992
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
      let uu____57055 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____57055
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57075 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57075
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57086 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57086
  
let (dummy_sort : sort) = Sort "Dummy_sort" 