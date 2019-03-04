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
    match projectee with | Bool_sort  -> true | uu____47399 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47410 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47421 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47432 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47443 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47456 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47483 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47519 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47552 -> false
  
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
        let uu____47580 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47580
    | Array (s1,s2) ->
        let uu____47585 = strSort s1  in
        let uu____47587 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47585 uu____47587
    | Arrow (s1,s2) ->
        let uu____47592 = strSort s1  in
        let uu____47594 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47592 uu____47594
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
    match projectee with | TrueOp  -> true | uu____47626 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47637 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47648 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47659 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47670 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47681 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47692 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47703 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47714 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47725 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47736 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47747 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47758 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47769 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47780 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47791 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47802 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47813 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47824 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47835 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47846 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47857 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47868 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47879 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47890 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47901 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47912 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47923 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47934 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47945 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47958 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47982 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____48004 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____48015 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____48028 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____48050 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____48061 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48221 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48245 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48269 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48300 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48350 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48407 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48490 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48535 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48581 -> false
  
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
    match projectee with | Name _0 -> true | uu____48805 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48825 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48846 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____49036 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____49059 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49125 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49184 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49205 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49235 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49276 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49297 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49323 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49351 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49362 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49373 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49384 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49402 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49439 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49450 -> false
  
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
          let uu____49624 =
            let uu____49625 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49651 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49625
            }  in
          [uu____49624]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49665 =
      let uu____49666 =
        FStar_List.collect
          (fun uu___402_49673  ->
             match uu___402_49673 with
             | Assume a -> [a.assumption_name]
             | uu____49680 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49666
      }  in
    [uu____49665]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49717  -> match uu____49717 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49737 = x  in
    match uu____49737 with | (nm,uu____49740,uu____49741) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49752 = x  in
    match uu____49752 with | (uu____49753,sort,uu____49755) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49767 = x  in
    match uu____49767 with | (uu____49769,uu____49770,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49788 = fv_name x  in
      let uu____49790 = fv_name y  in uu____49788 = uu____49790
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49824 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49835  ->
    match uu___403_49835 with
    | { tm = FreeV x; freevars = uu____49837; rng = uu____49838;_} ->
        fv_sort x
    | uu____49859 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49866  ->
    match uu___404_49866 with
    | { tm = FreeV fv; freevars = uu____49868; rng = uu____49869;_} -> fv
    | uu____49890 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49918 -> []
    | Real uu____49928 -> []
    | BoundV uu____49938 -> []
    | FreeV fv -> [fv]
    | App (uu____49973,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49987,uu____49988,uu____49989,uu____49990,t1) ->
        freevars t1
    | Labeled (t1,uu____50011,uu____50012) -> freevars t1
    | LblPos (t1,uu____50016) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____50039 = FStar_ST.op_Bang t.freevars  in
    match uu____50039 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50137 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50137  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50216  ->
    match uu___405_50216 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50226  ->
    match uu___406_50226 with
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
        let uu____50262 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50262
    | NatToBv n1 ->
        let uu____50267 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50267
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50281  ->
    match uu___407_50281 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50291 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50291
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50313 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50313
    | FreeV x ->
        let uu____50325 = fv_name x  in
        let uu____50327 =
          let uu____50329 =
            let uu____50331 = fv_sort x  in strSort uu____50331  in
          Prims.op_Hat ":" uu____50329  in
        Prims.op_Hat uu____50325 uu____50327
    | App (op,tms) ->
        let uu____50339 =
          let uu____50341 = op_to_string op  in
          let uu____50343 =
            let uu____50345 =
              let uu____50347 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50347 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50345 ")"  in
          Prims.op_Hat uu____50341 uu____50343  in
        Prims.op_Hat "(" uu____50339
    | Labeled (t1,r1,r2) ->
        let uu____50364 = hash_of_term t1  in
        let uu____50366 =
          let uu____50368 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50368  in
        Prims.op_Hat uu____50364 uu____50366
    | LblPos (t1,r) ->
        let uu____50374 =
          let uu____50376 = hash_of_term t1  in
          Prims.op_Hat uu____50376
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50374
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50404 =
          let uu____50406 =
            let uu____50408 =
              let uu____50410 =
                let uu____50412 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50412 (FStar_String.concat " ")
                 in
              let uu____50422 =
                let uu____50424 =
                  let uu____50426 = hash_of_term body  in
                  let uu____50428 =
                    let uu____50430 =
                      let uu____50432 = weightToSmt wopt  in
                      let uu____50434 =
                        let uu____50436 =
                          let uu____50438 =
                            let uu____50440 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50459 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50459
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50440
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50438 "))"  in
                        Prims.op_Hat " " uu____50436  in
                      Prims.op_Hat uu____50432 uu____50434  in
                    Prims.op_Hat " " uu____50430  in
                  Prims.op_Hat uu____50426 uu____50428  in
                Prims.op_Hat ")(! " uu____50424  in
              Prims.op_Hat uu____50410 uu____50422  in
            Prims.op_Hat " (" uu____50408  in
          Prims.op_Hat (qop_to_string qop) uu____50406  in
        Prims.op_Hat "(" uu____50404
    | Let (es,body) ->
        let uu____50486 =
          let uu____50488 =
            let uu____50490 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50490 (FStar_String.concat " ")  in
          let uu____50500 =
            let uu____50502 =
              let uu____50504 = hash_of_term body  in
              Prims.op_Hat uu____50504 ")"  in
            Prims.op_Hat ") " uu____50502  in
          Prims.op_Hat uu____50488 uu____50500  in
        Prims.op_Hat "(let (" uu____50486

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50565 =
      let uu____50567 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50567  in
    mkBoxFunctions uu____50565
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50592 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50592 = "Box") &&
        (let uu____50599 =
           let uu____50601 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50601  in
         Prims.op_Negation uu____50599)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50625 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50625; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50711 =
        let uu____50712 = FStar_Util.ensure_decimal i  in Integer uu____50712
         in
      mk uu____50711 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50727 = FStar_Util.string_of_int i  in
      mkInteger uu____50727 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50805  ->
    fun r  -> match uu____50805 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50835) -> mkFalse r
      | App (FalseOp ,uu____50840) -> mkTrue r
      | uu____50845 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50861  ->
    fun r  ->
      match uu____50861 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50869),uu____50870) -> t2
           | (uu____50875,App (TrueOp ,uu____50876)) -> t1
           | (App (FalseOp ,uu____50881),uu____50882) -> mkFalse r
           | (uu____50887,App (FalseOp ,uu____50888)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50905,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50914) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50921 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50941  ->
    fun r  ->
      match uu____50941 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50949),uu____50950) -> mkTrue r
           | (uu____50955,App (TrueOp ,uu____50956)) -> mkTrue r
           | (App (FalseOp ,uu____50961),uu____50962) -> t2
           | (uu____50967,App (FalseOp ,uu____50968)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50985,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50994) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____51001 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____51021  ->
    fun r  ->
      match uu____51021 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____51029,App (TrueOp ,uu____51030)) -> mkTrue r
           | (App (FalseOp ,uu____51035),uu____51036) -> mkTrue r
           | (App (TrueOp ,uu____51041),uu____51042) -> t2
           | (uu____51047,App (Imp ,t1'::t2'::[])) ->
               let uu____51052 =
                 let uu____51059 =
                   let uu____51062 = mkAnd (t1, t1') r  in [uu____51062; t2']
                    in
                 (Imp, uu____51059)  in
               mkApp' uu____51052 r
           | uu____51065 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51090  ->
      fun r  -> match uu____51090 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51250  ->
      fun r  ->
        match uu____51250 with
        | (t1,t2) ->
            let uu____51259 =
              let uu____51266 =
                let uu____51269 =
                  let uu____51272 = mkNatToBv sz t2 r  in [uu____51272]  in
                t1 :: uu____51269  in
              (BvShl, uu____51266)  in
            mkApp' uu____51259 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51294  ->
      fun r  ->
        match uu____51294 with
        | (t1,t2) ->
            let uu____51303 =
              let uu____51310 =
                let uu____51313 =
                  let uu____51316 = mkNatToBv sz t2 r  in [uu____51316]  in
                t1 :: uu____51313  in
              (BvShr, uu____51310)  in
            mkApp' uu____51303 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51338  ->
      fun r  ->
        match uu____51338 with
        | (t1,t2) ->
            let uu____51347 =
              let uu____51354 =
                let uu____51357 =
                  let uu____51360 = mkNatToBv sz t2 r  in [uu____51360]  in
                t1 :: uu____51357  in
              (BvUdiv, uu____51354)  in
            mkApp' uu____51347 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51382  ->
      fun r  ->
        match uu____51382 with
        | (t1,t2) ->
            let uu____51391 =
              let uu____51398 =
                let uu____51401 =
                  let uu____51404 = mkNatToBv sz t2 r  in [uu____51404]  in
                t1 :: uu____51401  in
              (BvMod, uu____51398)  in
            mkApp' uu____51391 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51426  ->
      fun r  ->
        match uu____51426 with
        | (t1,t2) ->
            let uu____51435 =
              let uu____51442 =
                let uu____51445 =
                  let uu____51448 = mkNatToBv sz t2 r  in [uu____51448]  in
                t1 :: uu____51445  in
              (BvMul, uu____51442)  in
            mkApp' uu____51435 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51490  ->
    fun r  ->
      match uu____51490 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51509 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51674  ->
    fun r  ->
      match uu____51674 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51685) -> t2
           | App (FalseOp ,uu____51690) -> t3
           | uu____51695 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51696),App (TrueOp ,uu____51697)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51706),uu____51707) ->
                    let uu____51712 =
                      let uu____51717 = mkNot t1 t1.rng  in (uu____51717, t3)
                       in
                    mkImp uu____51712 r
                | (uu____51718,App (TrueOp ,uu____51719)) -> mkImp (t1, t2) r
                | (uu____51724,uu____51725) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51781 -> FStar_Pervasives_Native.None
      | Real uu____51783 -> FStar_Pervasives_Native.None
      | BoundV uu____51785 -> FStar_Pervasives_Native.None
      | FreeV uu____51787 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51811 -> true
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
            | BvUext uu____51844 -> false
            | NatToBv uu____51847 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51858,uu____51859) -> aux t2
      | Quant uu____51862 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51882 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51897 = aux t1  in
          (match uu____51897 with
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
        let uu____51935 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51935
    | FreeV fv ->
        let uu____51947 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51947
    | App (op,l) ->
        let uu____51956 = op_to_string op  in
        let uu____51958 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51956 uu____51958
    | Labeled (t1,r1,r2) ->
        let uu____51966 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51966
    | LblPos (t1,s) ->
        let uu____51973 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51973
    | Quant (qop,l,uu____51978,uu____51979,t1) ->
        let uu____51999 = print_smt_term_list_list l  in
        let uu____52001 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51999
          uu____52001
    | Let (es,body) ->
        let uu____52010 = print_smt_term_list es  in
        let uu____52012 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____52010 uu____52012

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____52019 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____52019 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____52046 =
             let uu____52048 =
               let uu____52050 = print_smt_term_list l1  in
               Prims.op_Hat uu____52050 " ] "  in
             Prims.op_Hat "; [ " uu____52048  in
           Prims.op_Hat s uu____52046) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52090  ->
        match uu____52090 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52159 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52159 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52174 =
                         let uu____52180 =
                           let uu____52182 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52182
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____52180)
                          in
                       FStar_Errors.log_issue r uu____52174);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52193) -> body
               | uu____52198 ->
                   let uu____52199 =
                     let uu____52200 =
                       let uu____52220 = all_pats_ok pats  in
                       (qop, uu____52220, wopt, vars, body)  in
                     Quant uu____52200  in
                   mk uu____52199 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52249  ->
    fun r  ->
      match uu____52249 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52295 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52295 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52328 = FStar_ST.op_Bang t1.freevars  in
        match uu____52328 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52402 ->
            (match t1.tm with
             | Integer uu____52415 -> t1
             | Real uu____52417 -> t1
             | BoundV uu____52419 -> t1
             | FreeV x ->
                 let uu____52430 = index_of1 x  in
                 (match uu____52430 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52444 =
                   let uu____52451 = FStar_List.map (aux ix) tms  in
                   (op, uu____52451)  in
                 mkApp' uu____52444 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52461 =
                   let uu____52462 =
                     let uu____52470 = aux ix t2  in (uu____52470, r1, r2)
                      in
                   Labeled uu____52462  in
                 mk uu____52461 t2.rng
             | LblPos (t2,r) ->
                 let uu____52476 =
                   let uu____52477 =
                     let uu____52483 = aux ix t2  in (uu____52483, r)  in
                   LblPos uu____52477  in
                 mk uu____52476 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52509 =
                   let uu____52529 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52550 = aux (ix + n1) body  in
                   (qop, uu____52529, wopt, vars, uu____52550)  in
                 mkQuant t1.rng false uu____52509
             | Let (es,body) ->
                 let uu____52571 =
                   FStar_List.fold_left
                     (fun uu____52591  ->
                        fun e  ->
                          match uu____52591 with
                          | (ix1,l) ->
                              let uu____52615 =
                                let uu____52618 = aux ix1 e  in uu____52618
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52615))
                     (ix, []) es
                    in
                 (match uu____52571 with
                  | (ix1,es_rev) ->
                      let uu____52634 =
                        let uu____52641 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52641)  in
                      mkLet uu____52634 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52677 -> t1
        | Real uu____52679 -> t1
        | FreeV uu____52681 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52706 =
              let uu____52713 = FStar_List.map (aux shift) tms2  in
              (op, uu____52713)  in
            mkApp' uu____52706 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52723 =
              let uu____52724 =
                let uu____52732 = aux shift t2  in (uu____52732, r1, r2)  in
              Labeled uu____52724  in
            mk uu____52723 t2.rng
        | LblPos (t2,r) ->
            let uu____52738 =
              let uu____52739 =
                let uu____52745 = aux shift t2  in (uu____52745, r)  in
              LblPos uu____52739  in
            mk uu____52738 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52777 =
              let uu____52797 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52814 = aux shift1 body  in
              (qop, uu____52797, wopt, vars, uu____52814)  in
            mkQuant t1.rng false uu____52777
        | Let (es,body) ->
            let uu____52831 =
              FStar_List.fold_left
                (fun uu____52851  ->
                   fun e  ->
                     match uu____52851 with
                     | (ix,es1) ->
                         let uu____52875 =
                           let uu____52878 = aux shift e  in uu____52878 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52875))
                (shift, []) es
               in
            (match uu____52831 with
             | (shift1,es_rev) ->
                 let uu____52894 =
                   let uu____52901 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52901)  in
                 mkLet uu____52894 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52921 = abstr [fv] t  in inst [s] uu____52921
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52951  ->
      match uu____52951 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52994 =
            let uu____53014 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____53031 = FStar_List.map fv_sort vars  in
            let uu____53034 = abstr vars body  in
            (qop, uu____53014, wopt, uu____53031, uu____53034)  in
          mkQuant r true uu____52994
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53065  ->
      match uu____53065 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53124  ->
      match uu____53124 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53199  ->
      match uu____53199 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53262  ->
      match uu____53262 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53313  ->
    fun r  ->
      match uu____53313 with
      | (bindings,body) ->
          let uu____53339 = FStar_List.split bindings  in
          (match uu____53339 with
           | (vars,es) ->
               let uu____53358 =
                 let uu____53365 = abstr vars body  in (es, uu____53365)  in
               mkLet uu____53358 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53387  ->
    match uu____53387 with
    | (nm,vars,s,tm,c) ->
        let uu____53412 =
          let uu____53426 = FStar_List.map fv_sort vars  in
          let uu____53429 = abstr vars tm  in
          (nm, uu____53426, s, uu____53429, c)  in
        DefineFun uu____53412
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53440 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53440
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53458  ->
    fun id1  ->
      match uu____53458 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53474 =
              let uu____53475 =
                let uu____53480 = mkInteger' id1 norng  in
                let uu____53481 =
                  let uu____53482 =
                    let uu____53490 = constr_id_of_sort sort  in
                    let uu____53492 =
                      let uu____53495 = mkApp (tok_name, []) norng  in
                      [uu____53495]  in
                    (uu____53490, uu____53492)  in
                  mkApp uu____53482 norng  in
                (uu____53480, uu____53481)  in
              mkEq uu____53475 norng  in
            let uu____53502 = escape a_name  in
            {
              assumption_term = uu____53474;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53502;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53528  ->
      match uu____53528 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53568 =
                        let uu____53569 =
                          let uu____53575 =
                            let uu____53577 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53577  in
                          (uu____53575, s)  in
                        mk_fv uu____53569  in
                      mkFreeV uu____53568 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53605 =
              let uu____53613 = constr_id_of_sort sort  in
              (uu____53613, [capp])  in
            mkApp uu____53605 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53622 =
              let uu____53623 =
                let uu____53634 =
                  let uu____53635 =
                    let uu____53640 = mkInteger id2 norng  in
                    (uu____53640, cid_app)  in
                  mkEq uu____53635 norng  in
                ([[capp]], bvar_names, uu____53634)  in
              mkForall rng uu____53623  in
            let uu____53649 = escape a_name  in
            {
              assumption_term = uu____53622;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53649;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53674  ->
      match uu____53674 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53707 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53707  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53742 =
              let uu____53743 =
                let uu____53749 = bvar_name i  in (uu____53749, s)  in
              mk_fv uu____53743  in
            FStar_All.pipe_left mkFreeV uu____53742  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53785  ->
                      match uu____53785 with
                      | (uu____53795,s,uu____53797) ->
                          let uu____53802 = bvar i s  in uu____53802 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53830 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53868  ->
                      match uu____53868 with
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
                              let uu____53901 =
                                let uu____53902 =
                                  let uu____53913 =
                                    let uu____53914 =
                                      let uu____53919 =
                                        let uu____53920 = bvar i s  in
                                        uu____53920 norng  in
                                      (cproj_app, uu____53919)  in
                                    mkEq uu____53914 norng  in
                                  ([[capp]], bvar_names, uu____53913)  in
                                mkForall rng uu____53902  in
                              let uu____53933 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53901;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53933;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53830 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53958  ->
      match uu____53958 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____54006  ->
                    match uu____54006 with
                    | (uu____54015,sort1,uu____54017) -> sort1))
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
              let uu____54042 =
                let uu____54047 =
                  let uu____54048 =
                    let uu____54056 = constr_id_of_sort sort  in
                    (uu____54056, [xx])  in
                  mkApp uu____54048 norng  in
                let uu____54061 =
                  let uu____54062 = FStar_Util.string_of_int id1  in
                  mkInteger uu____54062 norng  in
                (uu____54047, uu____54061)  in
              mkEq uu____54042 norng  in
            let uu____54064 =
              let uu____54083 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54147  ->
                          match uu____54147 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54177 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54177, [])
                              else
                                (let fi =
                                   let uu____54186 =
                                     let uu____54192 =
                                       let uu____54194 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54194  in
                                     (uu____54192, s)  in
                                   mk_fv uu____54186  in
                                 let uu____54198 = mkFreeV fi norng  in
                                 (uu____54198, [fi]))))
                 in
              FStar_All.pipe_right uu____54083 FStar_List.split  in
            match uu____54064 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54295 =
                    let uu____54300 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54300)  in
                  mkEq uu____54295 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54313 ->
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
          let uu____54348 =
            let uu____54351 =
              let uu____54352 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54352  in
            uu____54351 :: cdecl :: cid :: projs  in
          let uu____54355 =
            let uu____54358 =
              let uu____54361 =
                let uu____54362 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54362  in
              [uu____54361]  in
            FStar_List.append [disc] uu____54358  in
          FStar_List.append uu____54348 uu____54355
  
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
          let uu____54414 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54463  ->
                    fun s  ->
                      match uu____54463 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54508 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54519 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54519  in
                          let names2 =
                            let uu____54524 = mk_fv (nm, s)  in uu____54524
                              :: names1
                             in
                          let b =
                            let uu____54528 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54528  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54414 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54599 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54599 with
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
              (let uu____54763 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54763)
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
                               "Prims.guard_free",{ tm = BoundV uu____54809;
                                                    freevars = uu____54810;
                                                    rng = uu____54811;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54832 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54910 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54910 fv_name
          | FreeV x when fv_force x ->
              let uu____54921 =
                let uu____54923 = fv_name x  in
                Prims.op_Hat uu____54923 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54921
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54945 = op_to_string op  in
              let uu____54947 =
                let uu____54949 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54949 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54945 uu____54947
          | Labeled (t2,uu____54961,uu____54962) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54969 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54969 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54997 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54997 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____55050 ->
                         let uu____55055 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____55074 =
                                     let uu____55076 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55084 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55084) pats2
                                        in
                                     FStar_String.concat " " uu____55076  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____55074))
                            in
                         FStar_All.pipe_right uu____55055
                           (FStar_String.concat "\n")
                      in
                   let uu____55094 =
                     let uu____55098 =
                       let uu____55102 =
                         let uu____55106 = aux1 n2 names2 body  in
                         let uu____55108 =
                           let uu____55112 = weightToSmt wopt  in
                           [uu____55112; pats_str; qid]  in
                         uu____55106 :: uu____55108  in
                       binders1 :: uu____55102  in
                     (qop_to_string qop) :: uu____55098  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55094)
          | Let (es,body) ->
              let uu____55128 =
                FStar_List.fold_left
                  (fun uu____55161  ->
                     fun e  ->
                       match uu____55161 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55204 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55204  in
                           let names01 =
                             let uu____55210 = mk_fv (nm, Term_sort)  in
                             uu____55210 :: names0  in
                           let b =
                             let uu____55214 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55214  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55128 with
               | (names2,binders,n2) ->
                   let uu____55248 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55248)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55264 = FStar_Range.string_of_range t1.rng  in
            let uu____55266 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55264
              uu____55266 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55288  ->
      match uu___408_55288 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55299 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55299 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55321 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55396 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55396 (FStar_String.concat "\n")  in
            let uu____55406 = FStar_Options.keep_query_captions ()  in
            if uu____55406
            then
              let uu____55410 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55412 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55410 uu____55412
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55421 =
                let uu____55423 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55423 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55421
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55464 = caption_to_string print_captions c  in
            let uu____55466 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55464 f
              (FStar_String.concat " " l) uu____55466
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55481 = name_macro_binders arg_sorts  in
            (match uu____55481 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55505 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55505 body  in
                 let uu____55510 = caption_to_string print_captions c  in
                 let uu____55512 = strSort retsort  in
                 let uu____55514 =
                   let uu____55516 = escape f  in
                   termToSmt print_captions uu____55516 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55510 f (FStar_String.concat " " binders)
                   uu____55512 uu____55514)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55543  ->
                      match uu___409_55543 with
                      | Name n1 ->
                          let uu____55546 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55546
                      | Namespace ns ->
                          let uu____55550 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55550
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55560 =
                  let uu____55562 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55562  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55560
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55573 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55575 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55573
              fids uu____55575 n1
        | Eval t ->
            let uu____55579 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55579
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55586 -> ""
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
      let uu____55607 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55607 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55618 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55618 (FStar_String.concat "\n")

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
      let uu____55753 =
        let uu____55757 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55757
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55753 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55788 =
      let uu____55789 =
        let uu____55791 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55791  in
      let uu____55800 =
        let uu____55803 =
          let uu____55804 =
            let uu____55806 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55806  in
          (uu____55804, (BitVec_sort sz), true)  in
        [uu____55803]  in
      (uu____55789, uu____55800, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55788 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55849  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55874 =
       let uu____55876 = FStar_ST.op_Bang __range_c  in
       uu____55876 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55874);
    (let uu____55921 =
       let uu____55929 =
         let uu____55932 = mkInteger' i norng  in [uu____55932]  in
       ("Range_const", uu____55929)  in
     mkApp uu____55921 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55975 =
        let uu____55983 =
          let uu____55986 = mkInteger' i norng  in [uu____55986]  in
        ("Tm_uvar", uu____55983)  in
      mkApp uu____55975 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____56029 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____56053 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____56053 u v1 t
  
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
      let uu____56148 =
        let uu____56150 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56150  in
      let uu____56159 =
        let uu____56161 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56161  in
      elim_box true uu____56148 uu____56159 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56184 =
        let uu____56186 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56186  in
      let uu____56195 =
        let uu____56197 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56197  in
      elim_box true uu____56184 uu____56195 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56221 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56236 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56262 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56262
         | uu____56265 -> FStar_Pervasives_Native.None)
    | uu____56267 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56285::t1::t2::[]);
                       freevars = uu____56288; rng = uu____56289;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56308::t1::t2::[]);
                       freevars = uu____56311; rng = uu____56312;_}::[])
        -> let uu____56331 = mkEq (t1, t2) norng  in mkNot uu____56331 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56334; rng = uu____56335;_}::[])
        ->
        let uu____56354 =
          let uu____56359 = unboxInt t1  in
          let uu____56360 = unboxInt t2  in (uu____56359, uu____56360)  in
        mkLTE uu____56354 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56363; rng = uu____56364;_}::[])
        ->
        let uu____56383 =
          let uu____56388 = unboxInt t1  in
          let uu____56389 = unboxInt t2  in (uu____56388, uu____56389)  in
        mkLT uu____56383 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56392; rng = uu____56393;_}::[])
        ->
        let uu____56412 =
          let uu____56417 = unboxInt t1  in
          let uu____56418 = unboxInt t2  in (uu____56417, uu____56418)  in
        mkGTE uu____56412 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56421; rng = uu____56422;_}::[])
        ->
        let uu____56441 =
          let uu____56446 = unboxInt t1  in
          let uu____56447 = unboxInt t2  in (uu____56446, uu____56447)  in
        mkGT uu____56441 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56450; rng = uu____56451;_}::[])
        ->
        let uu____56470 =
          let uu____56475 = unboxBool t1  in
          let uu____56476 = unboxBool t2  in (uu____56475, uu____56476)  in
        mkAnd uu____56470 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56479; rng = uu____56480;_}::[])
        ->
        let uu____56499 =
          let uu____56504 = unboxBool t1  in
          let uu____56505 = unboxBool t2  in (uu____56504, uu____56505)  in
        mkOr uu____56499 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56507; rng = uu____56508;_}::[])
        -> let uu____56527 = unboxBool t1  in mkNot uu____56527 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56531; rng = uu____56532;_}::[])
        when
        let uu____56551 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56551 ->
        let sz =
          let uu____56558 = getBoxedInteger t0  in
          match uu____56558 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56566 -> failwith "impossible"  in
        let uu____56572 =
          let uu____56577 = unboxBitVec sz t1  in
          let uu____56578 = unboxBitVec sz t2  in (uu____56577, uu____56578)
           in
        mkBvUlt uu____56572 t.rng
    | App
        (Var
         "Prims.equals",uu____56579::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56583;
                                       rng = uu____56584;_}::uu____56585::[])
        when
        let uu____56604 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56604 ->
        let sz =
          let uu____56611 = getBoxedInteger t0  in
          match uu____56611 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56619 -> failwith "impossible"  in
        let uu____56625 =
          let uu____56630 = unboxBitVec sz t1  in
          let uu____56631 = unboxBitVec sz t2  in (uu____56630, uu____56631)
           in
        mkBvUlt uu____56625 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56636 = unboxBool t1  in
        {
          tm = (uu___1789_56636.tm);
          freevars = (uu___1789_56636.freevars);
          rng = (t.rng)
        }
    | uu____56637 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56698 = FStar_Options.unthrottle_inductives ()  in
        if uu____56698
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
    let uu____56831 =
      let uu____56832 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56832 t t.rng  in
    FStar_All.pipe_right uu____56831 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56850 =
        let uu____56858 =
          let uu____56861 = mkInteger' i norng  in [uu____56861]  in
        ("FString_const", uu____56858)  in
      mkApp uu____56850 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56892 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56892 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56939 =
         let uu____56947 =
           let uu____56950 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56950]  in
         ("SFuel", uu____56947)  in
       mkApp uu____56939 norng)
  
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
            let uu____56998 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56998
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
      let uu____57061 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____57061
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57081 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57081
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57092 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57092
  
let (dummy_sort : sort) = Sort "Dummy_sort" 