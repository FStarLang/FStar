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
    match projectee with | Bool_sort  -> true | uu____47388 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47399 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47410 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47421 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47432 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47445 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47472 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47508 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47541 -> false
  
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
        let uu____47569 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47569
    | Array (s1,s2) ->
        let uu____47574 = strSort s1  in
        let uu____47576 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47574 uu____47576
    | Arrow (s1,s2) ->
        let uu____47581 = strSort s1  in
        let uu____47583 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47581 uu____47583
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
    match projectee with | TrueOp  -> true | uu____47615 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47626 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47637 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47648 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47659 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47670 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47681 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47692 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47703 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47714 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47725 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47736 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47747 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47758 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47769 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47780 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47791 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47802 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47813 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47824 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47835 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47846 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47857 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47868 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47879 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47890 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47901 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47912 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47923 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47934 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47947 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47971 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____47993 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____48004 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____48017 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____48039 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____48050 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48210 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48234 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48258 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48289 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48339 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48396 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48479 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48524 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48570 -> false
  
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
    match projectee with | Name _0 -> true | uu____48794 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48814 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48835 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____49025 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____49048 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49114 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49173 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49194 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49224 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49265 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49286 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49312 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49340 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49351 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49362 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49373 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49391 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49428 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49439 -> false
  
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
          let uu____49613 =
            let uu____49614 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49640 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49614
            }  in
          [uu____49613]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49654 =
      let uu____49655 =
        FStar_List.collect
          (fun uu___402_49662  ->
             match uu___402_49662 with
             | Assume a -> [a.assumption_name]
             | uu____49669 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49655
      }  in
    [uu____49654]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49706  -> match uu____49706 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49726 = x  in
    match uu____49726 with | (nm,uu____49729,uu____49730) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49741 = x  in
    match uu____49741 with | (uu____49742,sort,uu____49744) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49756 = x  in
    match uu____49756 with | (uu____49758,uu____49759,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49777 = fv_name x  in
      let uu____49779 = fv_name y  in uu____49777 = uu____49779
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49813 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49824  ->
    match uu___403_49824 with
    | { tm = FreeV x; freevars = uu____49826; rng = uu____49827;_} ->
        fv_sort x
    | uu____49848 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49855  ->
    match uu___404_49855 with
    | { tm = FreeV fv; freevars = uu____49857; rng = uu____49858;_} -> fv
    | uu____49879 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49907 -> []
    | Real uu____49917 -> []
    | BoundV uu____49927 -> []
    | FreeV fv -> [fv]
    | App (uu____49962,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49976,uu____49977,uu____49978,uu____49979,t1) ->
        freevars t1
    | Labeled (t1,uu____50000,uu____50001) -> freevars t1
    | LblPos (t1,uu____50005) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____50028 = FStar_ST.op_Bang t.freevars  in
    match uu____50028 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50126 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50126  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50205  ->
    match uu___405_50205 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50215  ->
    match uu___406_50215 with
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
        let uu____50251 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50251
    | NatToBv n1 ->
        let uu____50256 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50256
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50270  ->
    match uu___407_50270 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50280 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50280
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50302 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50302
    | FreeV x ->
        let uu____50314 = fv_name x  in
        let uu____50316 =
          let uu____50318 =
            let uu____50320 = fv_sort x  in strSort uu____50320  in
          Prims.op_Hat ":" uu____50318  in
        Prims.op_Hat uu____50314 uu____50316
    | App (op,tms) ->
        let uu____50328 =
          let uu____50330 = op_to_string op  in
          let uu____50332 =
            let uu____50334 =
              let uu____50336 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50336 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50334 ")"  in
          Prims.op_Hat uu____50330 uu____50332  in
        Prims.op_Hat "(" uu____50328
    | Labeled (t1,r1,r2) ->
        let uu____50353 = hash_of_term t1  in
        let uu____50355 =
          let uu____50357 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50357  in
        Prims.op_Hat uu____50353 uu____50355
    | LblPos (t1,r) ->
        let uu____50363 =
          let uu____50365 = hash_of_term t1  in
          Prims.op_Hat uu____50365
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50363
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50393 =
          let uu____50395 =
            let uu____50397 =
              let uu____50399 =
                let uu____50401 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50401 (FStar_String.concat " ")
                 in
              let uu____50411 =
                let uu____50413 =
                  let uu____50415 = hash_of_term body  in
                  let uu____50417 =
                    let uu____50419 =
                      let uu____50421 = weightToSmt wopt  in
                      let uu____50423 =
                        let uu____50425 =
                          let uu____50427 =
                            let uu____50429 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50448 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50448
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50429
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50427 "))"  in
                        Prims.op_Hat " " uu____50425  in
                      Prims.op_Hat uu____50421 uu____50423  in
                    Prims.op_Hat " " uu____50419  in
                  Prims.op_Hat uu____50415 uu____50417  in
                Prims.op_Hat ")(! " uu____50413  in
              Prims.op_Hat uu____50399 uu____50411  in
            Prims.op_Hat " (" uu____50397  in
          Prims.op_Hat (qop_to_string qop) uu____50395  in
        Prims.op_Hat "(" uu____50393
    | Let (es,body) ->
        let uu____50475 =
          let uu____50477 =
            let uu____50479 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50479 (FStar_String.concat " ")  in
          let uu____50489 =
            let uu____50491 =
              let uu____50493 = hash_of_term body  in
              Prims.op_Hat uu____50493 ")"  in
            Prims.op_Hat ") " uu____50491  in
          Prims.op_Hat uu____50477 uu____50489  in
        Prims.op_Hat "(let (" uu____50475

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50554 =
      let uu____50556 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50556  in
    mkBoxFunctions uu____50554
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50581 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50581 = "Box") &&
        (let uu____50588 =
           let uu____50590 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50590  in
         Prims.op_Negation uu____50588)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50614 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50614; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50700 =
        let uu____50701 = FStar_Util.ensure_decimal i  in Integer uu____50701
         in
      mk uu____50700 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50716 = FStar_Util.string_of_int i  in
      mkInteger uu____50716 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50794  ->
    fun r  -> match uu____50794 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50824) -> mkFalse r
      | App (FalseOp ,uu____50829) -> mkTrue r
      | uu____50834 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50850  ->
    fun r  ->
      match uu____50850 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50858),uu____50859) -> t2
           | (uu____50864,App (TrueOp ,uu____50865)) -> t1
           | (App (FalseOp ,uu____50870),uu____50871) -> mkFalse r
           | (uu____50876,App (FalseOp ,uu____50877)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50894,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50903) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50910 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50930  ->
    fun r  ->
      match uu____50930 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50938),uu____50939) -> mkTrue r
           | (uu____50944,App (TrueOp ,uu____50945)) -> mkTrue r
           | (App (FalseOp ,uu____50950),uu____50951) -> t2
           | (uu____50956,App (FalseOp ,uu____50957)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50974,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50983) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____50990 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____51010  ->
    fun r  ->
      match uu____51010 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____51018,App (TrueOp ,uu____51019)) -> mkTrue r
           | (App (FalseOp ,uu____51024),uu____51025) -> mkTrue r
           | (App (TrueOp ,uu____51030),uu____51031) -> t2
           | (uu____51036,App (Imp ,t1'::t2'::[])) ->
               let uu____51041 =
                 let uu____51048 =
                   let uu____51051 = mkAnd (t1, t1') r  in [uu____51051; t2']
                    in
                 (Imp, uu____51048)  in
               mkApp' uu____51041 r
           | uu____51054 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51079  ->
      fun r  -> match uu____51079 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51239  ->
      fun r  ->
        match uu____51239 with
        | (t1,t2) ->
            let uu____51248 =
              let uu____51255 =
                let uu____51258 =
                  let uu____51261 = mkNatToBv sz t2 r  in [uu____51261]  in
                t1 :: uu____51258  in
              (BvShl, uu____51255)  in
            mkApp' uu____51248 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51283  ->
      fun r  ->
        match uu____51283 with
        | (t1,t2) ->
            let uu____51292 =
              let uu____51299 =
                let uu____51302 =
                  let uu____51305 = mkNatToBv sz t2 r  in [uu____51305]  in
                t1 :: uu____51302  in
              (BvShr, uu____51299)  in
            mkApp' uu____51292 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51327  ->
      fun r  ->
        match uu____51327 with
        | (t1,t2) ->
            let uu____51336 =
              let uu____51343 =
                let uu____51346 =
                  let uu____51349 = mkNatToBv sz t2 r  in [uu____51349]  in
                t1 :: uu____51346  in
              (BvUdiv, uu____51343)  in
            mkApp' uu____51336 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51371  ->
      fun r  ->
        match uu____51371 with
        | (t1,t2) ->
            let uu____51380 =
              let uu____51387 =
                let uu____51390 =
                  let uu____51393 = mkNatToBv sz t2 r  in [uu____51393]  in
                t1 :: uu____51390  in
              (BvMod, uu____51387)  in
            mkApp' uu____51380 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51415  ->
      fun r  ->
        match uu____51415 with
        | (t1,t2) ->
            let uu____51424 =
              let uu____51431 =
                let uu____51434 =
                  let uu____51437 = mkNatToBv sz t2 r  in [uu____51437]  in
                t1 :: uu____51434  in
              (BvMul, uu____51431)  in
            mkApp' uu____51424 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51479  ->
    fun r  ->
      match uu____51479 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51498 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51663  ->
    fun r  ->
      match uu____51663 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51674) -> t2
           | App (FalseOp ,uu____51679) -> t3
           | uu____51684 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51685),App (TrueOp ,uu____51686)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51695),uu____51696) ->
                    let uu____51701 =
                      let uu____51706 = mkNot t1 t1.rng  in (uu____51706, t3)
                       in
                    mkImp uu____51701 r
                | (uu____51707,App (TrueOp ,uu____51708)) -> mkImp (t1, t2) r
                | (uu____51713,uu____51714) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51770 -> FStar_Pervasives_Native.None
      | Real uu____51772 -> FStar_Pervasives_Native.None
      | BoundV uu____51774 -> FStar_Pervasives_Native.None
      | FreeV uu____51776 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51800 -> true
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
            | BvUext uu____51833 -> false
            | NatToBv uu____51836 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51847,uu____51848) -> aux t2
      | Quant uu____51851 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51871 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51886 = aux t1  in
          (match uu____51886 with
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
        let uu____51924 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51924
    | FreeV fv ->
        let uu____51936 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51936
    | App (op,l) ->
        let uu____51945 = op_to_string op  in
        let uu____51947 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51945 uu____51947
    | Labeled (t1,r1,r2) ->
        let uu____51955 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51955
    | LblPos (t1,s) ->
        let uu____51962 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51962
    | Quant (qop,l,uu____51967,uu____51968,t1) ->
        let uu____51988 = print_smt_term_list_list l  in
        let uu____51990 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51988
          uu____51990
    | Let (es,body) ->
        let uu____51999 = print_smt_term_list es  in
        let uu____52001 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____51999 uu____52001

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____52008 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____52008 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____52035 =
             let uu____52037 =
               let uu____52039 = print_smt_term_list l1  in
               Prims.op_Hat uu____52039 " ] "  in
             Prims.op_Hat "; [ " uu____52037  in
           Prims.op_Hat s uu____52035) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52079  ->
        match uu____52079 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52148 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52148 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52163 =
                         let uu____52169 =
                           let uu____52171 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52171
                            in
                         (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                           uu____52169)
                          in
                       FStar_Errors.log_issue r uu____52163);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52182) -> body
               | uu____52187 ->
                   let uu____52188 =
                     let uu____52189 =
                       let uu____52209 = all_pats_ok pats  in
                       (qop, uu____52209, wopt, vars, body)  in
                     Quant uu____52189  in
                   mk uu____52188 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52238  ->
    fun r  ->
      match uu____52238 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52284 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52284 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52317 = FStar_ST.op_Bang t1.freevars  in
        match uu____52317 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52391 ->
            (match t1.tm with
             | Integer uu____52404 -> t1
             | Real uu____52406 -> t1
             | BoundV uu____52408 -> t1
             | FreeV x ->
                 let uu____52419 = index_of1 x  in
                 (match uu____52419 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52433 =
                   let uu____52440 = FStar_List.map (aux ix) tms  in
                   (op, uu____52440)  in
                 mkApp' uu____52433 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52450 =
                   let uu____52451 =
                     let uu____52459 = aux ix t2  in (uu____52459, r1, r2)
                      in
                   Labeled uu____52451  in
                 mk uu____52450 t2.rng
             | LblPos (t2,r) ->
                 let uu____52465 =
                   let uu____52466 =
                     let uu____52472 = aux ix t2  in (uu____52472, r)  in
                   LblPos uu____52466  in
                 mk uu____52465 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52498 =
                   let uu____52518 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52539 = aux (ix + n1) body  in
                   (qop, uu____52518, wopt, vars, uu____52539)  in
                 mkQuant t1.rng false uu____52498
             | Let (es,body) ->
                 let uu____52560 =
                   FStar_List.fold_left
                     (fun uu____52580  ->
                        fun e  ->
                          match uu____52580 with
                          | (ix1,l) ->
                              let uu____52604 =
                                let uu____52607 = aux ix1 e  in uu____52607
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52604))
                     (ix, []) es
                    in
                 (match uu____52560 with
                  | (ix1,es_rev) ->
                      let uu____52623 =
                        let uu____52630 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52630)  in
                      mkLet uu____52623 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52666 -> t1
        | Real uu____52668 -> t1
        | FreeV uu____52670 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52695 =
              let uu____52702 = FStar_List.map (aux shift) tms2  in
              (op, uu____52702)  in
            mkApp' uu____52695 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52712 =
              let uu____52713 =
                let uu____52721 = aux shift t2  in (uu____52721, r1, r2)  in
              Labeled uu____52713  in
            mk uu____52712 t2.rng
        | LblPos (t2,r) ->
            let uu____52727 =
              let uu____52728 =
                let uu____52734 = aux shift t2  in (uu____52734, r)  in
              LblPos uu____52728  in
            mk uu____52727 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52766 =
              let uu____52786 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52803 = aux shift1 body  in
              (qop, uu____52786, wopt, vars, uu____52803)  in
            mkQuant t1.rng false uu____52766
        | Let (es,body) ->
            let uu____52820 =
              FStar_List.fold_left
                (fun uu____52840  ->
                   fun e  ->
                     match uu____52840 with
                     | (ix,es1) ->
                         let uu____52864 =
                           let uu____52867 = aux shift e  in uu____52867 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52864))
                (shift, []) es
               in
            (match uu____52820 with
             | (shift1,es_rev) ->
                 let uu____52883 =
                   let uu____52890 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52890)  in
                 mkLet uu____52883 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52910 = abstr [fv] t  in inst [s] uu____52910
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52940  ->
      match uu____52940 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52983 =
            let uu____53003 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____53020 = FStar_List.map fv_sort vars  in
            let uu____53023 = abstr vars body  in
            (qop, uu____53003, wopt, uu____53020, uu____53023)  in
          mkQuant r true uu____52983
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53054  ->
      match uu____53054 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53113  ->
      match uu____53113 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53188  ->
      match uu____53188 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53251  ->
      match uu____53251 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53302  ->
    fun r  ->
      match uu____53302 with
      | (bindings,body) ->
          let uu____53328 = FStar_List.split bindings  in
          (match uu____53328 with
           | (vars,es) ->
               let uu____53347 =
                 let uu____53354 = abstr vars body  in (es, uu____53354)  in
               mkLet uu____53347 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53376  ->
    match uu____53376 with
    | (nm,vars,s,tm,c) ->
        let uu____53401 =
          let uu____53415 = FStar_List.map fv_sort vars  in
          let uu____53418 = abstr vars tm  in
          (nm, uu____53415, s, uu____53418, c)  in
        DefineFun uu____53401
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53429 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53429
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53447  ->
    fun id1  ->
      match uu____53447 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53463 =
              let uu____53464 =
                let uu____53469 = mkInteger' id1 norng  in
                let uu____53470 =
                  let uu____53471 =
                    let uu____53479 = constr_id_of_sort sort  in
                    let uu____53481 =
                      let uu____53484 = mkApp (tok_name, []) norng  in
                      [uu____53484]  in
                    (uu____53479, uu____53481)  in
                  mkApp uu____53471 norng  in
                (uu____53469, uu____53470)  in
              mkEq uu____53464 norng  in
            let uu____53491 = escape a_name  in
            {
              assumption_term = uu____53463;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53491;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53517  ->
      match uu____53517 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53557 =
                        let uu____53558 =
                          let uu____53564 =
                            let uu____53566 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53566  in
                          (uu____53564, s)  in
                        mk_fv uu____53558  in
                      mkFreeV uu____53557 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53594 =
              let uu____53602 = constr_id_of_sort sort  in
              (uu____53602, [capp])  in
            mkApp uu____53594 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53611 =
              let uu____53612 =
                let uu____53623 =
                  let uu____53624 =
                    let uu____53629 = mkInteger id2 norng  in
                    (uu____53629, cid_app)  in
                  mkEq uu____53624 norng  in
                ([[capp]], bvar_names, uu____53623)  in
              mkForall rng uu____53612  in
            let uu____53638 = escape a_name  in
            {
              assumption_term = uu____53611;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53638;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53663  ->
      match uu____53663 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53696 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53696  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53731 =
              let uu____53732 =
                let uu____53738 = bvar_name i  in (uu____53738, s)  in
              mk_fv uu____53732  in
            FStar_All.pipe_left mkFreeV uu____53731  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53774  ->
                      match uu____53774 with
                      | (uu____53784,s,uu____53786) ->
                          let uu____53791 = bvar i s  in uu____53791 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53819 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53857  ->
                      match uu____53857 with
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
                              let uu____53890 =
                                let uu____53891 =
                                  let uu____53902 =
                                    let uu____53903 =
                                      let uu____53908 =
                                        let uu____53909 = bvar i s  in
                                        uu____53909 norng  in
                                      (cproj_app, uu____53908)  in
                                    mkEq uu____53903 norng  in
                                  ([[capp]], bvar_names, uu____53902)  in
                                mkForall rng uu____53891  in
                              let uu____53922 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53890;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53922;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53819 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53947  ->
      match uu____53947 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____53995  ->
                    match uu____53995 with
                    | (uu____54004,sort1,uu____54006) -> sort1))
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
              let uu____54031 =
                let uu____54036 =
                  let uu____54037 =
                    let uu____54045 = constr_id_of_sort sort  in
                    (uu____54045, [xx])  in
                  mkApp uu____54037 norng  in
                let uu____54050 =
                  let uu____54051 = FStar_Util.string_of_int id1  in
                  mkInteger uu____54051 norng  in
                (uu____54036, uu____54050)  in
              mkEq uu____54031 norng  in
            let uu____54053 =
              let uu____54072 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54136  ->
                          match uu____54136 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54166 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54166, [])
                              else
                                (let fi =
                                   let uu____54175 =
                                     let uu____54181 =
                                       let uu____54183 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54183  in
                                     (uu____54181, s)  in
                                   mk_fv uu____54175  in
                                 let uu____54187 = mkFreeV fi norng  in
                                 (uu____54187, [fi]))))
                 in
              FStar_All.pipe_right uu____54072 FStar_List.split  in
            match uu____54053 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54284 =
                    let uu____54289 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54289)  in
                  mkEq uu____54284 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54302 ->
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
          let uu____54337 =
            let uu____54340 =
              let uu____54341 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54341  in
            uu____54340 :: cdecl :: cid :: projs  in
          let uu____54344 =
            let uu____54347 =
              let uu____54350 =
                let uu____54351 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54351  in
              [uu____54350]  in
            FStar_List.append [disc] uu____54347  in
          FStar_List.append uu____54337 uu____54344
  
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
          let uu____54403 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54452  ->
                    fun s  ->
                      match uu____54452 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54497 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54508 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54508  in
                          let names2 =
                            let uu____54513 = mk_fv (nm, s)  in uu____54513
                              :: names1
                             in
                          let b =
                            let uu____54517 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54517  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54403 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54588 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54588 with
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
              (let uu____54752 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54752)
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
                               "Prims.guard_free",{ tm = BoundV uu____54798;
                                                    freevars = uu____54799;
                                                    rng = uu____54800;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54821 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54899 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54899 fv_name
          | FreeV x when fv_force x ->
              let uu____54910 =
                let uu____54912 = fv_name x  in
                Prims.op_Hat uu____54912 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54910
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54934 = op_to_string op  in
              let uu____54936 =
                let uu____54938 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54938 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54934 uu____54936
          | Labeled (t2,uu____54950,uu____54951) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54958 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54958 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54986 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54986 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____55039 ->
                         let uu____55044 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____55063 =
                                     let uu____55065 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55073 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55073) pats2
                                        in
                                     FStar_String.concat " " uu____55065  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____55063))
                            in
                         FStar_All.pipe_right uu____55044
                           (FStar_String.concat "\n")
                      in
                   let uu____55083 =
                     let uu____55087 =
                       let uu____55091 =
                         let uu____55095 = aux1 n2 names2 body  in
                         let uu____55097 =
                           let uu____55101 = weightToSmt wopt  in
                           [uu____55101; pats_str; qid]  in
                         uu____55095 :: uu____55097  in
                       binders1 :: uu____55091  in
                     (qop_to_string qop) :: uu____55087  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55083)
          | Let (es,body) ->
              let uu____55117 =
                FStar_List.fold_left
                  (fun uu____55150  ->
                     fun e  ->
                       match uu____55150 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55193 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55193  in
                           let names01 =
                             let uu____55199 = mk_fv (nm, Term_sort)  in
                             uu____55199 :: names0  in
                           let b =
                             let uu____55203 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55203  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55117 with
               | (names2,binders,n2) ->
                   let uu____55237 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55237)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55253 = FStar_Range.string_of_range t1.rng  in
            let uu____55255 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55253
              uu____55255 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55277  ->
      match uu___408_55277 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55288 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55288 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55310 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55385 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55385 (FStar_String.concat "\n")  in
            let uu____55395 = FStar_Options.keep_query_captions ()  in
            if uu____55395
            then
              let uu____55399 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55401 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55399 uu____55401
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55410 =
                let uu____55412 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55412 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55410
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55453 = caption_to_string print_captions c  in
            let uu____55455 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55453 f
              (FStar_String.concat " " l) uu____55455
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55470 = name_macro_binders arg_sorts  in
            (match uu____55470 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55494 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55494 body  in
                 let uu____55499 = caption_to_string print_captions c  in
                 let uu____55501 = strSort retsort  in
                 let uu____55503 =
                   let uu____55505 = escape f  in
                   termToSmt print_captions uu____55505 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55499 f (FStar_String.concat " " binders)
                   uu____55501 uu____55503)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55532  ->
                      match uu___409_55532 with
                      | Name n1 ->
                          let uu____55535 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55535
                      | Namespace ns ->
                          let uu____55539 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55539
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55549 =
                  let uu____55551 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55551  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55549
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55562 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55564 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55562
              fids uu____55564 n1
        | Eval t ->
            let uu____55568 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55568
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55575 -> ""
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
      let uu____55596 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55596 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55607 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55607 (FStar_String.concat "\n")

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
      let uu____55742 =
        let uu____55746 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55746
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55742 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55777 =
      let uu____55778 =
        let uu____55780 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55780  in
      let uu____55789 =
        let uu____55792 =
          let uu____55793 =
            let uu____55795 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55795  in
          (uu____55793, (BitVec_sort sz), true)  in
        [uu____55792]  in
      (uu____55778, uu____55789, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55777 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55838  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55863 =
       let uu____55865 = FStar_ST.op_Bang __range_c  in
       uu____55865 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55863);
    (let uu____55910 =
       let uu____55918 =
         let uu____55921 = mkInteger' i norng  in [uu____55921]  in
       ("Range_const", uu____55918)  in
     mkApp uu____55910 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55964 =
        let uu____55972 =
          let uu____55975 = mkInteger' i norng  in [uu____55975]  in
        ("Tm_uvar", uu____55972)  in
      mkApp uu____55964 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____56018 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____56042 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____56042 u v1 t
  
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
      let uu____56137 =
        let uu____56139 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56139  in
      let uu____56148 =
        let uu____56150 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56150  in
      elim_box true uu____56137 uu____56148 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56173 =
        let uu____56175 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56175  in
      let uu____56184 =
        let uu____56186 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56186  in
      elim_box true uu____56173 uu____56184 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56210 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56225 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56251 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56251
         | uu____56254 -> FStar_Pervasives_Native.None)
    | uu____56256 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56274::t1::t2::[]);
                       freevars = uu____56277; rng = uu____56278;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56297::t1::t2::[]);
                       freevars = uu____56300; rng = uu____56301;_}::[])
        -> let uu____56320 = mkEq (t1, t2) norng  in mkNot uu____56320 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56323; rng = uu____56324;_}::[])
        ->
        let uu____56343 =
          let uu____56348 = unboxInt t1  in
          let uu____56349 = unboxInt t2  in (uu____56348, uu____56349)  in
        mkLTE uu____56343 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56352; rng = uu____56353;_}::[])
        ->
        let uu____56372 =
          let uu____56377 = unboxInt t1  in
          let uu____56378 = unboxInt t2  in (uu____56377, uu____56378)  in
        mkLT uu____56372 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56381; rng = uu____56382;_}::[])
        ->
        let uu____56401 =
          let uu____56406 = unboxInt t1  in
          let uu____56407 = unboxInt t2  in (uu____56406, uu____56407)  in
        mkGTE uu____56401 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56410; rng = uu____56411;_}::[])
        ->
        let uu____56430 =
          let uu____56435 = unboxInt t1  in
          let uu____56436 = unboxInt t2  in (uu____56435, uu____56436)  in
        mkGT uu____56430 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56439; rng = uu____56440;_}::[])
        ->
        let uu____56459 =
          let uu____56464 = unboxBool t1  in
          let uu____56465 = unboxBool t2  in (uu____56464, uu____56465)  in
        mkAnd uu____56459 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56468; rng = uu____56469;_}::[])
        ->
        let uu____56488 =
          let uu____56493 = unboxBool t1  in
          let uu____56494 = unboxBool t2  in (uu____56493, uu____56494)  in
        mkOr uu____56488 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56496; rng = uu____56497;_}::[])
        -> let uu____56516 = unboxBool t1  in mkNot uu____56516 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56520; rng = uu____56521;_}::[])
        when
        let uu____56540 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56540 ->
        let sz =
          let uu____56547 = getBoxedInteger t0  in
          match uu____56547 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56555 -> failwith "impossible"  in
        let uu____56561 =
          let uu____56566 = unboxBitVec sz t1  in
          let uu____56567 = unboxBitVec sz t2  in (uu____56566, uu____56567)
           in
        mkBvUlt uu____56561 t.rng
    | App
        (Var
         "Prims.equals",uu____56568::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56572;
                                       rng = uu____56573;_}::uu____56574::[])
        when
        let uu____56593 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56593 ->
        let sz =
          let uu____56600 = getBoxedInteger t0  in
          match uu____56600 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56608 -> failwith "impossible"  in
        let uu____56614 =
          let uu____56619 = unboxBitVec sz t1  in
          let uu____56620 = unboxBitVec sz t2  in (uu____56619, uu____56620)
           in
        mkBvUlt uu____56614 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56625 = unboxBool t1  in
        {
          tm = (uu___1789_56625.tm);
          freevars = (uu___1789_56625.freevars);
          rng = (t.rng)
        }
    | uu____56626 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56687 = FStar_Options.unthrottle_inductives ()  in
        if uu____56687
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
    let uu____56820 =
      let uu____56821 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56821 t t.rng  in
    FStar_All.pipe_right uu____56820 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56839 =
        let uu____56847 =
          let uu____56850 = mkInteger' i norng  in [uu____56850]  in
        ("FString_const", uu____56847)  in
      mkApp uu____56839 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56881 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56881 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56928 =
         let uu____56936 =
           let uu____56939 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56939]  in
         ("SFuel", uu____56936)  in
       mkApp uu____56928 norng)
  
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
            let uu____56987 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56987
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
      let uu____57050 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____57050
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57070 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57070
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57081 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57081
  
let (dummy_sort : sort) = Sort "Dummy_sort" 