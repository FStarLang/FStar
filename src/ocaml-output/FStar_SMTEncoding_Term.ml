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
    match projectee with | Bool_sort  -> true | uu____47394 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____47405 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____47416 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____47427 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____47438 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____47451 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47478 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____47514 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____47547 -> false
  
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
        let uu____47575 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____47575
    | Array (s1,s2) ->
        let uu____47580 = strSort s1  in
        let uu____47582 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____47580 uu____47582
    | Arrow (s1,s2) ->
        let uu____47587 = strSort s1  in
        let uu____47589 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____47587 uu____47589
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
    match projectee with | TrueOp  -> true | uu____47621 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____47632 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____47643 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____47654 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____47665 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____47676 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____47687 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____47698 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____47709 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____47720 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____47731 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____47742 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____47753 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____47764 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____47775 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____47786 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____47797 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____47808 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____47819 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____47830 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____47841 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____47852 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____47863 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____47874 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____47885 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____47896 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____47907 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____47918 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____47929 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____47940 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____47953 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____47977 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____47999 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____48010 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____48023 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____48045 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____48056 -> false
  
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
    match projectee with | Integer _0 -> true | uu____48216 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____48240 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____48264 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____48295 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____48345 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____48402 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____48485 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____48530 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____48576 -> false
  
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
    match projectee with | Name _0 -> true | uu____48800 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____48820 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____48841 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____49031 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____49054 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____49120 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____49179 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____49200 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____49230 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____49271 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____49292 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____49318 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____49346 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____49357 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____49368 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____49379 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____49397 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____49434 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____49445 -> false
  
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
          let uu____49619 =
            let uu____49620 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____49646 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____49620
            }  in
          [uu____49619]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____49660 =
      let uu____49661 =
        FStar_List.collect
          (fun uu___402_49668  ->
             match uu___402_49668 with
             | Assume a -> [a.assumption_name]
             | uu____49675 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____49661
      }  in
    [uu____49660]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____49712  -> match uu____49712 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____49732 = x  in
    match uu____49732 with | (nm,uu____49735,uu____49736) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____49747 = x  in
    match uu____49747 with | (uu____49748,sort,uu____49750) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____49762 = x  in
    match uu____49762 with | (uu____49764,uu____49765,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____49783 = fv_name x  in
      let uu____49785 = fv_name y  in uu____49783 = uu____49785
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____49819 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_49830  ->
    match uu___403_49830 with
    | { tm = FreeV x; freevars = uu____49832; rng = uu____49833;_} ->
        fv_sort x
    | uu____49854 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_49861  ->
    match uu___404_49861 with
    | { tm = FreeV fv; freevars = uu____49863; rng = uu____49864;_} -> fv
    | uu____49885 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____49913 -> []
    | Real uu____49923 -> []
    | BoundV uu____49933 -> []
    | FreeV fv -> [fv]
    | App (uu____49968,tms) -> FStar_List.collect freevars tms
    | Quant (uu____49982,uu____49983,uu____49984,uu____49985,t1) ->
        freevars t1
    | Labeled (t1,uu____50006,uu____50007) -> freevars t1
    | LblPos (t1,uu____50011) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____50034 = FStar_ST.op_Bang t.freevars  in
    match uu____50034 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____50132 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____50132  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_50211  ->
    match uu___405_50211 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_50221  ->
    match uu___406_50221 with
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
        let uu____50257 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____50257
    | NatToBv n1 ->
        let uu____50262 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____50262
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_50276  ->
    match uu___407_50276 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____50286 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____50286
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____50308 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____50308
    | FreeV x ->
        let uu____50320 = fv_name x  in
        let uu____50322 =
          let uu____50324 =
            let uu____50326 = fv_sort x  in strSort uu____50326  in
          Prims.op_Hat ":" uu____50324  in
        Prims.op_Hat uu____50320 uu____50322
    | App (op,tms) ->
        let uu____50334 =
          let uu____50336 = op_to_string op  in
          let uu____50338 =
            let uu____50340 =
              let uu____50342 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____50342 (FStar_String.concat " ")  in
            Prims.op_Hat uu____50340 ")"  in
          Prims.op_Hat uu____50336 uu____50338  in
        Prims.op_Hat "(" uu____50334
    | Labeled (t1,r1,r2) ->
        let uu____50359 = hash_of_term t1  in
        let uu____50361 =
          let uu____50363 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____50363  in
        Prims.op_Hat uu____50359 uu____50361
    | LblPos (t1,r) ->
        let uu____50369 =
          let uu____50371 = hash_of_term t1  in
          Prims.op_Hat uu____50371
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____50369
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____50399 =
          let uu____50401 =
            let uu____50403 =
              let uu____50405 =
                let uu____50407 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____50407 (FStar_String.concat " ")
                 in
              let uu____50417 =
                let uu____50419 =
                  let uu____50421 = hash_of_term body  in
                  let uu____50423 =
                    let uu____50425 =
                      let uu____50427 = weightToSmt wopt  in
                      let uu____50429 =
                        let uu____50431 =
                          let uu____50433 =
                            let uu____50435 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____50454 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____50454
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____50435
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____50433 "))"  in
                        Prims.op_Hat " " uu____50431  in
                      Prims.op_Hat uu____50427 uu____50429  in
                    Prims.op_Hat " " uu____50425  in
                  Prims.op_Hat uu____50421 uu____50423  in
                Prims.op_Hat ")(! " uu____50419  in
              Prims.op_Hat uu____50405 uu____50417  in
            Prims.op_Hat " (" uu____50403  in
          Prims.op_Hat (qop_to_string qop) uu____50401  in
        Prims.op_Hat "(" uu____50399
    | Let (es,body) ->
        let uu____50481 =
          let uu____50483 =
            let uu____50485 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____50485 (FStar_String.concat " ")  in
          let uu____50495 =
            let uu____50497 =
              let uu____50499 = hash_of_term body  in
              Prims.op_Hat uu____50499 ")"  in
            Prims.op_Hat ") " uu____50497  in
          Prims.op_Hat uu____50483 uu____50495  in
        Prims.op_Hat "(let (" uu____50481

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____50560 =
      let uu____50562 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____50562  in
    mkBoxFunctions uu____50560
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____50587 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____50587 = "Box") &&
        (let uu____50594 =
           let uu____50596 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____50596  in
         Prims.op_Negation uu____50594)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____50620 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____50620; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50706 =
        let uu____50707 = FStar_Util.ensure_decimal i  in Integer uu____50707
         in
      mk uu____50706 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____50722 = FStar_Util.string_of_int i  in
      mkInteger uu____50722 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____50800  ->
    fun r  -> match uu____50800 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____50830) -> mkFalse r
      | App (FalseOp ,uu____50835) -> mkTrue r
      | uu____50840 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____50856  ->
    fun r  ->
      match uu____50856 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50864),uu____50865) -> t2
           | (uu____50870,App (TrueOp ,uu____50871)) -> t1
           | (App (FalseOp ,uu____50876),uu____50877) -> mkFalse r
           | (uu____50882,App (FalseOp ,uu____50883)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____50900,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____50909) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____50916 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____50936  ->
    fun r  ->
      match uu____50936 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____50944),uu____50945) -> mkTrue r
           | (uu____50950,App (TrueOp ,uu____50951)) -> mkTrue r
           | (App (FalseOp ,uu____50956),uu____50957) -> t2
           | (uu____50962,App (FalseOp ,uu____50963)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____50980,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____50989) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____50996 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____51016  ->
    fun r  ->
      match uu____51016 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____51024,App (TrueOp ,uu____51025)) -> mkTrue r
           | (App (FalseOp ,uu____51030),uu____51031) -> mkTrue r
           | (App (TrueOp ,uu____51036),uu____51037) -> t2
           | (uu____51042,App (Imp ,t1'::t2'::[])) ->
               let uu____51047 =
                 let uu____51054 =
                   let uu____51057 = mkAnd (t1, t1') r  in [uu____51057; t2']
                    in
                 (Imp, uu____51054)  in
               mkApp' uu____51047 r
           | uu____51060 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____51085  ->
      fun r  -> match uu____51085 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____51245  ->
      fun r  ->
        match uu____51245 with
        | (t1,t2) ->
            let uu____51254 =
              let uu____51261 =
                let uu____51264 =
                  let uu____51267 = mkNatToBv sz t2 r  in [uu____51267]  in
                t1 :: uu____51264  in
              (BvShl, uu____51261)  in
            mkApp' uu____51254 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51289  ->
      fun r  ->
        match uu____51289 with
        | (t1,t2) ->
            let uu____51298 =
              let uu____51305 =
                let uu____51308 =
                  let uu____51311 = mkNatToBv sz t2 r  in [uu____51311]  in
                t1 :: uu____51308  in
              (BvShr, uu____51305)  in
            mkApp' uu____51298 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51333  ->
      fun r  ->
        match uu____51333 with
        | (t1,t2) ->
            let uu____51342 =
              let uu____51349 =
                let uu____51352 =
                  let uu____51355 = mkNatToBv sz t2 r  in [uu____51355]  in
                t1 :: uu____51352  in
              (BvUdiv, uu____51349)  in
            mkApp' uu____51342 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51377  ->
      fun r  ->
        match uu____51377 with
        | (t1,t2) ->
            let uu____51386 =
              let uu____51393 =
                let uu____51396 =
                  let uu____51399 = mkNatToBv sz t2 r  in [uu____51399]  in
                t1 :: uu____51396  in
              (BvMod, uu____51393)  in
            mkApp' uu____51386 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____51421  ->
      fun r  ->
        match uu____51421 with
        | (t1,t2) ->
            let uu____51430 =
              let uu____51437 =
                let uu____51440 =
                  let uu____51443 = mkNatToBv sz t2 r  in [uu____51443]  in
                t1 :: uu____51440  in
              (BvMul, uu____51437)  in
            mkApp' uu____51430 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____51485  ->
    fun r  ->
      match uu____51485 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____51504 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____51669  ->
    fun r  ->
      match uu____51669 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____51680) -> t2
           | App (FalseOp ,uu____51685) -> t3
           | uu____51690 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____51691),App (TrueOp ,uu____51692)) ->
                    mkTrue r
                | (App (TrueOp ,uu____51701),uu____51702) ->
                    let uu____51707 =
                      let uu____51712 = mkNot t1 t1.rng  in (uu____51712, t3)
                       in
                    mkImp uu____51707 r
                | (uu____51713,App (TrueOp ,uu____51714)) -> mkImp (t1, t2) r
                | (uu____51719,uu____51720) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____51776 -> FStar_Pervasives_Native.None
      | Real uu____51778 -> FStar_Pervasives_Native.None
      | BoundV uu____51780 -> FStar_Pervasives_Native.None
      | FreeV uu____51782 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____51806 -> true
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
            | BvUext uu____51839 -> false
            | NatToBv uu____51842 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____51853,uu____51854) -> aux t2
      | Quant uu____51857 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____51877 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____51892 = aux t1  in
          (match uu____51892 with
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
        let uu____51930 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____51930
    | FreeV fv ->
        let uu____51942 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____51942
    | App (op,l) ->
        let uu____51951 = op_to_string op  in
        let uu____51953 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____51951 uu____51953
    | Labeled (t1,r1,r2) ->
        let uu____51961 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____51961
    | LblPos (t1,s) ->
        let uu____51968 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____51968
    | Quant (qop,l,uu____51973,uu____51974,t1) ->
        let uu____51994 = print_smt_term_list_list l  in
        let uu____51996 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____51994
          uu____51996
    | Let (es,body) ->
        let uu____52005 = print_smt_term_list es  in
        let uu____52007 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____52005 uu____52007

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____52014 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____52014 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____52041 =
             let uu____52043 =
               let uu____52045 = print_smt_term_list l1  in
               Prims.op_Hat uu____52045 " ] "  in
             Prims.op_Hat "; [ " uu____52043  in
           Prims.op_Hat s uu____52041) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____52085  ->
        match uu____52085 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____52154 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____52154 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____52169 =
                         let uu____52175 =
                           let uu____52177 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____52177
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____52175)
                          in
                       FStar_Errors.log_issue r uu____52169);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____52188) -> body
               | uu____52193 ->
                   let uu____52194 =
                     let uu____52195 =
                       let uu____52215 = all_pats_ok pats  in
                       (qop, uu____52215, wopt, vars, body)  in
                     Quant uu____52195  in
                   mk uu____52194 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____52244  ->
    fun r  ->
      match uu____52244 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____52290 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____52290 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____52323 = FStar_ST.op_Bang t1.freevars  in
        match uu____52323 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____52397 ->
            (match t1.tm with
             | Integer uu____52410 -> t1
             | Real uu____52412 -> t1
             | BoundV uu____52414 -> t1
             | FreeV x ->
                 let uu____52425 = index_of1 x  in
                 (match uu____52425 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____52439 =
                   let uu____52446 = FStar_List.map (aux ix) tms  in
                   (op, uu____52446)  in
                 mkApp' uu____52439 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____52456 =
                   let uu____52457 =
                     let uu____52465 = aux ix t2  in (uu____52465, r1, r2)
                      in
                   Labeled uu____52457  in
                 mk uu____52456 t2.rng
             | LblPos (t2,r) ->
                 let uu____52471 =
                   let uu____52472 =
                     let uu____52478 = aux ix t2  in (uu____52478, r)  in
                   LblPos uu____52472  in
                 mk uu____52471 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____52504 =
                   let uu____52524 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____52545 = aux (ix + n1) body  in
                   (qop, uu____52524, wopt, vars, uu____52545)  in
                 mkQuant t1.rng false uu____52504
             | Let (es,body) ->
                 let uu____52566 =
                   FStar_List.fold_left
                     (fun uu____52586  ->
                        fun e  ->
                          match uu____52586 with
                          | (ix1,l) ->
                              let uu____52610 =
                                let uu____52613 = aux ix1 e  in uu____52613
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____52610))
                     (ix, []) es
                    in
                 (match uu____52566 with
                  | (ix1,es_rev) ->
                      let uu____52629 =
                        let uu____52636 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____52636)  in
                      mkLet uu____52629 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____52672 -> t1
        | Real uu____52674 -> t1
        | FreeV uu____52676 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____52701 =
              let uu____52708 = FStar_List.map (aux shift) tms2  in
              (op, uu____52708)  in
            mkApp' uu____52701 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____52718 =
              let uu____52719 =
                let uu____52727 = aux shift t2  in (uu____52727, r1, r2)  in
              Labeled uu____52719  in
            mk uu____52718 t2.rng
        | LblPos (t2,r) ->
            let uu____52733 =
              let uu____52734 =
                let uu____52740 = aux shift t2  in (uu____52740, r)  in
              LblPos uu____52734  in
            mk uu____52733 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____52772 =
              let uu____52792 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____52809 = aux shift1 body  in
              (qop, uu____52792, wopt, vars, uu____52809)  in
            mkQuant t1.rng false uu____52772
        | Let (es,body) ->
            let uu____52826 =
              FStar_List.fold_left
                (fun uu____52846  ->
                   fun e  ->
                     match uu____52846 with
                     | (ix,es1) ->
                         let uu____52870 =
                           let uu____52873 = aux shift e  in uu____52873 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____52870))
                (shift, []) es
               in
            (match uu____52826 with
             | (shift1,es_rev) ->
                 let uu____52889 =
                   let uu____52896 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____52896)  in
                 mkLet uu____52889 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____52916 = abstr [fv] t  in inst [s] uu____52916
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____52946  ->
      match uu____52946 with
      | (qop,pats,wopt,vars,body) ->
          let uu____52989 =
            let uu____53009 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____53026 = FStar_List.map fv_sort vars  in
            let uu____53029 = abstr vars body  in
            (qop, uu____53009, wopt, uu____53026, uu____53029)  in
          mkQuant r true uu____52989
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53060  ->
      match uu____53060 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____53119  ->
      match uu____53119 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____53194  ->
      match uu____53194 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____53257  ->
      match uu____53257 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____53308  ->
    fun r  ->
      match uu____53308 with
      | (bindings,body) ->
          let uu____53334 = FStar_List.split bindings  in
          (match uu____53334 with
           | (vars,es) ->
               let uu____53353 =
                 let uu____53360 = abstr vars body  in (es, uu____53360)  in
               mkLet uu____53353 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____53382  ->
    match uu____53382 with
    | (nm,vars,s,tm,c) ->
        let uu____53407 =
          let uu____53421 = FStar_List.map fv_sort vars  in
          let uu____53424 = abstr vars tm  in
          (nm, uu____53421, s, uu____53424, c)  in
        DefineFun uu____53407
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____53435 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____53435
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____53453  ->
    fun id1  ->
      match uu____53453 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____53469 =
              let uu____53470 =
                let uu____53475 = mkInteger' id1 norng  in
                let uu____53476 =
                  let uu____53477 =
                    let uu____53485 = constr_id_of_sort sort  in
                    let uu____53487 =
                      let uu____53490 = mkApp (tok_name, []) norng  in
                      [uu____53490]  in
                    (uu____53485, uu____53487)  in
                  mkApp uu____53477 norng  in
                (uu____53475, uu____53476)  in
              mkEq uu____53470 norng  in
            let uu____53497 = escape a_name  in
            {
              assumption_term = uu____53469;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____53497;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____53523  ->
      match uu____53523 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____53563 =
                        let uu____53564 =
                          let uu____53570 =
                            let uu____53572 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____53572  in
                          (uu____53570, s)  in
                        mk_fv uu____53564  in
                      mkFreeV uu____53563 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____53600 =
              let uu____53608 = constr_id_of_sort sort  in
              (uu____53608, [capp])  in
            mkApp uu____53600 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____53617 =
              let uu____53618 =
                let uu____53629 =
                  let uu____53630 =
                    let uu____53635 = mkInteger id2 norng  in
                    (uu____53635, cid_app)  in
                  mkEq uu____53630 norng  in
                ([[capp]], bvar_names, uu____53629)  in
              mkForall rng uu____53618  in
            let uu____53644 = escape a_name  in
            {
              assumption_term = uu____53617;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____53644;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____53669  ->
      match uu____53669 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____53702 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____53702  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____53737 =
              let uu____53738 =
                let uu____53744 = bvar_name i  in (uu____53744, s)  in
              mk_fv uu____53738  in
            FStar_All.pipe_left mkFreeV uu____53737  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53780  ->
                      match uu____53780 with
                      | (uu____53790,s,uu____53792) ->
                          let uu____53797 = bvar i s  in uu____53797 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____53825 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____53863  ->
                      match uu____53863 with
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
                              let uu____53896 =
                                let uu____53897 =
                                  let uu____53908 =
                                    let uu____53909 =
                                      let uu____53914 =
                                        let uu____53915 = bvar i s  in
                                        uu____53915 norng  in
                                      (cproj_app, uu____53914)  in
                                    mkEq uu____53909 norng  in
                                  ([[capp]], bvar_names, uu____53908)  in
                                mkForall rng uu____53897  in
                              let uu____53928 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____53896;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____53928;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____53825 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____53953  ->
      match uu____53953 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____54001  ->
                    match uu____54001 with
                    | (uu____54010,sort1,uu____54012) -> sort1))
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
              let uu____54037 =
                let uu____54042 =
                  let uu____54043 =
                    let uu____54051 = constr_id_of_sort sort  in
                    (uu____54051, [xx])  in
                  mkApp uu____54043 norng  in
                let uu____54056 =
                  let uu____54057 = FStar_Util.string_of_int id1  in
                  mkInteger uu____54057 norng  in
                (uu____54042, uu____54056)  in
              mkEq uu____54037 norng  in
            let uu____54059 =
              let uu____54078 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____54142  ->
                          match uu____54142 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____54172 = mkApp (proj, [xx]) norng
                                   in
                                (uu____54172, [])
                              else
                                (let fi =
                                   let uu____54181 =
                                     let uu____54187 =
                                       let uu____54189 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____54189  in
                                     (uu____54187, s)  in
                                   mk_fv uu____54181  in
                                 let uu____54193 = mkFreeV fi norng  in
                                 (uu____54193, [fi]))))
                 in
              FStar_All.pipe_right uu____54078 FStar_List.split  in
            match uu____54059 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____54290 =
                    let uu____54295 = mkApp (name, proj_terms) norng  in
                    (xx, uu____54295)  in
                  mkEq uu____54290 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____54308 ->
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
          let uu____54343 =
            let uu____54346 =
              let uu____54347 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____54347  in
            uu____54346 :: cdecl :: cid :: projs  in
          let uu____54350 =
            let uu____54353 =
              let uu____54356 =
                let uu____54357 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____54357  in
              [uu____54356]  in
            FStar_List.append [disc] uu____54353  in
          FStar_List.append uu____54343 uu____54350
  
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
          let uu____54409 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____54458  ->
                    fun s  ->
                      match uu____54458 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____54503 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____54514 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____54514  in
                          let names2 =
                            let uu____54519 = mk_fv (nm, s)  in uu____54519
                              :: names1
                             in
                          let b =
                            let uu____54523 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____54523  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____54409 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____54594 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____54594 with
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
              (let uu____54758 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____54758)
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
                               "Prims.guard_free",{ tm = BoundV uu____54804;
                                                    freevars = uu____54805;
                                                    rng = uu____54806;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____54827 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____54905 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____54905 fv_name
          | FreeV x when fv_force x ->
              let uu____54916 =
                let uu____54918 = fv_name x  in
                Prims.op_Hat uu____54918 " Dummy_value)"  in
              Prims.op_Hat "(" uu____54916
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____54940 = op_to_string op  in
              let uu____54942 =
                let uu____54944 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____54944 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____54940 uu____54942
          | Labeled (t2,uu____54956,uu____54957) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____54964 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____54964 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____54992 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____54992 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____55045 ->
                         let uu____55050 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____55069 =
                                     let uu____55071 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____55079 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____55079) pats2
                                        in
                                     FStar_String.concat " " uu____55071  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____55069))
                            in
                         FStar_All.pipe_right uu____55050
                           (FStar_String.concat "\n")
                      in
                   let uu____55089 =
                     let uu____55093 =
                       let uu____55097 =
                         let uu____55101 = aux1 n2 names2 body  in
                         let uu____55103 =
                           let uu____55107 = weightToSmt wopt  in
                           [uu____55107; pats_str; qid]  in
                         uu____55101 :: uu____55103  in
                       binders1 :: uu____55097  in
                     (qop_to_string qop) :: uu____55093  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____55089)
          | Let (es,body) ->
              let uu____55123 =
                FStar_List.fold_left
                  (fun uu____55156  ->
                     fun e  ->
                       match uu____55156 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____55199 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____55199  in
                           let names01 =
                             let uu____55205 = mk_fv (nm, Term_sort)  in
                             uu____55205 :: names0  in
                           let b =
                             let uu____55209 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____55209  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____55123 with
               | (names2,binders,n2) ->
                   let uu____55243 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____55243)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____55259 = FStar_Range.string_of_range t1.rng  in
            let uu____55261 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____55259
              uu____55261 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_55283  ->
      match uu___408_55283 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____55294 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____55294 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____55316 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____55391 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____55391 (FStar_String.concat "\n")  in
            let uu____55401 = FStar_Options.keep_query_captions ()  in
            if uu____55401
            then
              let uu____55405 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____55407 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____55405 uu____55407
            else res
        | Caption c ->
            if print_captions
            then
              let uu____55416 =
                let uu____55418 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____55418 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____55416
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____55459 = caption_to_string print_captions c  in
            let uu____55461 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____55459 f
              (FStar_String.concat " " l) uu____55461
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____55476 = name_macro_binders arg_sorts  in
            (match uu____55476 with
             | (names1,binders) ->
                 let body1 =
                   let uu____55500 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____55500 body  in
                 let uu____55505 = caption_to_string print_captions c  in
                 let uu____55507 = strSort retsort  in
                 let uu____55509 =
                   let uu____55511 = escape f  in
                   termToSmt print_captions uu____55511 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____55505 f (FStar_String.concat " " binders)
                   uu____55507 uu____55509)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_55538  ->
                      match uu___409_55538 with
                      | Name n1 ->
                          let uu____55541 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____55541
                      | Namespace ns ->
                          let uu____55545 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____55545
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____55555 =
                  let uu____55557 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____55557  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____55555
              else ""  in
            let n1 = a.assumption_name  in
            let uu____55568 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____55570 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____55568
              fids uu____55570 n1
        | Eval t ->
            let uu____55574 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____55574
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____55581 -> ""
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
      let uu____55602 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____55602 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____55613 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____55613 (FStar_String.concat "\n")

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
      let uu____55748 =
        let uu____55752 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____55752
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____55748 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____55783 =
      let uu____55784 =
        let uu____55786 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____55786  in
      let uu____55795 =
        let uu____55798 =
          let uu____55799 =
            let uu____55801 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____55801  in
          (uu____55799, (BitVec_sort sz), true)  in
        [uu____55798]  in
      (uu____55784, uu____55795, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____55783 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____55844  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____55869 =
       let uu____55871 = FStar_ST.op_Bang __range_c  in
       uu____55871 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____55869);
    (let uu____55916 =
       let uu____55924 =
         let uu____55927 = mkInteger' i norng  in [uu____55927]  in
       ("Range_const", uu____55924)  in
     mkApp uu____55916 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____55970 =
        let uu____55978 =
          let uu____55981 = mkInteger' i norng  in [uu____55981]  in
        ("Tm_uvar", uu____55978)  in
      mkApp uu____55970 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____56024 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____56048 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____56048 u v1 t
  
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
      let uu____56143 =
        let uu____56145 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56145  in
      let uu____56154 =
        let uu____56156 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56156  in
      elim_box true uu____56143 uu____56154 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____56179 =
        let uu____56181 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____56181  in
      let uu____56190 =
        let uu____56192 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____56192  in
      elim_box true uu____56179 uu____56190 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____56216 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____56231 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____56257 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____56257
         | uu____56260 -> FStar_Pervasives_Native.None)
    | uu____56262 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____56280::t1::t2::[]);
                       freevars = uu____56283; rng = uu____56284;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____56303::t1::t2::[]);
                       freevars = uu____56306; rng = uu____56307;_}::[])
        -> let uu____56326 = mkEq (t1, t2) norng  in mkNot uu____56326 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____56329; rng = uu____56330;_}::[])
        ->
        let uu____56349 =
          let uu____56354 = unboxInt t1  in
          let uu____56355 = unboxInt t2  in (uu____56354, uu____56355)  in
        mkLTE uu____56349 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____56358; rng = uu____56359;_}::[])
        ->
        let uu____56378 =
          let uu____56383 = unboxInt t1  in
          let uu____56384 = unboxInt t2  in (uu____56383, uu____56384)  in
        mkLT uu____56378 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____56387; rng = uu____56388;_}::[])
        ->
        let uu____56407 =
          let uu____56412 = unboxInt t1  in
          let uu____56413 = unboxInt t2  in (uu____56412, uu____56413)  in
        mkGTE uu____56407 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____56416; rng = uu____56417;_}::[])
        ->
        let uu____56436 =
          let uu____56441 = unboxInt t1  in
          let uu____56442 = unboxInt t2  in (uu____56441, uu____56442)  in
        mkGT uu____56436 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____56445; rng = uu____56446;_}::[])
        ->
        let uu____56465 =
          let uu____56470 = unboxBool t1  in
          let uu____56471 = unboxBool t2  in (uu____56470, uu____56471)  in
        mkAnd uu____56465 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____56474; rng = uu____56475;_}::[])
        ->
        let uu____56494 =
          let uu____56499 = unboxBool t1  in
          let uu____56500 = unboxBool t2  in (uu____56499, uu____56500)  in
        mkOr uu____56494 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____56502; rng = uu____56503;_}::[])
        -> let uu____56522 = unboxBool t1  in mkNot uu____56522 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____56526; rng = uu____56527;_}::[])
        when
        let uu____56546 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56546 ->
        let sz =
          let uu____56553 = getBoxedInteger t0  in
          match uu____56553 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56561 -> failwith "impossible"  in
        let uu____56567 =
          let uu____56572 = unboxBitVec sz t1  in
          let uu____56573 = unboxBitVec sz t2  in (uu____56572, uu____56573)
           in
        mkBvUlt uu____56567 t.rng
    | App
        (Var
         "Prims.equals",uu____56574::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____56578;
                                       rng = uu____56579;_}::uu____56580::[])
        when
        let uu____56599 = getBoxedInteger t0  in
        FStar_Util.is_some uu____56599 ->
        let sz =
          let uu____56606 = getBoxedInteger t0  in
          match uu____56606 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____56614 -> failwith "impossible"  in
        let uu____56620 =
          let uu____56625 = unboxBitVec sz t1  in
          let uu____56626 = unboxBitVec sz t2  in (uu____56625, uu____56626)
           in
        mkBvUlt uu____56620 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_56631 = unboxBool t1  in
        {
          tm = (uu___1789_56631.tm);
          freevars = (uu___1789_56631.freevars);
          rng = (t.rng)
        }
    | uu____56632 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____56693 = FStar_Options.unthrottle_inductives ()  in
        if uu____56693
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
    let uu____56826 =
      let uu____56827 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____56827 t t.rng  in
    FStar_All.pipe_right uu____56826 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____56845 =
        let uu____56853 =
          let uu____56856 = mkInteger' i norng  in [uu____56856]  in
        ("FString_const", uu____56853)  in
      mkApp uu____56845 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____56887 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____56887 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____56934 =
         let uu____56942 =
           let uu____56945 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____56945]  in
         ("SFuel", uu____56942)  in
       mkApp uu____56934 norng)
  
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
            let uu____56993 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____56993
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
      let uu____57056 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____57056
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____57076 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____57076
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____57087 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____57087
  
let (dummy_sort : sort) = Sort "Dummy_sort" 