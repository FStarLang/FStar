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
    match projectee with | Bool_sort  -> true | uu____43491 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____43502 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____43513 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____43524 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____43535 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____43548 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____43575 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____43611 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____43644 -> false
  
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
        let uu____43672 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____43672
    | Array (s1,s2) ->
        let uu____43677 = strSort s1  in
        let uu____43679 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____43677 uu____43679
    | Arrow (s1,s2) ->
        let uu____43684 = strSort s1  in
        let uu____43686 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____43684 uu____43686
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
    match projectee with | TrueOp  -> true | uu____43718 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____43729 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____43740 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____43751 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____43762 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____43773 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____43784 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____43795 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____43806 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____43817 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____43828 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____43839 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____43850 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____43861 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____43872 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____43883 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____43894 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____43905 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____43916 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____43927 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____43938 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____43949 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____43960 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____43971 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____43982 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____43993 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____44004 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____44015 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____44026 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____44037 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____44050 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____44074 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____44096 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____44107 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____44120 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____44142 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____44153 -> false
  
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
    match projectee with | Integer _0 -> true | uu____44302 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____44326 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____44350 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____44381 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____44431 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____44488 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____44571 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____44616 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____44662 -> false
  
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
    match projectee with | Name _0 -> true | uu____44853 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____44873 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____44894 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____45084 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____45107 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____45173 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____45232 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____45253 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____45283 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____45324 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____45345 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____45371 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____45399 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____45410 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____45421 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____45432 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____45450 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____45487 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____45498 -> false
  
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
          let uu____45672 =
            let uu____45673 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____45699 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____45673
            }  in
          [uu____45672]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____45713 =
      let uu____45714 =
        FStar_List.collect
          (fun uu___402_45721  ->
             match uu___402_45721 with
             | Assume a -> [a.assumption_name]
             | uu____45728 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____45714
      }  in
    [uu____45713]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____45765  -> match uu____45765 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____45785 = x  in
    match uu____45785 with | (nm,uu____45788,uu____45789) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____45800 = x  in
    match uu____45800 with | (uu____45801,sort,uu____45803) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____45815 = x  in
    match uu____45815 with | (uu____45817,uu____45818,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____45836 = fv_name x  in
      let uu____45838 = fv_name y  in uu____45836 = uu____45838
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____45872 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_45883  ->
    match uu___403_45883 with
    | { tm = FreeV x; freevars = uu____45885; rng = uu____45886;_} ->
        fv_sort x
    | uu____45907 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_45914  ->
    match uu___404_45914 with
    | { tm = FreeV fv; freevars = uu____45916; rng = uu____45917;_} -> fv
    | uu____45938 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____45966 -> []
    | Real uu____45976 -> []
    | BoundV uu____45986 -> []
    | FreeV fv -> [fv]
    | App (uu____46021,tms) -> FStar_List.collect freevars tms
    | Quant (uu____46035,uu____46036,uu____46037,uu____46038,t1) ->
        freevars t1
    | Labeled (t1,uu____46059,uu____46060) -> freevars t1
    | LblPos (t1,uu____46064) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____46087 = FStar_ST.op_Bang t.freevars  in
    match uu____46087 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____46185 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____46185  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_46264  ->
    match uu___405_46264 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_46274  ->
    match uu___406_46274 with
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
        let uu____46310 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____46310
    | NatToBv n1 ->
        let uu____46315 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____46315
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_46329  ->
    match uu___407_46329 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____46339 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____46339
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____46361 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____46361
    | FreeV x ->
        let uu____46373 = fv_name x  in
        let uu____46375 =
          let uu____46377 =
            let uu____46379 = fv_sort x  in strSort uu____46379  in
          Prims.op_Hat ":" uu____46377  in
        Prims.op_Hat uu____46373 uu____46375
    | App (op,tms) ->
        let uu____46387 =
          let uu____46389 = op_to_string op  in
          let uu____46391 =
            let uu____46393 =
              let uu____46395 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____46395 (FStar_String.concat " ")  in
            Prims.op_Hat uu____46393 ")"  in
          Prims.op_Hat uu____46389 uu____46391  in
        Prims.op_Hat "(" uu____46387
    | Labeled (t1,r1,r2) ->
        let uu____46412 = hash_of_term t1  in
        let uu____46414 =
          let uu____46416 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____46416  in
        Prims.op_Hat uu____46412 uu____46414
    | LblPos (t1,r) ->
        let uu____46422 =
          let uu____46424 = hash_of_term t1  in
          Prims.op_Hat uu____46424
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____46422
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____46452 =
          let uu____46454 =
            let uu____46456 =
              let uu____46458 =
                let uu____46460 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____46460 (FStar_String.concat " ")
                 in
              let uu____46470 =
                let uu____46472 =
                  let uu____46474 = hash_of_term body  in
                  let uu____46476 =
                    let uu____46478 =
                      let uu____46480 = weightToSmt wopt  in
                      let uu____46482 =
                        let uu____46484 =
                          let uu____46486 =
                            let uu____46488 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____46507 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____46507
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____46488
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____46486 "))"  in
                        Prims.op_Hat " " uu____46484  in
                      Prims.op_Hat uu____46480 uu____46482  in
                    Prims.op_Hat " " uu____46478  in
                  Prims.op_Hat uu____46474 uu____46476  in
                Prims.op_Hat ")(! " uu____46472  in
              Prims.op_Hat uu____46458 uu____46470  in
            Prims.op_Hat " (" uu____46456  in
          Prims.op_Hat (qop_to_string qop) uu____46454  in
        Prims.op_Hat "(" uu____46452
    | Let (es,body) ->
        let uu____46534 =
          let uu____46536 =
            let uu____46538 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____46538 (FStar_String.concat " ")  in
          let uu____46548 =
            let uu____46550 =
              let uu____46552 = hash_of_term body  in
              Prims.op_Hat uu____46552 ")"  in
            Prims.op_Hat ") " uu____46550  in
          Prims.op_Hat uu____46536 uu____46548  in
        Prims.op_Hat "(let (" uu____46534

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____46613 =
      let uu____46615 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____46615  in
    mkBoxFunctions uu____46613
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____46640 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____46640 = "Box") &&
        (let uu____46647 =
           let uu____46649 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____46649  in
         Prims.op_Negation uu____46647)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____46673 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____46673; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46737 =
        let uu____46738 = FStar_Util.ensure_decimal i  in Integer uu____46738
         in
      mk uu____46737 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46753 = FStar_Util.string_of_int i  in
      mkInteger uu____46753 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____46831  ->
    fun r  -> match uu____46831 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____46861) -> mkFalse r
      | App (FalseOp ,uu____46866) -> mkTrue r
      | uu____46871 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____46887  ->
    fun r  ->
      match uu____46887 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46895),uu____46896) -> t2
           | (uu____46901,App (TrueOp ,uu____46902)) -> t1
           | (App (FalseOp ,uu____46907),uu____46908) -> mkFalse r
           | (uu____46913,App (FalseOp ,uu____46914)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____46931,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____46940) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____46947 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____46967  ->
    fun r  ->
      match uu____46967 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46975),uu____46976) -> mkTrue r
           | (uu____46981,App (TrueOp ,uu____46982)) -> mkTrue r
           | (App (FalseOp ,uu____46987),uu____46988) -> t2
           | (uu____46993,App (FalseOp ,uu____46994)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____47011,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____47020) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____47027 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____47047  ->
    fun r  ->
      match uu____47047 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____47055,App (TrueOp ,uu____47056)) -> mkTrue r
           | (App (FalseOp ,uu____47061),uu____47062) -> mkTrue r
           | (App (TrueOp ,uu____47067),uu____47068) -> t2
           | (uu____47073,App (Imp ,t1'::t2'::[])) ->
               let uu____47078 =
                 let uu____47085 =
                   let uu____47088 = mkAnd (t1, t1') r  in [uu____47088; t2']
                    in
                 (Imp, uu____47085)  in
               mkApp' uu____47078 r
           | uu____47091 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____47116  ->
      fun r  -> match uu____47116 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____47276  ->
      fun r  ->
        match uu____47276 with
        | (t1,t2) ->
            let uu____47285 =
              let uu____47292 =
                let uu____47295 =
                  let uu____47298 = mkNatToBv sz t2 r  in [uu____47298]  in
                t1 :: uu____47295  in
              (BvShl, uu____47292)  in
            mkApp' uu____47285 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____47320  ->
      fun r  ->
        match uu____47320 with
        | (t1,t2) ->
            let uu____47329 =
              let uu____47336 =
                let uu____47339 =
                  let uu____47342 = mkNatToBv sz t2 r  in [uu____47342]  in
                t1 :: uu____47339  in
              (BvShr, uu____47336)  in
            mkApp' uu____47329 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____47364  ->
      fun r  ->
        match uu____47364 with
        | (t1,t2) ->
            let uu____47373 =
              let uu____47380 =
                let uu____47383 =
                  let uu____47386 = mkNatToBv sz t2 r  in [uu____47386]  in
                t1 :: uu____47383  in
              (BvUdiv, uu____47380)  in
            mkApp' uu____47373 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____47408  ->
      fun r  ->
        match uu____47408 with
        | (t1,t2) ->
            let uu____47417 =
              let uu____47424 =
                let uu____47427 =
                  let uu____47430 = mkNatToBv sz t2 r  in [uu____47430]  in
                t1 :: uu____47427  in
              (BvMod, uu____47424)  in
            mkApp' uu____47417 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____47452  ->
      fun r  ->
        match uu____47452 with
        | (t1,t2) ->
            let uu____47461 =
              let uu____47468 =
                let uu____47471 =
                  let uu____47474 = mkNatToBv sz t2 r  in [uu____47474]  in
                t1 :: uu____47471  in
              (BvMul, uu____47468)  in
            mkApp' uu____47461 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____47516  ->
    fun r  ->
      match uu____47516 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____47535 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____47700  ->
    fun r  ->
      match uu____47700 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____47711) -> t2
           | App (FalseOp ,uu____47716) -> t3
           | uu____47721 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____47722),App (TrueOp ,uu____47723)) ->
                    mkTrue r
                | (App (TrueOp ,uu____47732),uu____47733) ->
                    let uu____47738 =
                      let uu____47743 = mkNot t1 t1.rng  in (uu____47743, t3)
                       in
                    mkImp uu____47738 r
                | (uu____47744,App (TrueOp ,uu____47745)) -> mkImp (t1, t2) r
                | (uu____47750,uu____47751) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____47807 -> FStar_Pervasives_Native.None
      | Real uu____47809 -> FStar_Pervasives_Native.None
      | BoundV uu____47811 -> FStar_Pervasives_Native.None
      | FreeV uu____47813 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____47837 -> true
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
            | BvUext uu____47870 -> false
            | NatToBv uu____47873 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____47884,uu____47885) -> aux t2
      | Quant uu____47888 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____47908 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____47923 = aux t1  in
          (match uu____47923 with
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
        let uu____47961 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____47961
    | FreeV fv ->
        let uu____47973 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____47973
    | App (op,l) ->
        let uu____47982 = op_to_string op  in
        let uu____47984 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____47982 uu____47984
    | Labeled (t1,r1,r2) ->
        let uu____47992 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____47992
    | LblPos (t1,s) ->
        let uu____47999 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____47999
    | Quant (qop,l,uu____48004,uu____48005,t1) ->
        let uu____48025 = print_smt_term_list_list l  in
        let uu____48027 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____48025
          uu____48027
    | Let (es,body) ->
        let uu____48036 = print_smt_term_list es  in
        let uu____48038 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____48036 uu____48038

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____48045 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____48045 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____48072 =
             let uu____48074 =
               let uu____48076 = print_smt_term_list l1  in
               Prims.op_Hat uu____48076 " ] "  in
             Prims.op_Hat "; [ " uu____48074  in
           Prims.op_Hat s uu____48072) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____48116  ->
        match uu____48116 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____48185 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____48185 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____48200 =
                         let uu____48206 =
                           let uu____48208 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____48208
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____48206)
                          in
                       FStar_Errors.log_issue r uu____48200);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____48219) -> body
               | uu____48224 ->
                   let uu____48225 =
                     let uu____48226 =
                       let uu____48246 = all_pats_ok pats  in
                       (qop, uu____48246, wopt, vars, body)  in
                     Quant uu____48226  in
                   mk uu____48225 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____48275  ->
    fun r  ->
      match uu____48275 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____48321 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____48321 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____48348 = FStar_ST.op_Bang t1.freevars  in
        match uu____48348 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____48422 ->
            (match t1.tm with
             | Integer uu____48435 -> t1
             | Real uu____48437 -> t1
             | BoundV uu____48439 -> t1
             | FreeV x ->
                 let uu____48450 = index_of1 x  in
                 (match uu____48450 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____48464 =
                   let uu____48471 = FStar_List.map (aux ix) tms  in
                   (op, uu____48471)  in
                 mkApp' uu____48464 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____48481 =
                   let uu____48482 =
                     let uu____48490 = aux ix t2  in (uu____48490, r1, r2)
                      in
                   Labeled uu____48482  in
                 mk uu____48481 t2.rng
             | LblPos (t2,r) ->
                 let uu____48496 =
                   let uu____48497 =
                     let uu____48503 = aux ix t2  in (uu____48503, r)  in
                   LblPos uu____48497  in
                 mk uu____48496 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____48529 =
                   let uu____48549 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____48566 = aux (ix + n1) body  in
                   (qop, uu____48549, wopt, vars, uu____48566)  in
                 mkQuant t1.rng false uu____48529
             | Let (es,body) ->
                 let uu____48583 =
                   FStar_List.fold_left
                     (fun uu____48603  ->
                        fun e  ->
                          match uu____48603 with
                          | (ix1,l) ->
                              let uu____48627 =
                                let uu____48630 = aux ix1 e  in uu____48630
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____48627))
                     (ix, []) es
                    in
                 (match uu____48583 with
                  | (ix1,es_rev) ->
                      let uu____48646 =
                        let uu____48653 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____48653)  in
                      mkLet uu____48646 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____48689 -> t1
        | Real uu____48691 -> t1
        | FreeV uu____48693 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____48714 =
              let uu____48721 = FStar_List.map (aux shift) tms2  in
              (op, uu____48721)  in
            mkApp' uu____48714 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____48731 =
              let uu____48732 =
                let uu____48740 = aux shift t2  in (uu____48740, r1, r2)  in
              Labeled uu____48732  in
            mk uu____48731 t2.rng
        | LblPos (t2,r) ->
            let uu____48746 =
              let uu____48747 =
                let uu____48753 = aux shift t2  in (uu____48753, r)  in
              LblPos uu____48747  in
            mk uu____48746 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____48781 =
              let uu____48801 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____48818 = aux shift1 body  in
              (qop, uu____48801, wopt, vars, uu____48818)  in
            mkQuant t1.rng false uu____48781
        | Let (es,body) ->
            let uu____48835 =
              FStar_List.fold_left
                (fun uu____48855  ->
                   fun e  ->
                     match uu____48855 with
                     | (ix,es1) ->
                         let uu____48879 =
                           let uu____48882 = aux shift e  in uu____48882 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____48879))
                (shift, []) es
               in
            (match uu____48835 with
             | (shift1,es_rev) ->
                 let uu____48898 =
                   let uu____48905 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____48905)  in
                 mkLet uu____48898 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____48925 = abstr [fv] t  in inst [s] uu____48925
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48955  ->
      match uu____48955 with
      | (qop,pats,wopt,vars,body) ->
          let uu____48998 =
            let uu____49018 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____49035 = FStar_List.map fv_sort vars  in
            let uu____49038 = abstr vars body  in
            (qop, uu____49018, wopt, uu____49035, uu____49038)  in
          mkQuant r true uu____48998
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____49069  ->
      match uu____49069 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____49128  ->
      match uu____49128 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____49203  ->
      match uu____49203 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____49266  ->
      match uu____49266 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____49317  ->
    fun r  ->
      match uu____49317 with
      | (bindings,body) ->
          let uu____49343 = FStar_List.split bindings  in
          (match uu____49343 with
           | (vars,es) ->
               let uu____49362 =
                 let uu____49369 = abstr vars body  in (es, uu____49369)  in
               mkLet uu____49362 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____49391  ->
    match uu____49391 with
    | (nm,vars,s,tm,c) ->
        let uu____49416 =
          let uu____49430 = FStar_List.map fv_sort vars  in
          let uu____49433 = abstr vars tm  in
          (nm, uu____49430, s, uu____49433, c)  in
        DefineFun uu____49416
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____49444 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____49444
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____49462  ->
    fun id1  ->
      match uu____49462 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____49478 =
              let uu____49479 =
                let uu____49484 = mkInteger' id1 norng  in
                let uu____49485 =
                  let uu____49486 =
                    let uu____49494 = constr_id_of_sort sort  in
                    let uu____49496 =
                      let uu____49499 = mkApp (tok_name, []) norng  in
                      [uu____49499]  in
                    (uu____49494, uu____49496)  in
                  mkApp uu____49486 norng  in
                (uu____49484, uu____49485)  in
              mkEq uu____49479 norng  in
            let uu____49506 = escape a_name  in
            {
              assumption_term = uu____49478;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____49506;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____49532  ->
      match uu____49532 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____49572 =
                        let uu____49573 =
                          let uu____49579 =
                            let uu____49581 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____49581  in
                          (uu____49579, s)  in
                        mk_fv uu____49573  in
                      mkFreeV uu____49572 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____49609 =
              let uu____49617 = constr_id_of_sort sort  in
              (uu____49617, [capp])  in
            mkApp uu____49609 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____49626 =
              let uu____49627 =
                let uu____49638 =
                  let uu____49639 =
                    let uu____49644 = mkInteger id2 norng  in
                    (uu____49644, cid_app)  in
                  mkEq uu____49639 norng  in
                ([[capp]], bvar_names, uu____49638)  in
              mkForall rng uu____49627  in
            let uu____49653 = escape a_name  in
            {
              assumption_term = uu____49626;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____49653;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____49678  ->
      match uu____49678 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____49711 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____49711  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____49740 =
              let uu____49741 =
                let uu____49747 = bvar_name i  in (uu____49747, s)  in
              mk_fv uu____49741  in
            FStar_All.pipe_left mkFreeV uu____49740  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49783  ->
                      match uu____49783 with
                      | (uu____49793,s,uu____49795) ->
                          let uu____49800 = bvar i s  in uu____49800 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____49828 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49866  ->
                      match uu____49866 with
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
                              let uu____49899 =
                                let uu____49900 =
                                  let uu____49911 =
                                    let uu____49912 =
                                      let uu____49917 =
                                        let uu____49918 = bvar i s  in
                                        uu____49918 norng  in
                                      (cproj_app, uu____49917)  in
                                    mkEq uu____49912 norng  in
                                  ([[capp]], bvar_names, uu____49911)  in
                                mkForall rng uu____49900  in
                              let uu____49931 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____49899;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____49931;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____49828 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____49956  ->
      match uu____49956 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____50004  ->
                    match uu____50004 with
                    | (uu____50013,sort1,uu____50015) -> sort1))
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
              let uu____50040 =
                let uu____50045 =
                  let uu____50046 =
                    let uu____50054 = constr_id_of_sort sort  in
                    (uu____50054, [xx])  in
                  mkApp uu____50046 norng  in
                let uu____50059 =
                  let uu____50060 = FStar_Util.string_of_int id1  in
                  mkInteger uu____50060 norng  in
                (uu____50045, uu____50059)  in
              mkEq uu____50040 norng  in
            let uu____50062 =
              let uu____50081 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____50145  ->
                          match uu____50145 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____50175 = mkApp (proj, [xx]) norng
                                   in
                                (uu____50175, [])
                              else
                                (let fi =
                                   let uu____50184 =
                                     let uu____50190 =
                                       let uu____50192 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____50192  in
                                     (uu____50190, s)  in
                                   mk_fv uu____50184  in
                                 let uu____50196 = mkFreeV fi norng  in
                                 (uu____50196, [fi]))))
                 in
              FStar_All.pipe_right uu____50081 FStar_List.split  in
            match uu____50062 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____50293 =
                    let uu____50298 = mkApp (name, proj_terms) norng  in
                    (xx, uu____50298)  in
                  mkEq uu____50293 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____50311 ->
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
          let uu____50346 =
            let uu____50349 =
              let uu____50350 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____50350  in
            uu____50349 :: cdecl :: cid :: projs  in
          let uu____50353 =
            let uu____50356 =
              let uu____50359 =
                let uu____50360 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____50360  in
              [uu____50359]  in
            FStar_List.append [disc] uu____50356  in
          FStar_List.append uu____50346 uu____50353
  
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
          let uu____50412 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____50461  ->
                    fun s  ->
                      match uu____50461 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____50506 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____50517 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____50517  in
                          let names2 =
                            let uu____50522 = mk_fv (nm, s)  in uu____50522
                              :: names1
                             in
                          let b =
                            let uu____50526 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____50526  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____50412 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____50597 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____50597 with
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
              (let uu____50706 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____50706)
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
                               "Prims.guard_free",{ tm = BoundV uu____50752;
                                                    freevars = uu____50753;
                                                    rng = uu____50754;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____50775 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____50853 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____50853 fv_name
          | FreeV x when fv_force x ->
              let uu____50864 =
                let uu____50866 = fv_name x  in
                Prims.op_Hat uu____50866 " Dummy_value)"  in
              Prims.op_Hat "(" uu____50864
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____50888 = op_to_string op  in
              let uu____50890 =
                let uu____50892 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____50892 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____50888 uu____50890
          | Labeled (t2,uu____50904,uu____50905) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____50912 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____50912 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____50940 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____50940 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____50993 ->
                         let uu____50998 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____51017 =
                                     let uu____51019 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____51027 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____51027) pats2
                                        in
                                     FStar_String.concat " " uu____51019  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____51017))
                            in
                         FStar_All.pipe_right uu____50998
                           (FStar_String.concat "\n")
                      in
                   let uu____51037 =
                     let uu____51041 =
                       let uu____51045 =
                         let uu____51049 = aux1 n2 names2 body  in
                         let uu____51051 =
                           let uu____51055 = weightToSmt wopt  in
                           [uu____51055; pats_str; qid]  in
                         uu____51049 :: uu____51051  in
                       binders1 :: uu____51045  in
                     (qop_to_string qop) :: uu____51041  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____51037)
          | Let (es,body) ->
              let uu____51071 =
                FStar_List.fold_left
                  (fun uu____51104  ->
                     fun e  ->
                       match uu____51104 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____51147 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____51147  in
                           let names01 =
                             let uu____51153 = mk_fv (nm, Term_sort)  in
                             uu____51153 :: names0  in
                           let b =
                             let uu____51157 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____51157  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____51071 with
               | (names2,binders,n2) ->
                   let uu____51191 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____51191)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____51207 = FStar_Range.string_of_range t1.rng  in
            let uu____51209 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____51207
              uu____51209 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_51231  ->
      match uu___408_51231 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____51242 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____51242 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____51264 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____51339 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____51339 (FStar_String.concat "\n")  in
            let uu____51349 = FStar_Options.keep_query_captions ()  in
            if uu____51349
            then
              let uu____51353 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____51355 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____51353 uu____51355
            else res
        | Caption c ->
            if print_captions
            then
              let uu____51364 =
                let uu____51366 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____51366 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____51364
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____51407 = caption_to_string print_captions c  in
            let uu____51409 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____51407 f
              (FStar_String.concat " " l) uu____51409
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____51424 = name_macro_binders arg_sorts  in
            (match uu____51424 with
             | (names1,binders) ->
                 let body1 =
                   let uu____51448 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____51448 body  in
                 let uu____51453 = caption_to_string print_captions c  in
                 let uu____51455 = strSort retsort  in
                 let uu____51457 =
                   let uu____51459 = escape f  in
                   termToSmt print_captions uu____51459 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____51453 f (FStar_String.concat " " binders)
                   uu____51455 uu____51457)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_51486  ->
                      match uu___409_51486 with
                      | Name n1 ->
                          let uu____51489 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____51489
                      | Namespace ns ->
                          let uu____51493 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____51493
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____51503 =
                  let uu____51505 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____51505  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____51503
              else ""  in
            let n1 = a.assumption_name  in
            let uu____51516 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____51518 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____51516
              fids uu____51518 n1
        | Eval t ->
            let uu____51522 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____51522
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____51529 -> ""
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
      let uu____51550 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____51550 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____51561 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____51561 (FStar_String.concat "\n")

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
      let uu____51696 =
        let uu____51700 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____51700
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____51696 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____51731 =
      let uu____51732 =
        let uu____51734 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51734  in
      let uu____51743 =
        let uu____51746 =
          let uu____51747 =
            let uu____51749 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____51749  in
          (uu____51747, (BitVec_sort sz), true)  in
        [uu____51746]  in
      (uu____51732, uu____51743, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____51731 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____51781  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____51806 =
       let uu____51808 = FStar_ST.op_Bang __range_c  in
       uu____51808 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____51806);
    (let uu____51853 =
       let uu____51861 =
         let uu____51864 = mkInteger' i norng  in [uu____51864]  in
       ("Range_const", uu____51861)  in
     mkApp uu____51853 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____51907 =
        let uu____51915 =
          let uu____51918 = mkInteger' i norng  in [uu____51918]  in
        ("Tm_uvar", uu____51915)  in
      mkApp uu____51907 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____51961 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____51985 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____51985 u v1 t
  
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
      let uu____52080 =
        let uu____52082 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____52082  in
      let uu____52091 =
        let uu____52093 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____52093  in
      elim_box true uu____52080 uu____52091 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____52116 =
        let uu____52118 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____52118  in
      let uu____52127 =
        let uu____52129 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____52129  in
      elim_box true uu____52116 uu____52127 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____52153 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____52168 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____52194 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____52194
         | uu____52197 -> FStar_Pervasives_Native.None)
    | uu____52199 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____52217::t1::t2::[]);
                       freevars = uu____52220; rng = uu____52221;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____52240::t1::t2::[]);
                       freevars = uu____52243; rng = uu____52244;_}::[])
        -> let uu____52263 = mkEq (t1, t2) norng  in mkNot uu____52263 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____52266; rng = uu____52267;_}::[])
        ->
        let uu____52286 =
          let uu____52291 = unboxInt t1  in
          let uu____52292 = unboxInt t2  in (uu____52291, uu____52292)  in
        mkLTE uu____52286 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____52295; rng = uu____52296;_}::[])
        ->
        let uu____52315 =
          let uu____52320 = unboxInt t1  in
          let uu____52321 = unboxInt t2  in (uu____52320, uu____52321)  in
        mkLT uu____52315 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____52324; rng = uu____52325;_}::[])
        ->
        let uu____52344 =
          let uu____52349 = unboxInt t1  in
          let uu____52350 = unboxInt t2  in (uu____52349, uu____52350)  in
        mkGTE uu____52344 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____52353; rng = uu____52354;_}::[])
        ->
        let uu____52373 =
          let uu____52378 = unboxInt t1  in
          let uu____52379 = unboxInt t2  in (uu____52378, uu____52379)  in
        mkGT uu____52373 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____52382; rng = uu____52383;_}::[])
        ->
        let uu____52402 =
          let uu____52407 = unboxBool t1  in
          let uu____52408 = unboxBool t2  in (uu____52407, uu____52408)  in
        mkAnd uu____52402 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____52411; rng = uu____52412;_}::[])
        ->
        let uu____52431 =
          let uu____52436 = unboxBool t1  in
          let uu____52437 = unboxBool t2  in (uu____52436, uu____52437)  in
        mkOr uu____52431 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____52439; rng = uu____52440;_}::[])
        -> let uu____52459 = unboxBool t1  in mkNot uu____52459 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____52463; rng = uu____52464;_}::[])
        when
        let uu____52483 = getBoxedInteger t0  in
        FStar_Util.is_some uu____52483 ->
        let sz =
          let uu____52490 = getBoxedInteger t0  in
          match uu____52490 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____52498 -> failwith "impossible"  in
        let uu____52504 =
          let uu____52509 = unboxBitVec sz t1  in
          let uu____52510 = unboxBitVec sz t2  in (uu____52509, uu____52510)
           in
        mkBvUlt uu____52504 t.rng
    | App
        (Var
         "Prims.equals",uu____52511::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____52515;
                                       rng = uu____52516;_}::uu____52517::[])
        when
        let uu____52536 = getBoxedInteger t0  in
        FStar_Util.is_some uu____52536 ->
        let sz =
          let uu____52543 = getBoxedInteger t0  in
          match uu____52543 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____52551 -> failwith "impossible"  in
        let uu____52557 =
          let uu____52562 = unboxBitVec sz t1  in
          let uu____52563 = unboxBitVec sz t2  in (uu____52562, uu____52563)
           in
        mkBvUlt uu____52557 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_52568 = unboxBool t1  in
        {
          tm = (uu___1789_52568.tm);
          freevars = (uu___1789_52568.freevars);
          rng = (t.rng)
        }
    | uu____52569 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____52630 = FStar_Options.unthrottle_inductives ()  in
        if uu____52630
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
    let uu____52763 =
      let uu____52764 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____52764 t t.rng  in
    FStar_All.pipe_right uu____52763 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____52782 =
        let uu____52790 =
          let uu____52793 = mkInteger' i norng  in [uu____52793]  in
        ("FString_const", uu____52790)  in
      mkApp uu____52782 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____52824 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____52824 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____52871 =
         let uu____52879 =
           let uu____52882 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____52882]  in
         ("SFuel", uu____52879)  in
       mkApp uu____52871 norng)
  
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
            let uu____52930 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____52930
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
      let uu____52993 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____52993
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____53013 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____53013
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____53024 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____53024
  
let (dummy_sort : sort) = Sort "Dummy_sort" 