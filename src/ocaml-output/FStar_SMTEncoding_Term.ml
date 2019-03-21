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
    match projectee with | Bool_sort  -> true | uu____42922 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____42933 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____42944 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____42955 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____42966 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____42979 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____43005 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____43040 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____43072 -> false
  
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
        let uu____43099 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____43099
    | Array (s1,s2) ->
        let uu____43104 = strSort s1  in
        let uu____43106 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____43104 uu____43106
    | Arrow (s1,s2) ->
        let uu____43111 = strSort s1  in
        let uu____43113 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____43111 uu____43113
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
    match projectee with | TrueOp  -> true | uu____43145 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____43156 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____43167 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____43178 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____43189 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____43200 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____43211 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____43222 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____43233 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____43244 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____43255 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____43266 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____43277 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____43288 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____43299 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____43310 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____43321 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____43332 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____43343 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____43354 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____43365 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____43376 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____43387 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____43398 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____43409 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____43420 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____43431 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____43442 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____43453 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____43464 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____43477 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____43500 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____43521 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____43532 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____43545 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____43566 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____43577 -> false
  
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
    match projectee with | Integer _0 -> true | uu____43726 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____43749 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____43772 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____43802 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____43851 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____43907 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____43989 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____44033 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____44078 -> false
  
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
    match projectee with | Name _0 -> true | uu____44268 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____44287 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____44307 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____44496 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____44519 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____44584 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____44642 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____44662 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____44691 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____44731 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____44751 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____44776 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____44803 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____44814 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____44825 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____44836 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____44854 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____44890 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____44901 -> false
  
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
          let uu____45075 =
            let uu____45076 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____45102 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____45076
            }  in
          [uu____45075]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____45116 =
      let uu____45117 =
        FStar_List.collect
          (fun uu___402_45124  ->
             match uu___402_45124 with
             | Assume a -> [a.assumption_name]
             | uu____45131 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____45117
      }  in
    [uu____45116]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____45168  -> match uu____45168 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____45188 = x  in
    match uu____45188 with | (nm,uu____45191,uu____45192) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____45203 = x  in
    match uu____45203 with | (uu____45204,sort,uu____45206) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____45218 = x  in
    match uu____45218 with | (uu____45220,uu____45221,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____45239 = fv_name x  in
      let uu____45241 = fv_name y  in uu____45239 = uu____45241
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____45275 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_45286  ->
    match uu___403_45286 with
    | { tm = FreeV x; freevars = uu____45288; rng = uu____45289;_} ->
        fv_sort x
    | uu____45310 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_45317  ->
    match uu___404_45317 with
    | { tm = FreeV fv; freevars = uu____45319; rng = uu____45320;_} -> fv
    | uu____45341 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____45369 -> []
    | Real uu____45379 -> []
    | BoundV uu____45389 -> []
    | FreeV fv -> [fv]
    | App (uu____45424,tms) -> FStar_List.collect freevars tms
    | Quant (uu____45438,uu____45439,uu____45440,uu____45441,t1) ->
        freevars t1
    | Labeled (t1,uu____45462,uu____45463) -> freevars t1
    | LblPos (t1,uu____45467) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____45490 = FStar_ST.op_Bang t.freevars  in
    match uu____45490 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____45588 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____45588  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_45667  ->
    match uu___405_45667 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_45677  ->
    match uu___406_45677 with
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
        let uu____45713 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____45713
    | NatToBv n1 ->
        let uu____45718 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____45718
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_45732  ->
    match uu___407_45732 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____45742 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____45742
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____45764 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____45764
    | FreeV x ->
        let uu____45776 = fv_name x  in
        let uu____45778 =
          let uu____45780 =
            let uu____45782 = fv_sort x  in strSort uu____45782  in
          Prims.op_Hat ":" uu____45780  in
        Prims.op_Hat uu____45776 uu____45778
    | App (op,tms) ->
        let uu____45790 =
          let uu____45792 = op_to_string op  in
          let uu____45794 =
            let uu____45796 =
              let uu____45798 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____45798 (FStar_String.concat " ")  in
            Prims.op_Hat uu____45796 ")"  in
          Prims.op_Hat uu____45792 uu____45794  in
        Prims.op_Hat "(" uu____45790
    | Labeled (t1,r1,r2) ->
        let uu____45815 = hash_of_term t1  in
        let uu____45817 =
          let uu____45819 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____45819  in
        Prims.op_Hat uu____45815 uu____45817
    | LblPos (t1,r) ->
        let uu____45825 =
          let uu____45827 = hash_of_term t1  in
          Prims.op_Hat uu____45827
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____45825
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____45855 =
          let uu____45857 =
            let uu____45859 =
              let uu____45861 =
                let uu____45863 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____45863 (FStar_String.concat " ")
                 in
              let uu____45873 =
                let uu____45875 =
                  let uu____45877 = hash_of_term body  in
                  let uu____45879 =
                    let uu____45881 =
                      let uu____45883 = weightToSmt wopt  in
                      let uu____45885 =
                        let uu____45887 =
                          let uu____45889 =
                            let uu____45891 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____45910 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____45910
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____45891
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____45889 "))"  in
                        Prims.op_Hat " " uu____45887  in
                      Prims.op_Hat uu____45883 uu____45885  in
                    Prims.op_Hat " " uu____45881  in
                  Prims.op_Hat uu____45877 uu____45879  in
                Prims.op_Hat ")(! " uu____45875  in
              Prims.op_Hat uu____45861 uu____45873  in
            Prims.op_Hat " (" uu____45859  in
          Prims.op_Hat (qop_to_string qop) uu____45857  in
        Prims.op_Hat "(" uu____45855
    | Let (es,body) ->
        let uu____45937 =
          let uu____45939 =
            let uu____45941 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____45941 (FStar_String.concat " ")  in
          let uu____45951 =
            let uu____45953 =
              let uu____45955 = hash_of_term body  in
              Prims.op_Hat uu____45955 ")"  in
            Prims.op_Hat ") " uu____45953  in
          Prims.op_Hat uu____45939 uu____45951  in
        Prims.op_Hat "(let (" uu____45937

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____46016 =
      let uu____46018 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____46018  in
    mkBoxFunctions uu____46016
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____46043 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____46043 = "Box") &&
        (let uu____46050 =
           let uu____46052 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____46052  in
         Prims.op_Negation uu____46050)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____46076 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____46076; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46140 =
        let uu____46141 = FStar_Util.ensure_decimal i  in Integer uu____46141
         in
      mk uu____46140 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46156 = FStar_Util.string_of_int i  in
      mkInteger uu____46156 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____46234  ->
    fun r  -> match uu____46234 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____46264) -> mkFalse r
      | App (FalseOp ,uu____46269) -> mkTrue r
      | uu____46274 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____46290  ->
    fun r  ->
      match uu____46290 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46298),uu____46299) -> t2
           | (uu____46304,App (TrueOp ,uu____46305)) -> t1
           | (App (FalseOp ,uu____46310),uu____46311) -> mkFalse r
           | (uu____46316,App (FalseOp ,uu____46317)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____46334,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____46343) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____46350 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____46370  ->
    fun r  ->
      match uu____46370 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46378),uu____46379) -> mkTrue r
           | (uu____46384,App (TrueOp ,uu____46385)) -> mkTrue r
           | (App (FalseOp ,uu____46390),uu____46391) -> t2
           | (uu____46396,App (FalseOp ,uu____46397)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____46414,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____46423) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____46430 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____46450  ->
    fun r  ->
      match uu____46450 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____46458,App (TrueOp ,uu____46459)) -> mkTrue r
           | (App (FalseOp ,uu____46464),uu____46465) -> mkTrue r
           | (App (TrueOp ,uu____46470),uu____46471) -> t2
           | (uu____46476,App (Imp ,t1'::t2'::[])) ->
               let uu____46481 =
                 let uu____46488 =
                   let uu____46491 = mkAnd (t1, t1') r  in [uu____46491; t2']
                    in
                 (Imp, uu____46488)  in
               mkApp' uu____46481 r
           | uu____46494 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____46519  ->
      fun r  -> match uu____46519 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____46679  ->
      fun r  ->
        match uu____46679 with
        | (t1,t2) ->
            let uu____46688 =
              let uu____46695 =
                let uu____46698 =
                  let uu____46701 = mkNatToBv sz t2 r  in [uu____46701]  in
                t1 :: uu____46698  in
              (BvShl, uu____46695)  in
            mkApp' uu____46688 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46723  ->
      fun r  ->
        match uu____46723 with
        | (t1,t2) ->
            let uu____46732 =
              let uu____46739 =
                let uu____46742 =
                  let uu____46745 = mkNatToBv sz t2 r  in [uu____46745]  in
                t1 :: uu____46742  in
              (BvShr, uu____46739)  in
            mkApp' uu____46732 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46767  ->
      fun r  ->
        match uu____46767 with
        | (t1,t2) ->
            let uu____46776 =
              let uu____46783 =
                let uu____46786 =
                  let uu____46789 = mkNatToBv sz t2 r  in [uu____46789]  in
                t1 :: uu____46786  in
              (BvUdiv, uu____46783)  in
            mkApp' uu____46776 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46811  ->
      fun r  ->
        match uu____46811 with
        | (t1,t2) ->
            let uu____46820 =
              let uu____46827 =
                let uu____46830 =
                  let uu____46833 = mkNatToBv sz t2 r  in [uu____46833]  in
                t1 :: uu____46830  in
              (BvMod, uu____46827)  in
            mkApp' uu____46820 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46855  ->
      fun r  ->
        match uu____46855 with
        | (t1,t2) ->
            let uu____46864 =
              let uu____46871 =
                let uu____46874 =
                  let uu____46877 = mkNatToBv sz t2 r  in [uu____46877]  in
                t1 :: uu____46874  in
              (BvMul, uu____46871)  in
            mkApp' uu____46864 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____46919  ->
    fun r  ->
      match uu____46919 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____46938 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____47103  ->
    fun r  ->
      match uu____47103 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____47114) -> t2
           | App (FalseOp ,uu____47119) -> t3
           | uu____47124 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____47125),App (TrueOp ,uu____47126)) ->
                    mkTrue r
                | (App (TrueOp ,uu____47135),uu____47136) ->
                    let uu____47141 =
                      let uu____47146 = mkNot t1 t1.rng  in (uu____47146, t3)
                       in
                    mkImp uu____47141 r
                | (uu____47147,App (TrueOp ,uu____47148)) -> mkImp (t1, t2) r
                | (uu____47153,uu____47154) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____47210 -> FStar_Pervasives_Native.None
      | Real uu____47212 -> FStar_Pervasives_Native.None
      | BoundV uu____47214 -> FStar_Pervasives_Native.None
      | FreeV uu____47216 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____47240 -> true
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
            | BvUext uu____47273 -> false
            | NatToBv uu____47276 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____47287,uu____47288) -> aux t2
      | Quant uu____47291 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____47311 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____47326 = aux t1  in
          (match uu____47326 with
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
        let uu____47364 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____47364
    | FreeV fv ->
        let uu____47376 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____47376
    | App (op,l) ->
        let uu____47385 = op_to_string op  in
        let uu____47387 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____47385 uu____47387
    | Labeled (t1,r1,r2) ->
        let uu____47395 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____47395
    | LblPos (t1,s) ->
        let uu____47402 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____47402
    | Quant (qop,l,uu____47407,uu____47408,t1) ->
        let uu____47428 = print_smt_term_list_list l  in
        let uu____47430 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____47428
          uu____47430
    | Let (es,body) ->
        let uu____47439 = print_smt_term_list es  in
        let uu____47441 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____47439 uu____47441

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____47448 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____47448 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____47475 =
             let uu____47477 =
               let uu____47479 = print_smt_term_list l1  in
               Prims.op_Hat uu____47479 " ] "  in
             Prims.op_Hat "; [ " uu____47477  in
           Prims.op_Hat s uu____47475) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____47519  ->
        match uu____47519 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____47588 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____47588 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____47603 =
                         let uu____47609 =
                           let uu____47611 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____47611
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____47609)
                          in
                       FStar_Errors.log_issue r uu____47603);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____47622) -> body
               | uu____47627 ->
                   let uu____47628 =
                     let uu____47629 =
                       let uu____47649 = all_pats_ok pats  in
                       (qop, uu____47649, wopt, vars, body)  in
                     Quant uu____47629  in
                   mk uu____47628 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____47678  ->
    fun r  ->
      match uu____47678 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____47724 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____47724 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____47751 = FStar_ST.op_Bang t1.freevars  in
        match uu____47751 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____47825 ->
            (match t1.tm with
             | Integer uu____47838 -> t1
             | Real uu____47840 -> t1
             | BoundV uu____47842 -> t1
             | FreeV x ->
                 let uu____47853 = index_of1 x  in
                 (match uu____47853 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____47867 =
                   let uu____47874 = FStar_List.map (aux ix) tms  in
                   (op, uu____47874)  in
                 mkApp' uu____47867 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____47884 =
                   let uu____47885 =
                     let uu____47893 = aux ix t2  in (uu____47893, r1, r2)
                      in
                   Labeled uu____47885  in
                 mk uu____47884 t2.rng
             | LblPos (t2,r) ->
                 let uu____47899 =
                   let uu____47900 =
                     let uu____47906 = aux ix t2  in (uu____47906, r)  in
                   LblPos uu____47900  in
                 mk uu____47899 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____47932 =
                   let uu____47952 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____47969 = aux (ix + n1) body  in
                   (qop, uu____47952, wopt, vars, uu____47969)  in
                 mkQuant t1.rng false uu____47932
             | Let (es,body) ->
                 let uu____47986 =
                   FStar_List.fold_left
                     (fun uu____48006  ->
                        fun e  ->
                          match uu____48006 with
                          | (ix1,l) ->
                              let uu____48030 =
                                let uu____48033 = aux ix1 e  in uu____48033
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____48030))
                     (ix, []) es
                    in
                 (match uu____47986 with
                  | (ix1,es_rev) ->
                      let uu____48049 =
                        let uu____48056 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____48056)  in
                      mkLet uu____48049 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____48092 -> t1
        | Real uu____48094 -> t1
        | FreeV uu____48096 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____48117 =
              let uu____48124 = FStar_List.map (aux shift) tms2  in
              (op, uu____48124)  in
            mkApp' uu____48117 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____48134 =
              let uu____48135 =
                let uu____48143 = aux shift t2  in (uu____48143, r1, r2)  in
              Labeled uu____48135  in
            mk uu____48134 t2.rng
        | LblPos (t2,r) ->
            let uu____48149 =
              let uu____48150 =
                let uu____48156 = aux shift t2  in (uu____48156, r)  in
              LblPos uu____48150  in
            mk uu____48149 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____48184 =
              let uu____48204 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____48221 = aux shift1 body  in
              (qop, uu____48204, wopt, vars, uu____48221)  in
            mkQuant t1.rng false uu____48184
        | Let (es,body) ->
            let uu____48238 =
              FStar_List.fold_left
                (fun uu____48258  ->
                   fun e  ->
                     match uu____48258 with
                     | (ix,es1) ->
                         let uu____48282 =
                           let uu____48285 = aux shift e  in uu____48285 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____48282))
                (shift, []) es
               in
            (match uu____48238 with
             | (shift1,es_rev) ->
                 let uu____48301 =
                   let uu____48308 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____48308)  in
                 mkLet uu____48301 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____48328 = abstr [fv] t  in inst [s] uu____48328
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48358  ->
      match uu____48358 with
      | (qop,pats,wopt,vars,body) ->
          let uu____48401 =
            let uu____48421 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____48438 = FStar_List.map fv_sort vars  in
            let uu____48441 = abstr vars body  in
            (qop, uu____48421, wopt, uu____48438, uu____48441)  in
          mkQuant r true uu____48401
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48472  ->
      match uu____48472 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48531  ->
      match uu____48531 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____48606  ->
      match uu____48606 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48669  ->
      match uu____48669 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____48720  ->
    fun r  ->
      match uu____48720 with
      | (bindings,body) ->
          let uu____48746 = FStar_List.split bindings  in
          (match uu____48746 with
           | (vars,es) ->
               let uu____48765 =
                 let uu____48772 = abstr vars body  in (es, uu____48772)  in
               mkLet uu____48765 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____48794  ->
    match uu____48794 with
    | (nm,vars,s,tm,c) ->
        let uu____48819 =
          let uu____48833 = FStar_List.map fv_sort vars  in
          let uu____48836 = abstr vars tm  in
          (nm, uu____48833, s, uu____48836, c)  in
        DefineFun uu____48819
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____48847 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____48847
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____48865  ->
    fun id1  ->
      match uu____48865 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____48881 =
              let uu____48882 =
                let uu____48887 = mkInteger' id1 norng  in
                let uu____48888 =
                  let uu____48889 =
                    let uu____48897 = constr_id_of_sort sort  in
                    let uu____48899 =
                      let uu____48902 = mkApp (tok_name, []) norng  in
                      [uu____48902]  in
                    (uu____48897, uu____48899)  in
                  mkApp uu____48889 norng  in
                (uu____48887, uu____48888)  in
              mkEq uu____48882 norng  in
            let uu____48909 = escape a_name  in
            {
              assumption_term = uu____48881;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____48909;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____48935  ->
      match uu____48935 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____48975 =
                        let uu____48976 =
                          let uu____48982 =
                            let uu____48984 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____48984  in
                          (uu____48982, s)  in
                        mk_fv uu____48976  in
                      mkFreeV uu____48975 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____49012 =
              let uu____49020 = constr_id_of_sort sort  in
              (uu____49020, [capp])  in
            mkApp uu____49012 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____49029 =
              let uu____49030 =
                let uu____49041 =
                  let uu____49042 =
                    let uu____49047 = mkInteger id2 norng  in
                    (uu____49047, cid_app)  in
                  mkEq uu____49042 norng  in
                ([[capp]], bvar_names, uu____49041)  in
              mkForall rng uu____49030  in
            let uu____49056 = escape a_name  in
            {
              assumption_term = uu____49029;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____49056;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____49081  ->
      match uu____49081 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____49114 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____49114  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____49143 =
              let uu____49144 =
                let uu____49150 = bvar_name i  in (uu____49150, s)  in
              mk_fv uu____49144  in
            FStar_All.pipe_left mkFreeV uu____49143  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49186  ->
                      match uu____49186 with
                      | (uu____49196,s,uu____49198) ->
                          let uu____49203 = bvar i s  in uu____49203 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____49231 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49269  ->
                      match uu____49269 with
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
                              let uu____49302 =
                                let uu____49303 =
                                  let uu____49314 =
                                    let uu____49315 =
                                      let uu____49320 =
                                        let uu____49321 = bvar i s  in
                                        uu____49321 norng  in
                                      (cproj_app, uu____49320)  in
                                    mkEq uu____49315 norng  in
                                  ([[capp]], bvar_names, uu____49314)  in
                                mkForall rng uu____49303  in
                              let uu____49334 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____49302;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____49334;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____49231 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____49359  ->
      match uu____49359 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____49407  ->
                    match uu____49407 with
                    | (uu____49416,sort1,uu____49418) -> sort1))
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
              let uu____49443 =
                let uu____49448 =
                  let uu____49449 =
                    let uu____49457 = constr_id_of_sort sort  in
                    (uu____49457, [xx])  in
                  mkApp uu____49449 norng  in
                let uu____49462 =
                  let uu____49463 = FStar_Util.string_of_int id1  in
                  mkInteger uu____49463 norng  in
                (uu____49448, uu____49462)  in
              mkEq uu____49443 norng  in
            let uu____49465 =
              let uu____49484 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____49548  ->
                          match uu____49548 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____49578 = mkApp (proj, [xx]) norng
                                   in
                                (uu____49578, [])
                              else
                                (let fi =
                                   let uu____49587 =
                                     let uu____49593 =
                                       let uu____49595 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____49595  in
                                     (uu____49593, s)  in
                                   mk_fv uu____49587  in
                                 let uu____49599 = mkFreeV fi norng  in
                                 (uu____49599, [fi]))))
                 in
              FStar_All.pipe_right uu____49484 FStar_List.split  in
            match uu____49465 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____49696 =
                    let uu____49701 = mkApp (name, proj_terms) norng  in
                    (xx, uu____49701)  in
                  mkEq uu____49696 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____49714 ->
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
          let uu____49749 =
            let uu____49752 =
              let uu____49753 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____49753  in
            uu____49752 :: cdecl :: cid :: projs  in
          let uu____49756 =
            let uu____49759 =
              let uu____49762 =
                let uu____49763 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____49763  in
              [uu____49762]  in
            FStar_List.append [disc] uu____49759  in
          FStar_List.append uu____49749 uu____49756
  
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
          let uu____49815 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____49864  ->
                    fun s  ->
                      match uu____49864 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____49909 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____49920 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____49920  in
                          let names2 =
                            let uu____49925 = mk_fv (nm, s)  in uu____49925
                              :: names1
                             in
                          let b =
                            let uu____49929 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____49929  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____49815 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____50000 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____50000 with
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
              (let uu____50109 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____50109)
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
                               "Prims.guard_free",{ tm = BoundV uu____50155;
                                                    freevars = uu____50156;
                                                    rng = uu____50157;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____50178 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____50256 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____50256 fv_name
          | FreeV x when fv_force x ->
              let uu____50267 =
                let uu____50269 = fv_name x  in
                Prims.op_Hat uu____50269 " Dummy_value)"  in
              Prims.op_Hat "(" uu____50267
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____50291 = op_to_string op  in
              let uu____50293 =
                let uu____50295 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____50295 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____50291 uu____50293
          | Labeled (t2,uu____50307,uu____50308) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____50315 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____50315 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____50343 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____50343 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____50396 ->
                         let uu____50401 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____50420 =
                                     let uu____50422 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____50430 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____50430) pats2
                                        in
                                     FStar_String.concat " " uu____50422  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____50420))
                            in
                         FStar_All.pipe_right uu____50401
                           (FStar_String.concat "\n")
                      in
                   let uu____50440 =
                     let uu____50444 =
                       let uu____50448 =
                         let uu____50452 = aux1 n2 names2 body  in
                         let uu____50454 =
                           let uu____50458 = weightToSmt wopt  in
                           [uu____50458; pats_str; qid]  in
                         uu____50452 :: uu____50454  in
                       binders1 :: uu____50448  in
                     (qop_to_string qop) :: uu____50444  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____50440)
          | Let (es,body) ->
              let uu____50474 =
                FStar_List.fold_left
                  (fun uu____50507  ->
                     fun e  ->
                       match uu____50507 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____50550 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____50550  in
                           let names01 =
                             let uu____50556 = mk_fv (nm, Term_sort)  in
                             uu____50556 :: names0  in
                           let b =
                             let uu____50560 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____50560  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____50474 with
               | (names2,binders,n2) ->
                   let uu____50594 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____50594)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____50610 = FStar_Range.string_of_range t1.rng  in
            let uu____50612 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____50610
              uu____50612 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_50634  ->
      match uu___408_50634 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____50645 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____50645 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____50667 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____50742 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____50742 (FStar_String.concat "\n")  in
            let uu____50752 = FStar_Options.keep_query_captions ()  in
            if uu____50752
            then
              let uu____50756 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____50758 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____50756 uu____50758
            else res
        | Caption c ->
            if print_captions
            then
              let uu____50767 =
                let uu____50769 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____50769 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____50767
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____50810 = caption_to_string print_captions c  in
            let uu____50812 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____50810 f
              (FStar_String.concat " " l) uu____50812
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____50827 = name_macro_binders arg_sorts  in
            (match uu____50827 with
             | (names1,binders) ->
                 let body1 =
                   let uu____50851 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____50851 body  in
                 let uu____50856 = caption_to_string print_captions c  in
                 let uu____50858 = strSort retsort  in
                 let uu____50860 =
                   let uu____50862 = escape f  in
                   termToSmt print_captions uu____50862 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____50856 f (FStar_String.concat " " binders)
                   uu____50858 uu____50860)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_50889  ->
                      match uu___409_50889 with
                      | Name n1 ->
                          let uu____50892 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____50892
                      | Namespace ns ->
                          let uu____50896 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____50896
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____50906 =
                  let uu____50908 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____50908  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____50906
              else ""  in
            let n1 = a.assumption_name  in
            let uu____50919 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____50921 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____50919
              fids uu____50921 n1
        | Eval t ->
            let uu____50925 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____50925
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____50932 -> ""
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
      let uu____50953 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____50953 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____50964 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____50964 (FStar_String.concat "\n")

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
      let uu____51099 =
        let uu____51103 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____51103
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____51099 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____51134 =
      let uu____51135 =
        let uu____51137 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51137  in
      let uu____51146 =
        let uu____51149 =
          let uu____51150 =
            let uu____51152 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____51152  in
          (uu____51150, (BitVec_sort sz), true)  in
        [uu____51149]  in
      (uu____51135, uu____51146, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____51134 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____51184  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____51209 =
       let uu____51211 = FStar_ST.op_Bang __range_c  in
       uu____51211 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____51209);
    (let uu____51256 =
       let uu____51264 =
         let uu____51267 = mkInteger' i norng  in [uu____51267]  in
       ("Range_const", uu____51264)  in
     mkApp uu____51256 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____51310 =
        let uu____51318 =
          let uu____51321 = mkInteger' i norng  in [uu____51321]  in
        ("Tm_uvar", uu____51318)  in
      mkApp uu____51310 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____51364 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____51388 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____51388 u v1 t
  
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
      let uu____51483 =
        let uu____51485 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51485  in
      let uu____51494 =
        let uu____51496 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51496  in
      elim_box true uu____51483 uu____51494 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____51519 =
        let uu____51521 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51521  in
      let uu____51530 =
        let uu____51532 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51532  in
      elim_box true uu____51519 uu____51530 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____51556 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____51571 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____51597 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____51597
         | uu____51600 -> FStar_Pervasives_Native.None)
    | uu____51602 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____51620::t1::t2::[]);
                       freevars = uu____51623; rng = uu____51624;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____51643::t1::t2::[]);
                       freevars = uu____51646; rng = uu____51647;_}::[])
        -> let uu____51666 = mkEq (t1, t2) norng  in mkNot uu____51666 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____51669; rng = uu____51670;_}::[])
        ->
        let uu____51689 =
          let uu____51694 = unboxInt t1  in
          let uu____51695 = unboxInt t2  in (uu____51694, uu____51695)  in
        mkLTE uu____51689 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____51698; rng = uu____51699;_}::[])
        ->
        let uu____51718 =
          let uu____51723 = unboxInt t1  in
          let uu____51724 = unboxInt t2  in (uu____51723, uu____51724)  in
        mkLT uu____51718 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____51727; rng = uu____51728;_}::[])
        ->
        let uu____51747 =
          let uu____51752 = unboxInt t1  in
          let uu____51753 = unboxInt t2  in (uu____51752, uu____51753)  in
        mkGTE uu____51747 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____51756; rng = uu____51757;_}::[])
        ->
        let uu____51776 =
          let uu____51781 = unboxInt t1  in
          let uu____51782 = unboxInt t2  in (uu____51781, uu____51782)  in
        mkGT uu____51776 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____51785; rng = uu____51786;_}::[])
        ->
        let uu____51805 =
          let uu____51810 = unboxBool t1  in
          let uu____51811 = unboxBool t2  in (uu____51810, uu____51811)  in
        mkAnd uu____51805 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____51814; rng = uu____51815;_}::[])
        ->
        let uu____51834 =
          let uu____51839 = unboxBool t1  in
          let uu____51840 = unboxBool t2  in (uu____51839, uu____51840)  in
        mkOr uu____51834 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____51842; rng = uu____51843;_}::[])
        -> let uu____51862 = unboxBool t1  in mkNot uu____51862 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____51866; rng = uu____51867;_}::[])
        when
        let uu____51886 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51886 ->
        let sz =
          let uu____51893 = getBoxedInteger t0  in
          match uu____51893 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51901 -> failwith "impossible"  in
        let uu____51907 =
          let uu____51912 = unboxBitVec sz t1  in
          let uu____51913 = unboxBitVec sz t2  in (uu____51912, uu____51913)
           in
        mkBvUlt uu____51907 t.rng
    | App
        (Var
         "Prims.equals",uu____51914::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____51918;
                                       rng = uu____51919;_}::uu____51920::[])
        when
        let uu____51939 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51939 ->
        let sz =
          let uu____51946 = getBoxedInteger t0  in
          match uu____51946 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51954 -> failwith "impossible"  in
        let uu____51960 =
          let uu____51965 = unboxBitVec sz t1  in
          let uu____51966 = unboxBitVec sz t2  in (uu____51965, uu____51966)
           in
        mkBvUlt uu____51960 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_51971 = unboxBool t1  in
        {
          tm = (uu___1789_51971.tm);
          freevars = (uu___1789_51971.freevars);
          rng = (t.rng)
        }
    | uu____51972 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____52033 = FStar_Options.unthrottle_inductives ()  in
        if uu____52033
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
    let uu____52166 =
      let uu____52167 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____52167 t t.rng  in
    FStar_All.pipe_right uu____52166 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____52185 =
        let uu____52193 =
          let uu____52196 = mkInteger' i norng  in [uu____52196]  in
        ("FString_const", uu____52193)  in
      mkApp uu____52185 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____52227 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____52227 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____52274 =
         let uu____52282 =
           let uu____52285 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____52285]  in
         ("SFuel", uu____52282)  in
       mkApp uu____52274 norng)
  
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
            let uu____52333 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____52333
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
      let uu____52396 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____52396
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____52416 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____52416
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____52427 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____52427
  
let (dummy_sort : sort) = Sort "Dummy_sort" 