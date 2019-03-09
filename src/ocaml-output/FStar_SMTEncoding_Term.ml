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
    match projectee with | Bool_sort  -> true | uu____42902 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____42913 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____42924 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____42935 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____42946 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____42959 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____42985 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____43020 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____43052 -> false
  
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
        let uu____43079 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____43079
    | Array (s1,s2) ->
        let uu____43084 = strSort s1  in
        let uu____43086 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____43084 uu____43086
    | Arrow (s1,s2) ->
        let uu____43091 = strSort s1  in
        let uu____43093 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____43091 uu____43093
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
    match projectee with | TrueOp  -> true | uu____43125 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____43136 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____43147 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____43158 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____43169 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____43180 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____43191 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____43202 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____43213 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____43224 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____43235 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____43246 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____43257 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____43268 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____43279 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____43290 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____43301 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____43312 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____43323 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____43334 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____43345 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____43356 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____43367 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____43378 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____43389 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____43400 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____43411 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____43422 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____43433 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____43444 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____43457 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____43480 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____43501 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____43512 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____43525 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____43546 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____43557 -> false
  
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
    match projectee with | Integer _0 -> true | uu____43706 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____43729 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____43752 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____43782 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____43831 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____43887 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____43969 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____44013 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____44058 -> false
  
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
    match projectee with | Name _0 -> true | uu____44248 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____44267 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____44287 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____44476 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____44499 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____44564 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____44622 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____44642 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____44671 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____44711 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____44731 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____44756 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____44783 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____44794 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____44805 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____44816 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____44834 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____44870 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____44881 -> false
  
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
          let uu____45055 =
            let uu____45056 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____45082 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____45056
            }  in
          [uu____45055]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____45096 =
      let uu____45097 =
        FStar_List.collect
          (fun uu___402_45104  ->
             match uu___402_45104 with
             | Assume a -> [a.assumption_name]
             | uu____45111 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____45097
      }  in
    [uu____45096]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____45148  -> match uu____45148 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____45168 = x  in
    match uu____45168 with | (nm,uu____45171,uu____45172) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____45183 = x  in
    match uu____45183 with | (uu____45184,sort,uu____45186) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____45198 = x  in
    match uu____45198 with | (uu____45200,uu____45201,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____45219 = fv_name x  in
      let uu____45221 = fv_name y  in uu____45219 = uu____45221
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____45255 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_45266  ->
    match uu___403_45266 with
    | { tm = FreeV x; freevars = uu____45268; rng = uu____45269;_} ->
        fv_sort x
    | uu____45290 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_45297  ->
    match uu___404_45297 with
    | { tm = FreeV fv; freevars = uu____45299; rng = uu____45300;_} -> fv
    | uu____45321 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____45349 -> []
    | Real uu____45359 -> []
    | BoundV uu____45369 -> []
    | FreeV fv -> [fv]
    | App (uu____45404,tms) -> FStar_List.collect freevars tms
    | Quant (uu____45418,uu____45419,uu____45420,uu____45421,t1) ->
        freevars t1
    | Labeled (t1,uu____45442,uu____45443) -> freevars t1
    | LblPos (t1,uu____45447) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____45470 = FStar_ST.op_Bang t.freevars  in
    match uu____45470 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____45568 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____45568  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_45647  ->
    match uu___405_45647 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_45657  ->
    match uu___406_45657 with
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
        let uu____45693 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____45693
    | NatToBv n1 ->
        let uu____45698 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____45698
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_45712  ->
    match uu___407_45712 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____45722 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____45722
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____45744 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____45744
    | FreeV x ->
        let uu____45756 = fv_name x  in
        let uu____45758 =
          let uu____45760 =
            let uu____45762 = fv_sort x  in strSort uu____45762  in
          Prims.op_Hat ":" uu____45760  in
        Prims.op_Hat uu____45756 uu____45758
    | App (op,tms) ->
        let uu____45770 =
          let uu____45772 = op_to_string op  in
          let uu____45774 =
            let uu____45776 =
              let uu____45778 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____45778 (FStar_String.concat " ")  in
            Prims.op_Hat uu____45776 ")"  in
          Prims.op_Hat uu____45772 uu____45774  in
        Prims.op_Hat "(" uu____45770
    | Labeled (t1,r1,r2) ->
        let uu____45795 = hash_of_term t1  in
        let uu____45797 =
          let uu____45799 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____45799  in
        Prims.op_Hat uu____45795 uu____45797
    | LblPos (t1,r) ->
        let uu____45805 =
          let uu____45807 = hash_of_term t1  in
          Prims.op_Hat uu____45807
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____45805
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____45835 =
          let uu____45837 =
            let uu____45839 =
              let uu____45841 =
                let uu____45843 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____45843 (FStar_String.concat " ")
                 in
              let uu____45853 =
                let uu____45855 =
                  let uu____45857 = hash_of_term body  in
                  let uu____45859 =
                    let uu____45861 =
                      let uu____45863 = weightToSmt wopt  in
                      let uu____45865 =
                        let uu____45867 =
                          let uu____45869 =
                            let uu____45871 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____45890 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____45890
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____45871
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____45869 "))"  in
                        Prims.op_Hat " " uu____45867  in
                      Prims.op_Hat uu____45863 uu____45865  in
                    Prims.op_Hat " " uu____45861  in
                  Prims.op_Hat uu____45857 uu____45859  in
                Prims.op_Hat ")(! " uu____45855  in
              Prims.op_Hat uu____45841 uu____45853  in
            Prims.op_Hat " (" uu____45839  in
          Prims.op_Hat (qop_to_string qop) uu____45837  in
        Prims.op_Hat "(" uu____45835
    | Let (es,body) ->
        let uu____45917 =
          let uu____45919 =
            let uu____45921 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____45921 (FStar_String.concat " ")  in
          let uu____45931 =
            let uu____45933 =
              let uu____45935 = hash_of_term body  in
              Prims.op_Hat uu____45935 ")"  in
            Prims.op_Hat ") " uu____45933  in
          Prims.op_Hat uu____45919 uu____45931  in
        Prims.op_Hat "(let (" uu____45917

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____45996 =
      let uu____45998 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____45998  in
    mkBoxFunctions uu____45996
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____46023 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____46023 = "Box") &&
        (let uu____46030 =
           let uu____46032 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____46032  in
         Prims.op_Negation uu____46030)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____46056 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____46056; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46120 =
        let uu____46121 = FStar_Util.ensure_decimal i  in Integer uu____46121
         in
      mk uu____46120 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46136 = FStar_Util.string_of_int i  in
      mkInteger uu____46136 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____46214  ->
    fun r  -> match uu____46214 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____46244) -> mkFalse r
      | App (FalseOp ,uu____46249) -> mkTrue r
      | uu____46254 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____46270  ->
    fun r  ->
      match uu____46270 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46278),uu____46279) -> t2
           | (uu____46284,App (TrueOp ,uu____46285)) -> t1
           | (App (FalseOp ,uu____46290),uu____46291) -> mkFalse r
           | (uu____46296,App (FalseOp ,uu____46297)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____46314,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____46323) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____46330 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____46350  ->
    fun r  ->
      match uu____46350 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46358),uu____46359) -> mkTrue r
           | (uu____46364,App (TrueOp ,uu____46365)) -> mkTrue r
           | (App (FalseOp ,uu____46370),uu____46371) -> t2
           | (uu____46376,App (FalseOp ,uu____46377)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____46394,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____46403) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____46410 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____46430  ->
    fun r  ->
      match uu____46430 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____46438,App (TrueOp ,uu____46439)) -> mkTrue r
           | (App (FalseOp ,uu____46444),uu____46445) -> mkTrue r
           | (App (TrueOp ,uu____46450),uu____46451) -> t2
           | (uu____46456,App (Imp ,t1'::t2'::[])) ->
               let uu____46461 =
                 let uu____46468 =
                   let uu____46471 = mkAnd (t1, t1') r  in [uu____46471; t2']
                    in
                 (Imp, uu____46468)  in
               mkApp' uu____46461 r
           | uu____46474 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____46499  ->
      fun r  -> match uu____46499 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____46659  ->
      fun r  ->
        match uu____46659 with
        | (t1,t2) ->
            let uu____46668 =
              let uu____46675 =
                let uu____46678 =
                  let uu____46681 = mkNatToBv sz t2 r  in [uu____46681]  in
                t1 :: uu____46678  in
              (BvShl, uu____46675)  in
            mkApp' uu____46668 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46703  ->
      fun r  ->
        match uu____46703 with
        | (t1,t2) ->
            let uu____46712 =
              let uu____46719 =
                let uu____46722 =
                  let uu____46725 = mkNatToBv sz t2 r  in [uu____46725]  in
                t1 :: uu____46722  in
              (BvShr, uu____46719)  in
            mkApp' uu____46712 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46747  ->
      fun r  ->
        match uu____46747 with
        | (t1,t2) ->
            let uu____46756 =
              let uu____46763 =
                let uu____46766 =
                  let uu____46769 = mkNatToBv sz t2 r  in [uu____46769]  in
                t1 :: uu____46766  in
              (BvUdiv, uu____46763)  in
            mkApp' uu____46756 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46791  ->
      fun r  ->
        match uu____46791 with
        | (t1,t2) ->
            let uu____46800 =
              let uu____46807 =
                let uu____46810 =
                  let uu____46813 = mkNatToBv sz t2 r  in [uu____46813]  in
                t1 :: uu____46810  in
              (BvMod, uu____46807)  in
            mkApp' uu____46800 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46835  ->
      fun r  ->
        match uu____46835 with
        | (t1,t2) ->
            let uu____46844 =
              let uu____46851 =
                let uu____46854 =
                  let uu____46857 = mkNatToBv sz t2 r  in [uu____46857]  in
                t1 :: uu____46854  in
              (BvMul, uu____46851)  in
            mkApp' uu____46844 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____46899  ->
    fun r  ->
      match uu____46899 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____46918 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____47083  ->
    fun r  ->
      match uu____47083 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____47094) -> t2
           | App (FalseOp ,uu____47099) -> t3
           | uu____47104 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____47105),App (TrueOp ,uu____47106)) ->
                    mkTrue r
                | (App (TrueOp ,uu____47115),uu____47116) ->
                    let uu____47121 =
                      let uu____47126 = mkNot t1 t1.rng  in (uu____47126, t3)
                       in
                    mkImp uu____47121 r
                | (uu____47127,App (TrueOp ,uu____47128)) -> mkImp (t1, t2) r
                | (uu____47133,uu____47134) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____47190 -> FStar_Pervasives_Native.None
      | Real uu____47192 -> FStar_Pervasives_Native.None
      | BoundV uu____47194 -> FStar_Pervasives_Native.None
      | FreeV uu____47196 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____47220 -> true
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
            | BvUext uu____47253 -> false
            | NatToBv uu____47256 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____47267,uu____47268) -> aux t2
      | Quant uu____47271 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____47291 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____47306 = aux t1  in
          (match uu____47306 with
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
        let uu____47344 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____47344
    | FreeV fv ->
        let uu____47356 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____47356
    | App (op,l) ->
        let uu____47365 = op_to_string op  in
        let uu____47367 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____47365 uu____47367
    | Labeled (t1,r1,r2) ->
        let uu____47375 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____47375
    | LblPos (t1,s) ->
        let uu____47382 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____47382
    | Quant (qop,l,uu____47387,uu____47388,t1) ->
        let uu____47408 = print_smt_term_list_list l  in
        let uu____47410 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____47408
          uu____47410
    | Let (es,body) ->
        let uu____47419 = print_smt_term_list es  in
        let uu____47421 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____47419 uu____47421

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____47428 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____47428 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____47455 =
             let uu____47457 =
               let uu____47459 = print_smt_term_list l1  in
               Prims.op_Hat uu____47459 " ] "  in
             Prims.op_Hat "; [ " uu____47457  in
           Prims.op_Hat s uu____47455) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____47499  ->
        match uu____47499 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____47568 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____47568 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____47583 =
                         let uu____47589 =
                           let uu____47591 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____47591
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____47589)
                          in
                       FStar_Errors.log_issue r uu____47583);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____47602) -> body
               | uu____47607 ->
                   let uu____47608 =
                     let uu____47609 =
                       let uu____47629 = all_pats_ok pats  in
                       (qop, uu____47629, wopt, vars, body)  in
                     Quant uu____47609  in
                   mk uu____47608 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____47658  ->
    fun r  ->
      match uu____47658 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____47704 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____47704 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____47731 = FStar_ST.op_Bang t1.freevars  in
        match uu____47731 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____47805 ->
            (match t1.tm with
             | Integer uu____47818 -> t1
             | Real uu____47820 -> t1
             | BoundV uu____47822 -> t1
             | FreeV x ->
                 let uu____47833 = index_of1 x  in
                 (match uu____47833 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____47847 =
                   let uu____47854 = FStar_List.map (aux ix) tms  in
                   (op, uu____47854)  in
                 mkApp' uu____47847 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____47864 =
                   let uu____47865 =
                     let uu____47873 = aux ix t2  in (uu____47873, r1, r2)
                      in
                   Labeled uu____47865  in
                 mk uu____47864 t2.rng
             | LblPos (t2,r) ->
                 let uu____47879 =
                   let uu____47880 =
                     let uu____47886 = aux ix t2  in (uu____47886, r)  in
                   LblPos uu____47880  in
                 mk uu____47879 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____47912 =
                   let uu____47932 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____47949 = aux (ix + n1) body  in
                   (qop, uu____47932, wopt, vars, uu____47949)  in
                 mkQuant t1.rng false uu____47912
             | Let (es,body) ->
                 let uu____47966 =
                   FStar_List.fold_left
                     (fun uu____47986  ->
                        fun e  ->
                          match uu____47986 with
                          | (ix1,l) ->
                              let uu____48010 =
                                let uu____48013 = aux ix1 e  in uu____48013
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____48010))
                     (ix, []) es
                    in
                 (match uu____47966 with
                  | (ix1,es_rev) ->
                      let uu____48029 =
                        let uu____48036 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____48036)  in
                      mkLet uu____48029 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____48072 -> t1
        | Real uu____48074 -> t1
        | FreeV uu____48076 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____48097 =
              let uu____48104 = FStar_List.map (aux shift) tms2  in
              (op, uu____48104)  in
            mkApp' uu____48097 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____48114 =
              let uu____48115 =
                let uu____48123 = aux shift t2  in (uu____48123, r1, r2)  in
              Labeled uu____48115  in
            mk uu____48114 t2.rng
        | LblPos (t2,r) ->
            let uu____48129 =
              let uu____48130 =
                let uu____48136 = aux shift t2  in (uu____48136, r)  in
              LblPos uu____48130  in
            mk uu____48129 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____48164 =
              let uu____48184 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____48201 = aux shift1 body  in
              (qop, uu____48184, wopt, vars, uu____48201)  in
            mkQuant t1.rng false uu____48164
        | Let (es,body) ->
            let uu____48218 =
              FStar_List.fold_left
                (fun uu____48238  ->
                   fun e  ->
                     match uu____48238 with
                     | (ix,es1) ->
                         let uu____48262 =
                           let uu____48265 = aux shift e  in uu____48265 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____48262))
                (shift, []) es
               in
            (match uu____48218 with
             | (shift1,es_rev) ->
                 let uu____48281 =
                   let uu____48288 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____48288)  in
                 mkLet uu____48281 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____48308 = abstr [fv] t  in inst [s] uu____48308
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48338  ->
      match uu____48338 with
      | (qop,pats,wopt,vars,body) ->
          let uu____48381 =
            let uu____48401 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____48418 = FStar_List.map fv_sort vars  in
            let uu____48421 = abstr vars body  in
            (qop, uu____48401, wopt, uu____48418, uu____48421)  in
          mkQuant r true uu____48381
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48452  ->
      match uu____48452 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48511  ->
      match uu____48511 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____48586  ->
      match uu____48586 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48649  ->
      match uu____48649 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____48700  ->
    fun r  ->
      match uu____48700 with
      | (bindings,body) ->
          let uu____48726 = FStar_List.split bindings  in
          (match uu____48726 with
           | (vars,es) ->
               let uu____48745 =
                 let uu____48752 = abstr vars body  in (es, uu____48752)  in
               mkLet uu____48745 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____48774  ->
    match uu____48774 with
    | (nm,vars,s,tm,c) ->
        let uu____48799 =
          let uu____48813 = FStar_List.map fv_sort vars  in
          let uu____48816 = abstr vars tm  in
          (nm, uu____48813, s, uu____48816, c)  in
        DefineFun uu____48799
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____48827 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____48827
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____48845  ->
    fun id1  ->
      match uu____48845 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____48861 =
              let uu____48862 =
                let uu____48867 = mkInteger' id1 norng  in
                let uu____48868 =
                  let uu____48869 =
                    let uu____48877 = constr_id_of_sort sort  in
                    let uu____48879 =
                      let uu____48882 = mkApp (tok_name, []) norng  in
                      [uu____48882]  in
                    (uu____48877, uu____48879)  in
                  mkApp uu____48869 norng  in
                (uu____48867, uu____48868)  in
              mkEq uu____48862 norng  in
            let uu____48889 = escape a_name  in
            {
              assumption_term = uu____48861;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____48889;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____48915  ->
      match uu____48915 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____48955 =
                        let uu____48956 =
                          let uu____48962 =
                            let uu____48964 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____48964  in
                          (uu____48962, s)  in
                        mk_fv uu____48956  in
                      mkFreeV uu____48955 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____48992 =
              let uu____49000 = constr_id_of_sort sort  in
              (uu____49000, [capp])  in
            mkApp uu____48992 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____49009 =
              let uu____49010 =
                let uu____49021 =
                  let uu____49022 =
                    let uu____49027 = mkInteger id2 norng  in
                    (uu____49027, cid_app)  in
                  mkEq uu____49022 norng  in
                ([[capp]], bvar_names, uu____49021)  in
              mkForall rng uu____49010  in
            let uu____49036 = escape a_name  in
            {
              assumption_term = uu____49009;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____49036;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____49061  ->
      match uu____49061 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____49094 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____49094  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____49123 =
              let uu____49124 =
                let uu____49130 = bvar_name i  in (uu____49130, s)  in
              mk_fv uu____49124  in
            FStar_All.pipe_left mkFreeV uu____49123  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49166  ->
                      match uu____49166 with
                      | (uu____49176,s,uu____49178) ->
                          let uu____49183 = bvar i s  in uu____49183 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____49211 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49249  ->
                      match uu____49249 with
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
                              let uu____49282 =
                                let uu____49283 =
                                  let uu____49294 =
                                    let uu____49295 =
                                      let uu____49300 =
                                        let uu____49301 = bvar i s  in
                                        uu____49301 norng  in
                                      (cproj_app, uu____49300)  in
                                    mkEq uu____49295 norng  in
                                  ([[capp]], bvar_names, uu____49294)  in
                                mkForall rng uu____49283  in
                              let uu____49314 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____49282;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____49314;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____49211 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____49339  ->
      match uu____49339 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____49387  ->
                    match uu____49387 with
                    | (uu____49396,sort1,uu____49398) -> sort1))
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
              let uu____49423 =
                let uu____49428 =
                  let uu____49429 =
                    let uu____49437 = constr_id_of_sort sort  in
                    (uu____49437, [xx])  in
                  mkApp uu____49429 norng  in
                let uu____49442 =
                  let uu____49443 = FStar_Util.string_of_int id1  in
                  mkInteger uu____49443 norng  in
                (uu____49428, uu____49442)  in
              mkEq uu____49423 norng  in
            let uu____49445 =
              let uu____49464 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____49528  ->
                          match uu____49528 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____49558 = mkApp (proj, [xx]) norng
                                   in
                                (uu____49558, [])
                              else
                                (let fi =
                                   let uu____49567 =
                                     let uu____49573 =
                                       let uu____49575 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____49575  in
                                     (uu____49573, s)  in
                                   mk_fv uu____49567  in
                                 let uu____49579 = mkFreeV fi norng  in
                                 (uu____49579, [fi]))))
                 in
              FStar_All.pipe_right uu____49464 FStar_List.split  in
            match uu____49445 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____49676 =
                    let uu____49681 = mkApp (name, proj_terms) norng  in
                    (xx, uu____49681)  in
                  mkEq uu____49676 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____49694 ->
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
          let uu____49729 =
            let uu____49732 =
              let uu____49733 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____49733  in
            uu____49732 :: cdecl :: cid :: projs  in
          let uu____49736 =
            let uu____49739 =
              let uu____49742 =
                let uu____49743 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____49743  in
              [uu____49742]  in
            FStar_List.append [disc] uu____49739  in
          FStar_List.append uu____49729 uu____49736
  
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
          let uu____49795 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____49844  ->
                    fun s  ->
                      match uu____49844 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____49889 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____49900 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____49900  in
                          let names2 =
                            let uu____49905 = mk_fv (nm, s)  in uu____49905
                              :: names1
                             in
                          let b =
                            let uu____49909 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____49909  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____49795 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____49980 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____49980 with
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
              (let uu____50089 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____50089)
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
                               "Prims.guard_free",{ tm = BoundV uu____50135;
                                                    freevars = uu____50136;
                                                    rng = uu____50137;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____50158 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____50236 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____50236 fv_name
          | FreeV x when fv_force x ->
              let uu____50247 =
                let uu____50249 = fv_name x  in
                Prims.op_Hat uu____50249 " Dummy_value)"  in
              Prims.op_Hat "(" uu____50247
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____50271 = op_to_string op  in
              let uu____50273 =
                let uu____50275 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____50275 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____50271 uu____50273
          | Labeled (t2,uu____50287,uu____50288) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____50295 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____50295 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____50323 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____50323 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____50376 ->
                         let uu____50381 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____50400 =
                                     let uu____50402 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____50410 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____50410) pats2
                                        in
                                     FStar_String.concat " " uu____50402  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____50400))
                            in
                         FStar_All.pipe_right uu____50381
                           (FStar_String.concat "\n")
                      in
                   let uu____50420 =
                     let uu____50424 =
                       let uu____50428 =
                         let uu____50432 = aux1 n2 names2 body  in
                         let uu____50434 =
                           let uu____50438 = weightToSmt wopt  in
                           [uu____50438; pats_str; qid]  in
                         uu____50432 :: uu____50434  in
                       binders1 :: uu____50428  in
                     (qop_to_string qop) :: uu____50424  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____50420)
          | Let (es,body) ->
              let uu____50454 =
                FStar_List.fold_left
                  (fun uu____50487  ->
                     fun e  ->
                       match uu____50487 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____50530 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____50530  in
                           let names01 =
                             let uu____50536 = mk_fv (nm, Term_sort)  in
                             uu____50536 :: names0  in
                           let b =
                             let uu____50540 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____50540  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____50454 with
               | (names2,binders,n2) ->
                   let uu____50574 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____50574)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____50590 = FStar_Range.string_of_range t1.rng  in
            let uu____50592 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____50590
              uu____50592 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_50614  ->
      match uu___408_50614 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____50625 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____50625 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____50647 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____50722 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____50722 (FStar_String.concat "\n")  in
            let uu____50732 = FStar_Options.keep_query_captions ()  in
            if uu____50732
            then
              let uu____50736 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____50738 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____50736 uu____50738
            else res
        | Caption c ->
            if print_captions
            then
              let uu____50747 =
                let uu____50749 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____50749 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____50747
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____50790 = caption_to_string print_captions c  in
            let uu____50792 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____50790 f
              (FStar_String.concat " " l) uu____50792
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____50807 = name_macro_binders arg_sorts  in
            (match uu____50807 with
             | (names1,binders) ->
                 let body1 =
                   let uu____50831 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____50831 body  in
                 let uu____50836 = caption_to_string print_captions c  in
                 let uu____50838 = strSort retsort  in
                 let uu____50840 =
                   let uu____50842 = escape f  in
                   termToSmt print_captions uu____50842 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____50836 f (FStar_String.concat " " binders)
                   uu____50838 uu____50840)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_50869  ->
                      match uu___409_50869 with
                      | Name n1 ->
                          let uu____50872 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____50872
                      | Namespace ns ->
                          let uu____50876 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____50876
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____50886 =
                  let uu____50888 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____50888  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____50886
              else ""  in
            let n1 = a.assumption_name  in
            let uu____50899 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____50901 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____50899
              fids uu____50901 n1
        | Eval t ->
            let uu____50905 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____50905
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____50912 -> ""
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
      let uu____50933 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____50933 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____50944 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____50944 (FStar_String.concat "\n")

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
      let uu____51079 =
        let uu____51083 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____51083
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____51079 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____51114 =
      let uu____51115 =
        let uu____51117 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51117  in
      let uu____51126 =
        let uu____51129 =
          let uu____51130 =
            let uu____51132 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____51132  in
          (uu____51130, (BitVec_sort sz), true)  in
        [uu____51129]  in
      (uu____51115, uu____51126, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____51114 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____51164  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____51189 =
       let uu____51191 = FStar_ST.op_Bang __range_c  in
       uu____51191 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____51189);
    (let uu____51236 =
       let uu____51244 =
         let uu____51247 = mkInteger' i norng  in [uu____51247]  in
       ("Range_const", uu____51244)  in
     mkApp uu____51236 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____51290 =
        let uu____51298 =
          let uu____51301 = mkInteger' i norng  in [uu____51301]  in
        ("Tm_uvar", uu____51298)  in
      mkApp uu____51290 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____51344 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____51368 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____51368 u v1 t
  
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
      let uu____51463 =
        let uu____51465 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51465  in
      let uu____51474 =
        let uu____51476 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51476  in
      elim_box true uu____51463 uu____51474 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____51499 =
        let uu____51501 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51501  in
      let uu____51510 =
        let uu____51512 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51512  in
      elim_box true uu____51499 uu____51510 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____51536 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____51551 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____51577 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____51577
         | uu____51580 -> FStar_Pervasives_Native.None)
    | uu____51582 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____51600::t1::t2::[]);
                       freevars = uu____51603; rng = uu____51604;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____51623::t1::t2::[]);
                       freevars = uu____51626; rng = uu____51627;_}::[])
        -> let uu____51646 = mkEq (t1, t2) norng  in mkNot uu____51646 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____51649; rng = uu____51650;_}::[])
        ->
        let uu____51669 =
          let uu____51674 = unboxInt t1  in
          let uu____51675 = unboxInt t2  in (uu____51674, uu____51675)  in
        mkLTE uu____51669 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____51678; rng = uu____51679;_}::[])
        ->
        let uu____51698 =
          let uu____51703 = unboxInt t1  in
          let uu____51704 = unboxInt t2  in (uu____51703, uu____51704)  in
        mkLT uu____51698 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____51707; rng = uu____51708;_}::[])
        ->
        let uu____51727 =
          let uu____51732 = unboxInt t1  in
          let uu____51733 = unboxInt t2  in (uu____51732, uu____51733)  in
        mkGTE uu____51727 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____51736; rng = uu____51737;_}::[])
        ->
        let uu____51756 =
          let uu____51761 = unboxInt t1  in
          let uu____51762 = unboxInt t2  in (uu____51761, uu____51762)  in
        mkGT uu____51756 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____51765; rng = uu____51766;_}::[])
        ->
        let uu____51785 =
          let uu____51790 = unboxBool t1  in
          let uu____51791 = unboxBool t2  in (uu____51790, uu____51791)  in
        mkAnd uu____51785 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____51794; rng = uu____51795;_}::[])
        ->
        let uu____51814 =
          let uu____51819 = unboxBool t1  in
          let uu____51820 = unboxBool t2  in (uu____51819, uu____51820)  in
        mkOr uu____51814 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____51822; rng = uu____51823;_}::[])
        -> let uu____51842 = unboxBool t1  in mkNot uu____51842 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____51846; rng = uu____51847;_}::[])
        when
        let uu____51866 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51866 ->
        let sz =
          let uu____51873 = getBoxedInteger t0  in
          match uu____51873 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51881 -> failwith "impossible"  in
        let uu____51887 =
          let uu____51892 = unboxBitVec sz t1  in
          let uu____51893 = unboxBitVec sz t2  in (uu____51892, uu____51893)
           in
        mkBvUlt uu____51887 t.rng
    | App
        (Var
         "Prims.equals",uu____51894::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____51898;
                                       rng = uu____51899;_}::uu____51900::[])
        when
        let uu____51919 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51919 ->
        let sz =
          let uu____51926 = getBoxedInteger t0  in
          match uu____51926 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51934 -> failwith "impossible"  in
        let uu____51940 =
          let uu____51945 = unboxBitVec sz t1  in
          let uu____51946 = unboxBitVec sz t2  in (uu____51945, uu____51946)
           in
        mkBvUlt uu____51940 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_51951 = unboxBool t1  in
        {
          tm = (uu___1789_51951.tm);
          freevars = (uu___1789_51951.freevars);
          rng = (t.rng)
        }
    | uu____51952 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____52013 = FStar_Options.unthrottle_inductives ()  in
        if uu____52013
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
    let uu____52146 =
      let uu____52147 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____52147 t t.rng  in
    FStar_All.pipe_right uu____52146 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____52165 =
        let uu____52173 =
          let uu____52176 = mkInteger' i norng  in [uu____52176]  in
        ("FString_const", uu____52173)  in
      mkApp uu____52165 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____52207 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____52207 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____52254 =
         let uu____52262 =
           let uu____52265 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____52265]  in
         ("SFuel", uu____52262)  in
       mkApp uu____52254 norng)
  
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
            let uu____52313 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____52313
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
      let uu____52376 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____52376
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____52396 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____52396
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____52407 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____52407
  
let (dummy_sort : sort) = Sort "Dummy_sort" 