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
    match projectee with | Bool_sort  -> true | uu____42889 -> false
  
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____42900 -> false
  
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____42911 -> false
  
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____42922 -> false
  
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____42933 -> false
  
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | BitVec_sort _0 -> true | uu____42946 -> false
  
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee  -> match projectee with | BitVec_sort _0 -> _0 
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____42972 -> false
  
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____43007 -> false
  
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____43039 -> false
  
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
        let uu____43066 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ BitVec %s)" uu____43066
    | Array (s1,s2) ->
        let uu____43071 = strSort s1  in
        let uu____43073 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____43071 uu____43073
    | Arrow (s1,s2) ->
        let uu____43078 = strSort s1  in
        let uu____43080 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" uu____43078 uu____43080
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
    match projectee with | TrueOp  -> true | uu____43112 -> false
  
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____43123 -> false
  
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not  -> true | uu____43134 -> false
  
let (uu___is_And : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | And  -> true | uu____43145 -> false
  
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____43156 -> false 
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp  -> true | uu____43167 -> false
  
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iff  -> true | uu____43178 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____43189 -> false 
let (uu___is_LT : op -> Prims.bool) =
  fun projectee  -> match projectee with | LT  -> true | uu____43200 -> false 
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LTE  -> true | uu____43211 -> false
  
let (uu___is_GT : op -> Prims.bool) =
  fun projectee  -> match projectee with | GT  -> true | uu____43222 -> false 
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTE  -> true | uu____43233 -> false
  
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Add  -> true | uu____43244 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sub  -> true | uu____43255 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Div  -> true | uu____43266 -> false
  
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | RealDiv  -> true | uu____43277 -> false
  
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mul  -> true | uu____43288 -> false
  
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____43299 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mod  -> true | uu____43310 -> false
  
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAnd  -> true | uu____43321 -> false
  
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvXor  -> true | uu____43332 -> false
  
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvOr  -> true | uu____43343 -> false
  
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvAdd  -> true | uu____43354 -> false
  
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvSub  -> true | uu____43365 -> false
  
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShl  -> true | uu____43376 -> false
  
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvShr  -> true | uu____43387 -> false
  
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUdiv  -> true | uu____43398 -> false
  
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMod  -> true | uu____43409 -> false
  
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvMul  -> true | uu____43420 -> false
  
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUlt  -> true | uu____43431 -> false
  
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvUext _0 -> true | uu____43444 -> false
  
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | BvUext _0 -> _0 
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____43467 -> false
  
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BvToNat  -> true | uu____43488 -> false
  
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ITE  -> true | uu____43499 -> false
  
let (uu___is_Var : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____43512 -> false
  
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____43533 -> false
  
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____43544 -> false
  
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
    match projectee with | Integer _0 -> true | uu____43693 -> false
  
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Real _0 -> true | uu____43716 -> false
  
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee  -> match projectee with | Real _0 -> _0 
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____43739 -> false
  
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____43769 -> false
  
let (__proj__FreeV__item___0 : term' -> (Prims.string * sort * Prims.bool)) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____43818 -> false
  
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____43874 -> false
  
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____43956 -> false
  
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____44000 -> false
  
let (__proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____44045 -> false
  
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
    match projectee with | Name _0 -> true | uu____44235 -> false
  
let (__proj__Name__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____44254 -> false
  
let (__proj__Namespace__item___0 : fact_db_id -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____44274 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____44463 -> false
  
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____44486 -> false
  
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____44551 -> false
  
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____44609 -> false
  
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____44629 -> false
  
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____44658 -> false
  
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____44698 -> false
  
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____44718 -> false
  
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | RetainAssumptions _0 -> true
    | uu____44743 -> false
  
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0 
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push  -> true | uu____44770 -> false
  
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____44781 -> false
  
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____44792 -> false
  
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____44803 -> false
  
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____44821 -> false
  
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____44857 -> false
  
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____44868 -> false
  
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
          let uu____45042 =
            let uu____45043 =
              let sm = FStar_Util.smap_create (Prims.parse_int "20")  in
              FStar_List.iter
                (fun elt  ->
                   FStar_List.iter (fun s  -> FStar_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStar_List.iter
                (fun d  ->
                   match d with
                   | Assume a -> FStar_Util.smap_add sm a.assumption_name "0"
                   | uu____45069 -> ()) decls;
              FStar_Util.smap_keys sm  in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu____45043
            }  in
          [uu____45042]
  
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls  ->
    let uu____45083 =
      let uu____45084 =
        FStar_List.collect
          (fun uu___402_45091  ->
             match uu___402_45091 with
             | Assume a -> [a.assumption_name]
             | uu____45098 -> []) decls
         in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu____45084
      }  in
    [uu____45083]
  
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l  ->
    FStar_All.pipe_right l (FStar_List.collect (fun elt  -> elt.decls))
  
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu____45135  -> match uu____45135 with | (x,y) -> (x, y, false) 
let (fv_name : fv -> Prims.string) =
  fun x  ->
    let uu____45155 = x  in
    match uu____45155 with | (nm,uu____45158,uu____45159) -> nm
  
let (fv_sort : fv -> sort) =
  fun x  ->
    let uu____45170 = x  in
    match uu____45170 with | (uu____45171,sort,uu____45173) -> sort
  
let (fv_force : fv -> Prims.bool) =
  fun x  ->
    let uu____45185 = x  in
    match uu____45185 with | (uu____45187,uu____45188,force) -> force
  
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x  ->
    fun y  ->
      let uu____45206 = fv_name x  in
      let uu____45208 = fv_name y  in uu____45206 = uu____45208
  
let (freevar_eq : term -> term -> Prims.bool) =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____45242 -> false
  
let (freevar_sort : term -> sort) =
  fun uu___403_45253  ->
    match uu___403_45253 with
    | { tm = FreeV x; freevars = uu____45255; rng = uu____45256;_} ->
        fv_sort x
    | uu____45277 -> failwith "impossible"
  
let (fv_of_term : term -> fv) =
  fun uu___404_45284  ->
    match uu___404_45284 with
    | { tm = FreeV fv; freevars = uu____45286; rng = uu____45287;_} -> fv
    | uu____45308 -> failwith "impossible"
  
let rec (freevars : term -> (Prims.string * sort * Prims.bool) Prims.list) =
  fun t  ->
    match t.tm with
    | Integer uu____45336 -> []
    | Real uu____45346 -> []
    | BoundV uu____45356 -> []
    | FreeV fv -> [fv]
    | App (uu____45391,tms) -> FStar_List.collect freevars tms
    | Quant (uu____45405,uu____45406,uu____45407,uu____45408,t1) ->
        freevars t1
    | Labeled (t1,uu____45429,uu____45430) -> freevars t1
    | LblPos (t1,uu____45434) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let (free_variables : term -> fvs) =
  fun t  ->
    let uu____45457 = FStar_ST.op_Bang t.freevars  in
    match uu____45457 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____45555 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____45555  in
        (FStar_ST.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs);
         fvs)
  
let (qop_to_string : qop -> Prims.string) =
  fun uu___405_45634  ->
    match uu___405_45634 with | Forall  -> "forall" | Exists  -> "exists"
  
let (op_to_string : op -> Prims.string) =
  fun uu___406_45644  ->
    match uu___406_45644 with
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
        let uu____45680 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ zero_extend %s)" uu____45680
    | NatToBv n1 ->
        let uu____45685 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(_ int2bv %s)" uu____45685
    | Var s -> s
  
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___407_45699  ->
    match uu___407_45699 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____45709 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____45709
  
let rec (hash_of_term' : term' -> Prims.string) =
  fun t  ->
    match t with
    | Integer i -> i
    | Real r -> r
    | BoundV i ->
        let uu____45731 = FStar_Util.string_of_int i  in
        Prims.op_Hat "@" uu____45731
    | FreeV x ->
        let uu____45743 = fv_name x  in
        let uu____45745 =
          let uu____45747 =
            let uu____45749 = fv_sort x  in strSort uu____45749  in
          Prims.op_Hat ":" uu____45747  in
        Prims.op_Hat uu____45743 uu____45745
    | App (op,tms) ->
        let uu____45757 =
          let uu____45759 = op_to_string op  in
          let uu____45761 =
            let uu____45763 =
              let uu____45765 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____45765 (FStar_String.concat " ")  in
            Prims.op_Hat uu____45763 ")"  in
          Prims.op_Hat uu____45759 uu____45761  in
        Prims.op_Hat "(" uu____45757
    | Labeled (t1,r1,r2) ->
        let uu____45782 = hash_of_term t1  in
        let uu____45784 =
          let uu____45786 = FStar_Range.string_of_range r2  in
          Prims.op_Hat r1 uu____45786  in
        Prims.op_Hat uu____45782 uu____45784
    | LblPos (t1,r) ->
        let uu____45792 =
          let uu____45794 = hash_of_term t1  in
          Prims.op_Hat uu____45794
            (Prims.op_Hat " :lblpos " (Prims.op_Hat r ")"))
           in
        Prims.op_Hat "(! " uu____45792
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____45822 =
          let uu____45824 =
            let uu____45826 =
              let uu____45828 =
                let uu____45830 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____45830 (FStar_String.concat " ")
                 in
              let uu____45840 =
                let uu____45842 =
                  let uu____45844 = hash_of_term body  in
                  let uu____45846 =
                    let uu____45848 =
                      let uu____45850 = weightToSmt wopt  in
                      let uu____45852 =
                        let uu____45854 =
                          let uu____45856 =
                            let uu____45858 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____45877 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____45877
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____45858
                              (FStar_String.concat "; ")
                             in
                          Prims.op_Hat uu____45856 "))"  in
                        Prims.op_Hat " " uu____45854  in
                      Prims.op_Hat uu____45850 uu____45852  in
                    Prims.op_Hat " " uu____45848  in
                  Prims.op_Hat uu____45844 uu____45846  in
                Prims.op_Hat ")(! " uu____45842  in
              Prims.op_Hat uu____45828 uu____45840  in
            Prims.op_Hat " (" uu____45826  in
          Prims.op_Hat (qop_to_string qop) uu____45824  in
        Prims.op_Hat "(" uu____45822
    | Let (es,body) ->
        let uu____45904 =
          let uu____45906 =
            let uu____45908 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____45908 (FStar_String.concat " ")  in
          let uu____45918 =
            let uu____45920 =
              let uu____45922 = hash_of_term body  in
              Prims.op_Hat uu____45922 ")"  in
            Prims.op_Hat ") " uu____45920  in
          Prims.op_Hat uu____45906 uu____45918  in
        Prims.op_Hat "(let (" uu____45904

and (hash_of_term : term -> Prims.string) = fun tm  -> hash_of_term' tm.tm

let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s  -> (s, (Prims.op_Hat s "_proj_0")) 
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt" 
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool" 
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString" 
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz  ->
    let uu____45983 =
      let uu____45985 = FStar_Util.string_of_int sz  in
      Prims.op_Hat "BoxBitVec" uu____45985  in
    mkBoxFunctions uu____45983
  
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal" 
let (isInjective : Prims.string -> Prims.bool) =
  fun s  ->
    if (FStar_String.length s) >= (Prims.parse_int "3")
    then
      (let uu____46010 =
         FStar_String.substring s (Prims.parse_int "0") (Prims.parse_int "3")
          in
       uu____46010 = "Box") &&
        (let uu____46017 =
           let uu____46019 = FStar_String.list_of_string s  in
           FStar_List.existsML (fun c  -> c = 46) uu____46019  in
         Prims.op_Negation uu____46017)
    else false
  
let (mk : term' -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      let uu____46043 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
      { tm = t; freevars = uu____46043; rng = r }
  
let (mkTrue : FStar_Range.range -> term) = fun r  -> mk (App (TrueOp, [])) r 
let (mkFalse : FStar_Range.range -> term) =
  fun r  -> mk (App (FalseOp, [])) r 
let (mkInteger : Prims.string -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46107 =
        let uu____46108 = FStar_Util.ensure_decimal i  in Integer uu____46108
         in
      mk uu____46107 r
  
let (mkInteger' : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____46123 = FStar_Util.string_of_int i  in
      mkInteger uu____46123 r
  
let (mkReal : Prims.string -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (Real i) r 
let (mkBoundV : Prims.int -> FStar_Range.range -> term) =
  fun i  -> fun r  -> mk (BoundV i) r 
let (mkFreeV : fv -> FStar_Range.range -> term) =
  fun x  -> fun r  -> mk (FreeV x) r 
let (mkApp' : (op * term Prims.list) -> FStar_Range.range -> term) =
  fun f  -> fun r  -> mk (App f) r 
let (mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term) =
  fun uu____46201  ->
    fun r  -> match uu____46201 with | (s,args) -> mk (App ((Var s), args)) r
  
let (mkNot : term -> FStar_Range.range -> term) =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____46231) -> mkFalse r
      | App (FalseOp ,uu____46236) -> mkTrue r
      | uu____46241 -> mkApp' (Not, [t]) r
  
let (mkAnd : (term * term) -> FStar_Range.range -> term) =
  fun uu____46257  ->
    fun r  ->
      match uu____46257 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46265),uu____46266) -> t2
           | (uu____46271,App (TrueOp ,uu____46272)) -> t1
           | (App (FalseOp ,uu____46277),uu____46278) -> mkFalse r
           | (uu____46283,App (FalseOp ,uu____46284)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____46301,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____46310) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____46317 -> mkApp' (And, [t1; t2]) r)
  
let (mkOr : (term * term) -> FStar_Range.range -> term) =
  fun uu____46337  ->
    fun r  ->
      match uu____46337 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____46345),uu____46346) -> mkTrue r
           | (uu____46351,App (TrueOp ,uu____46352)) -> mkTrue r
           | (App (FalseOp ,uu____46357),uu____46358) -> t2
           | (uu____46363,App (FalseOp ,uu____46364)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____46381,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____46390) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____46397 -> mkApp' (Or, [t1; t2]) r)
  
let (mkImp : (term * term) -> FStar_Range.range -> term) =
  fun uu____46417  ->
    fun r  ->
      match uu____46417 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____46425,App (TrueOp ,uu____46426)) -> mkTrue r
           | (App (FalseOp ,uu____46431),uu____46432) -> mkTrue r
           | (App (TrueOp ,uu____46437),uu____46438) -> t2
           | (uu____46443,App (Imp ,t1'::t2'::[])) ->
               let uu____46448 =
                 let uu____46455 =
                   let uu____46458 = mkAnd (t1, t1') r  in [uu____46458; t2']
                    in
                 (Imp, uu____46455)  in
               mkApp' uu____46448 r
           | uu____46461 -> mkApp' (Imp, [t1; t2]) r)
  
let (mk_bin_op : op -> (term * term) -> FStar_Range.range -> term) =
  fun op  ->
    fun uu____46486  ->
      fun r  -> match uu____46486 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
    fun uu____46646  ->
      fun r  ->
        match uu____46646 with
        | (t1,t2) ->
            let uu____46655 =
              let uu____46662 =
                let uu____46665 =
                  let uu____46668 = mkNatToBv sz t2 r  in [uu____46668]  in
                t1 :: uu____46665  in
              (BvShl, uu____46662)  in
            mkApp' uu____46655 r
  
let (mkBvShr : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46690  ->
      fun r  ->
        match uu____46690 with
        | (t1,t2) ->
            let uu____46699 =
              let uu____46706 =
                let uu____46709 =
                  let uu____46712 = mkNatToBv sz t2 r  in [uu____46712]  in
                t1 :: uu____46709  in
              (BvShr, uu____46706)  in
            mkApp' uu____46699 r
  
let (mkBvUdiv : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46734  ->
      fun r  ->
        match uu____46734 with
        | (t1,t2) ->
            let uu____46743 =
              let uu____46750 =
                let uu____46753 =
                  let uu____46756 = mkNatToBv sz t2 r  in [uu____46756]  in
                t1 :: uu____46753  in
              (BvUdiv, uu____46750)  in
            mkApp' uu____46743 r
  
let (mkBvMod : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46778  ->
      fun r  ->
        match uu____46778 with
        | (t1,t2) ->
            let uu____46787 =
              let uu____46794 =
                let uu____46797 =
                  let uu____46800 = mkNatToBv sz t2 r  in [uu____46800]  in
                t1 :: uu____46797  in
              (BvMod, uu____46794)  in
            mkApp' uu____46787 r
  
let (mkBvMul : Prims.int -> (term * term) -> FStar_Range.range -> term) =
  fun sz  ->
    fun uu____46822  ->
      fun r  ->
        match uu____46822 with
        | (t1,t2) ->
            let uu____46831 =
              let uu____46838 =
                let uu____46841 =
                  let uu____46844 = mkNatToBv sz t2 r  in [uu____46844]  in
                t1 :: uu____46841  in
              (BvMul, uu____46838)  in
            mkApp' uu____46831 r
  
let (mkBvUlt : (term * term) -> FStar_Range.range -> term) = mk_bin_op BvUlt 
let (mkIff : (term * term) -> FStar_Range.range -> term) = mk_bin_op Iff 
let (mkEq : (term * term) -> FStar_Range.range -> term) =
  fun uu____46886  ->
    fun r  ->
      match uu____46886 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1,s1::[]),App (Var f2,s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu____46905 -> mk_bin_op Eq (t1, t2) r)
  
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
  fun uu____47070  ->
    fun r  ->
      match uu____47070 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____47081) -> t2
           | App (FalseOp ,uu____47086) -> t3
           | uu____47091 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____47092),App (TrueOp ,uu____47093)) ->
                    mkTrue r
                | (App (TrueOp ,uu____47102),uu____47103) ->
                    let uu____47108 =
                      let uu____47113 = mkNot t1 t1.rng  in (uu____47113, t3)
                       in
                    mkImp uu____47108 r
                | (uu____47114,App (TrueOp ,uu____47115)) -> mkImp (t1, t2) r
                | (uu____47120,uu____47121) -> mkApp' (ITE, [t1; t2; t3]) r))
  
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
      | Integer uu____47177 -> FStar_Pervasives_Native.None
      | Real uu____47179 -> FStar_Pervasives_Native.None
      | BoundV uu____47181 -> FStar_Pervasives_Native.None
      | FreeV uu____47183 -> FStar_Pervasives_Native.None
      | Let (tms,tm) -> aux_l (tm :: tms)
      | App (head1,terms) ->
          let head_ok =
            match head1 with
            | Var uu____47207 -> true
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
            | BvUext uu____47240 -> false
            | NatToBv uu____47243 -> false
            | BvToNat  -> false
            | ITE  -> false  in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2,uu____47254,uu____47255) -> aux t2
      | Quant uu____47258 -> FStar_Pervasives_Native.Some t1
      | LblPos uu____47278 -> FStar_Pervasives_Native.Some t1
    
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu____47293 = aux t1  in
          (match uu____47293 with
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
        let uu____47331 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____47331
    | FreeV fv ->
        let uu____47343 = fv_name fv  in
        FStar_Util.format1 "(FreeV %s)" uu____47343
    | App (op,l) ->
        let uu____47352 = op_to_string op  in
        let uu____47354 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" uu____47352 uu____47354
    | Labeled (t1,r1,r2) ->
        let uu____47362 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____47362
    | LblPos (t1,s) ->
        let uu____47369 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____47369
    | Quant (qop,l,uu____47374,uu____47375,t1) ->
        let uu____47395 = print_smt_term_list_list l  in
        let uu____47397 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____47395
          uu____47397
    | Let (es,body) ->
        let uu____47406 = print_smt_term_list es  in
        let uu____47408 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____47406 uu____47408

and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l  ->
    let uu____47415 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____47415 (FStar_String.concat " ")

and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____47442 =
             let uu____47444 =
               let uu____47446 = print_smt_term_list l1  in
               Prims.op_Hat uu____47446 " ] "  in
             Prims.op_Hat "; [ " uu____47444  in
           Prims.op_Hat s uu____47442) "" l

let (mkQuant :
  FStar_Range.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r  ->
    fun check_pats  ->
      fun uu____47486  ->
        match uu____47486 with
        | (qop,pats,wopt,vars,body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu____47555 =
                   FStar_Util.find_map pats1
                     (fun x  -> FStar_Util.find_map x check_pattern_ok)
                    in
                 match uu____47555 with
                 | FStar_Pervasives_Native.None  -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu____47570 =
                         let uu____47576 =
                           let uu____47578 = print_smt_term p  in
                           FStar_Util.format1
                             "Pattern (%s) contains illegal symbols; dropping it"
                             uu____47578
                            in
                         (FStar_Errors.Warning_SMTPatternIllFormed,
                           uu____47576)
                          in
                       FStar_Errors.log_issue r uu____47570);
                      []))
               in
            if (FStar_List.length vars) = (Prims.parse_int "0")
            then body
            else
              (match body.tm with
               | App (TrueOp ,uu____47589) -> body
               | uu____47594 ->
                   let uu____47595 =
                     let uu____47596 =
                       let uu____47616 = all_pats_ok pats  in
                       (qop, uu____47616, wopt, vars, body)  in
                     Quant uu____47596  in
                   mk uu____47595 r)
  
let (mkLet : (term Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____47645  ->
    fun r  ->
      match uu____47645 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let (abstr : fv Prims.list -> term -> term) =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of1 fv =
        let uu____47691 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____47691 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1")))
         in
      let rec aux ix t1 =
        let uu____47718 = FStar_ST.op_Bang t1.freevars  in
        match uu____47718 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____47792 ->
            (match t1.tm with
             | Integer uu____47805 -> t1
             | Real uu____47807 -> t1
             | BoundV uu____47809 -> t1
             | FreeV x ->
                 let uu____47820 = index_of1 x  in
                 (match uu____47820 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____47834 =
                   let uu____47841 = FStar_List.map (aux ix) tms  in
                   (op, uu____47841)  in
                 mkApp' uu____47834 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____47851 =
                   let uu____47852 =
                     let uu____47860 = aux ix t2  in (uu____47860, r1, r2)
                      in
                   Labeled uu____47852  in
                 mk uu____47851 t2.rng
             | LblPos (t2,r) ->
                 let uu____47866 =
                   let uu____47867 =
                     let uu____47873 = aux ix t2  in (uu____47873, r)  in
                   LblPos uu____47867  in
                 mk uu____47866 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____47899 =
                   let uu____47919 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____47936 = aux (ix + n1) body  in
                   (qop, uu____47919, wopt, vars, uu____47936)  in
                 mkQuant t1.rng false uu____47899
             | Let (es,body) ->
                 let uu____47953 =
                   FStar_List.fold_left
                     (fun uu____47973  ->
                        fun e  ->
                          match uu____47973 with
                          | (ix1,l) ->
                              let uu____47997 =
                                let uu____48000 = aux ix1 e  in uu____48000
                                  :: l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____47997))
                     (ix, []) es
                    in
                 (match uu____47953 with
                  | (ix1,es_rev) ->
                      let uu____48016 =
                        let uu____48023 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____48023)  in
                      mkLet uu____48016 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let (inst : term Prims.list -> term -> term) =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____48059 -> t1
        | Real uu____48061 -> t1
        | FreeV uu____48063 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____48084 =
              let uu____48091 = FStar_List.map (aux shift) tms2  in
              (op, uu____48091)  in
            mkApp' uu____48084 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____48101 =
              let uu____48102 =
                let uu____48110 = aux shift t2  in (uu____48110, r1, r2)  in
              Labeled uu____48102  in
            mk uu____48101 t2.rng
        | LblPos (t2,r) ->
            let uu____48116 =
              let uu____48117 =
                let uu____48123 = aux shift t2  in (uu____48123, r)  in
              LblPos uu____48117  in
            mk uu____48116 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____48151 =
              let uu____48171 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____48188 = aux shift1 body  in
              (qop, uu____48171, wopt, vars, uu____48188)  in
            mkQuant t1.rng false uu____48151
        | Let (es,body) ->
            let uu____48205 =
              FStar_List.fold_left
                (fun uu____48225  ->
                   fun e  ->
                     match uu____48225 with
                     | (ix,es1) ->
                         let uu____48249 =
                           let uu____48252 = aux shift e  in uu____48252 ::
                             es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____48249))
                (shift, []) es
               in
            (match uu____48205 with
             | (shift1,es_rev) ->
                 let uu____48268 =
                   let uu____48275 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____48275)  in
                 mkLet uu____48268 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let (subst : term -> fv -> term -> term) =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____48295 = abstr [fv] t  in inst [s] uu____48295
  
let (mkQuant' :
  FStar_Range.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48325  ->
      match uu____48325 with
      | (qop,pats,wopt,vars,body) ->
          let uu____48368 =
            let uu____48388 =
              FStar_All.pipe_right pats
                (FStar_List.map (FStar_List.map (abstr vars)))
               in
            let uu____48405 = FStar_List.map fv_sort vars  in
            let uu____48408 = abstr vars body  in
            (qop, uu____48388, wopt, uu____48405, uu____48408)  in
          mkQuant r true uu____48368
  
let (mkForall :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48439  ->
      match uu____48439 with
      | (pats,vars,body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkForall'' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r  ->
    fun uu____48498  ->
      match uu____48498 with
      | (pats,wopt,sorts,body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
  
let (mkForall' :
  FStar_Range.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r  ->
    fun uu____48573  ->
      match uu____48573 with
      | (pats,wopt,vars,body) -> mkQuant' r (Forall, pats, wopt, vars, body)
  
let (mkExists :
  FStar_Range.range -> (pat Prims.list Prims.list * fvs * term) -> term) =
  fun r  ->
    fun uu____48636  ->
      match uu____48636 with
      | (pats,vars,body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
  
let (mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term) =
  fun uu____48687  ->
    fun r  ->
      match uu____48687 with
      | (bindings,body) ->
          let uu____48713 = FStar_List.split bindings  in
          (match uu____48713 with
           | (vars,es) ->
               let uu____48732 =
                 let uu____48739 = abstr vars body  in (es, uu____48739)  in
               mkLet uu____48732 r)
  
let (norng : FStar_Range.range) = FStar_Range.dummyRange 
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu____48761  ->
    match uu____48761 with
    | (nm,vars,s,tm,c) ->
        let uu____48786 =
          let uu____48800 = FStar_List.map fv_sort vars  in
          let uu____48803 = abstr vars tm  in
          (nm, uu____48800, s, uu____48803, c)  in
        DefineFun uu____48786
  
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort  ->
    let uu____48814 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____48814
  
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu____48832  ->
    fun id1  ->
      match uu____48832 with
      | (tok_name,sort) ->
          let a_name = Prims.op_Hat "fresh_token_" tok_name  in
          let a =
            let uu____48848 =
              let uu____48849 =
                let uu____48854 = mkInteger' id1 norng  in
                let uu____48855 =
                  let uu____48856 =
                    let uu____48864 = constr_id_of_sort sort  in
                    let uu____48866 =
                      let uu____48869 = mkApp (tok_name, []) norng  in
                      [uu____48869]  in
                    (uu____48864, uu____48866)  in
                  mkApp uu____48856 norng  in
                (uu____48854, uu____48855)  in
              mkEq uu____48849 norng  in
            let uu____48876 = escape a_name  in
            {
              assumption_term = uu____48848;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu____48876;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (fresh_constructor :
  FStar_Range.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng  ->
    fun uu____48902  ->
      match uu____48902 with
      | (name,arg_sorts,sort,id1) ->
          let id2 = FStar_Util.string_of_int id1  in
          let bvars =
            FStar_All.pipe_right arg_sorts
              (FStar_List.mapi
                 (fun i  ->
                    fun s  ->
                      let uu____48942 =
                        let uu____48943 =
                          let uu____48949 =
                            let uu____48951 = FStar_Util.string_of_int i  in
                            Prims.op_Hat "x_" uu____48951  in
                          (uu____48949, s)  in
                        mk_fv uu____48943  in
                      mkFreeV uu____48942 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let cid_app =
            let uu____48979 =
              let uu____48987 = constr_id_of_sort sort  in
              (uu____48987, [capp])  in
            mkApp uu____48979 norng  in
          let a_name = Prims.op_Hat "constructor_distinct_" name  in
          let a =
            let uu____48996 =
              let uu____48997 =
                let uu____49008 =
                  let uu____49009 =
                    let uu____49014 = mkInteger id2 norng  in
                    (uu____49014, cid_app)  in
                  mkEq uu____49009 norng  in
                ([[capp]], bvar_names, uu____49008)  in
              mkForall rng uu____48997  in
            let uu____49023 = escape a_name  in
            {
              assumption_term = uu____48996;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu____49023;
              assumption_fact_ids = []
            }  in
          Assume a
  
let (injective_constructor :
  FStar_Range.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng  ->
    fun uu____49048  ->
      match uu____49048 with
      | (name,fields,sort) ->
          let n_bvars = FStar_List.length fields  in
          let bvar_name i =
            let uu____49081 = FStar_Util.string_of_int i  in
            Prims.op_Hat "x_" uu____49081  in
          let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
          let bvar i s =
            let uu____49110 =
              let uu____49111 =
                let uu____49117 = bvar_name i  in (uu____49117, s)  in
              mk_fv uu____49111  in
            FStar_All.pipe_left mkFreeV uu____49110  in
          let bvars =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49153  ->
                      match uu____49153 with
                      | (uu____49163,s,uu____49165) ->
                          let uu____49170 = bvar i s  in uu____49170 norng))
             in
          let bvar_names = FStar_List.map fv_of_term bvars  in
          let capp = mkApp (name, bvars) norng  in
          let uu____49198 =
            FStar_All.pipe_right fields
              (FStar_List.mapi
                 (fun i  ->
                    fun uu____49236  ->
                      match uu____49236 with
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
                              let uu____49269 =
                                let uu____49270 =
                                  let uu____49281 =
                                    let uu____49282 =
                                      let uu____49287 =
                                        let uu____49288 = bvar i s  in
                                        uu____49288 norng  in
                                      (cproj_app, uu____49287)  in
                                    mkEq uu____49282 norng  in
                                  ([[capp]], bvar_names, uu____49281)  in
                                mkForall rng uu____49270  in
                              let uu____49301 =
                                escape
                                  (Prims.op_Hat "projection_inverse_" name1)
                                 in
                              {
                                assumption_term = uu____49269;
                                assumption_caption =
                                  (FStar_Pervasives_Native.Some
                                     "Projection inverse");
                                assumption_name = uu____49301;
                                assumption_fact_ids = []
                              }  in
                            [proj_name; Assume a]
                          else [proj_name]))
             in
          FStar_All.pipe_right uu____49198 FStar_List.flatten
  
let (constructor_to_decl :
  FStar_Range.range -> constructor_t -> decl Prims.list) =
  fun rng  ->
    fun uu____49326  ->
      match uu____49326 with
      | (name,fields,sort,id1,injective) ->
          let injective1 = injective || true  in
          let field_sorts =
            FStar_All.pipe_right fields
              (FStar_List.map
                 (fun uu____49374  ->
                    match uu____49374 with
                    | (uu____49383,sort1,uu____49385) -> sort1))
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
              let uu____49410 =
                let uu____49415 =
                  let uu____49416 =
                    let uu____49424 = constr_id_of_sort sort  in
                    (uu____49424, [xx])  in
                  mkApp uu____49416 norng  in
                let uu____49429 =
                  let uu____49430 = FStar_Util.string_of_int id1  in
                  mkInteger uu____49430 norng  in
                (uu____49415, uu____49429)  in
              mkEq uu____49410 norng  in
            let uu____49432 =
              let uu____49451 =
                FStar_All.pipe_right fields
                  (FStar_List.mapi
                     (fun i  ->
                        fun uu____49515  ->
                          match uu____49515 with
                          | (proj,s,projectible) ->
                              if projectible
                              then
                                let uu____49545 = mkApp (proj, [xx]) norng
                                   in
                                (uu____49545, [])
                              else
                                (let fi =
                                   let uu____49554 =
                                     let uu____49560 =
                                       let uu____49562 =
                                         FStar_Util.string_of_int i  in
                                       Prims.op_Hat "f_" uu____49562  in
                                     (uu____49560, s)  in
                                   mk_fv uu____49554  in
                                 let uu____49566 = mkFreeV fi norng  in
                                 (uu____49566, [fi]))))
                 in
              FStar_All.pipe_right uu____49451 FStar_List.split  in
            match uu____49432 with
            | (proj_terms,ex_vars) ->
                let ex_vars1 = FStar_List.flatten ex_vars  in
                let disc_inv_body =
                  let uu____49663 =
                    let uu____49668 = mkApp (name, proj_terms) norng  in
                    (xx, uu____49668)  in
                  mkEq uu____49663 norng  in
                let disc_inv_body1 =
                  match ex_vars1 with
                  | [] -> disc_inv_body
                  | uu____49681 ->
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
          let uu____49716 =
            let uu____49719 =
              let uu____49720 =
                FStar_Util.format1 "<start constructor %s>" name  in
              Caption uu____49720  in
            uu____49719 :: cdecl :: cid :: projs  in
          let uu____49723 =
            let uu____49726 =
              let uu____49729 =
                let uu____49730 =
                  FStar_Util.format1 "</end constructor %s>" name  in
                Caption uu____49730  in
              [uu____49729]  in
            FStar_List.append [disc] uu____49726  in
          FStar_List.append uu____49716 uu____49723
  
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
          let uu____49782 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____49831  ->
                    fun s  ->
                      match uu____49831 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____49876 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.op_Hat p prefix1
                             in
                          let nm =
                            let uu____49887 = FStar_Util.string_of_int n1  in
                            Prims.op_Hat prefix2 uu____49887  in
                          let names2 =
                            let uu____49892 = mk_fv (nm, s)  in uu____49892
                              :: names1
                             in
                          let b =
                            let uu____49896 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____49896  in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____49782 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
  
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts  ->
    let uu____49967 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts
       in
    match uu____49967 with
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
              (let uu____50076 = FStar_Util.string_of_int n1  in
               FStar_Util.format2 "%s.%s" enclosing_name uu____50076)
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
                               "Prims.guard_free",{ tm = BoundV uu____50122;
                                                    freevars = uu____50123;
                                                    rng = uu____50124;_}::[])
                              -> tm
                          | App (Var "Prims.guard_free",p::[]) -> p
                          | uu____50145 -> tm))))
           in
        let rec aux' depth n1 names1 t1 =
          let aux1 = aux (depth + (Prims.parse_int "1"))  in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | BoundV i ->
              let uu____50223 = FStar_List.nth names1 i  in
              FStar_All.pipe_right uu____50223 fv_name
          | FreeV x when fv_force x ->
              let uu____50234 =
                let uu____50236 = fv_name x  in
                Prims.op_Hat uu____50236 " Dummy_value)"  in
              Prims.op_Hat "(" uu____50234
          | FreeV x -> fv_name x
          | App (op,[]) -> op_to_string op
          | App (op,tms) ->
              let uu____50258 = op_to_string op  in
              let uu____50260 =
                let uu____50262 = FStar_List.map (aux1 n1 names1) tms  in
                FStar_All.pipe_right uu____50262 (FStar_String.concat "\n")
                 in
              FStar_Util.format2 "(%s %s)" uu____50258 uu____50260
          | Labeled (t2,uu____50274,uu____50275) -> aux1 n1 names1 t2
          | LblPos (t2,s) ->
              let uu____50282 = aux1 n1 names1 t2  in
              FStar_Util.format2 "(! %s :lblpos %s)" uu____50282 s
          | Quant (qop,pats,wopt,sorts,body) ->
              let qid = next_qid ()  in
              let uu____50310 =
                name_binders_inner FStar_Pervasives_Native.None names1 n1
                  sorts
                 in
              (match uu____50310 with
               | (names2,binders,n2) ->
                   let binders1 =
                     FStar_All.pipe_right binders (FStar_String.concat " ")
                      in
                   let pats1 = remove_guard_free pats  in
                   let pats_str =
                     match pats1 with
                     | []::[] -> ";;no pats"
                     | [] -> ";;no pats"
                     | uu____50363 ->
                         let uu____50368 =
                           FStar_All.pipe_right pats1
                             (FStar_List.map
                                (fun pats2  ->
                                   let uu____50387 =
                                     let uu____50389 =
                                       FStar_List.map
                                         (fun p  ->
                                            let uu____50397 =
                                              aux1 n2 names2 p  in
                                            FStar_Util.format1 "%s"
                                              uu____50397) pats2
                                        in
                                     FStar_String.concat " " uu____50389  in
                                   FStar_Util.format1 "\n:pattern (%s)"
                                     uu____50387))
                            in
                         FStar_All.pipe_right uu____50368
                           (FStar_String.concat "\n")
                      in
                   let uu____50407 =
                     let uu____50411 =
                       let uu____50415 =
                         let uu____50419 = aux1 n2 names2 body  in
                         let uu____50421 =
                           let uu____50425 = weightToSmt wopt  in
                           [uu____50425; pats_str; qid]  in
                         uu____50419 :: uu____50421  in
                       binders1 :: uu____50415  in
                     (qop_to_string qop) :: uu____50411  in
                   FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                     uu____50407)
          | Let (es,body) ->
              let uu____50441 =
                FStar_List.fold_left
                  (fun uu____50474  ->
                     fun e  ->
                       match uu____50474 with
                       | (names0,binders,n0) ->
                           let nm =
                             let uu____50517 = FStar_Util.string_of_int n0
                                in
                             Prims.op_Hat "@lb" uu____50517  in
                           let names01 =
                             let uu____50523 = mk_fv (nm, Term_sort)  in
                             uu____50523 :: names0  in
                           let b =
                             let uu____50527 = aux1 n1 names1 e  in
                             FStar_Util.format2 "(%s %s)" nm uu____50527  in
                           (names01, (b :: binders),
                             (n0 + (Prims.parse_int "1")))) (names1, [], n1)
                  es
                 in
              (match uu____50441 with
               | (names2,binders,n2) ->
                   let uu____50561 = aux1 n2 names2 body  in
                   FStar_Util.format2 "(let (%s)\n%s)"
                     (FStar_String.concat " " binders) uu____50561)
        
        and aux depth n1 names1 t1 =
          let s = aux' depth n1 names1 t1  in
          if print_ranges && (t1.rng <> norng)
          then
            let uu____50577 = FStar_Range.string_of_range t1.rng  in
            let uu____50579 = FStar_Range.string_of_use_range t1.rng  in
            FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____50577
              uu____50579 s
          else s
         in aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
  
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions  ->
    fun uu___408_50601  ->
      match uu___408_50601 with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu____50612 =
              FStar_All.pipe_right (FStar_String.split [10] c)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____50612 (FStar_String.concat " ")  in
          Prims.op_Hat ";;;;;;;;;;;;;;;;" (Prims.op_Hat c1 "\n")
      | uu____50634 -> ""
  
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions  ->
    fun z3options  ->
      fun decl  ->
        match decl with
        | DefPrelude  -> mkPrelude z3options
        | Module (s,decls) ->
            let res =
              let uu____50709 =
                FStar_List.map (declToSmt' print_captions z3options) decls
                 in
              FStar_All.pipe_right uu____50709 (FStar_String.concat "\n")  in
            let uu____50719 = FStar_Options.keep_query_captions ()  in
            if uu____50719
            then
              let uu____50723 =
                FStar_Util.string_of_int (FStar_List.length decls)  in
              let uu____50725 =
                FStar_Util.string_of_int (FStar_String.length res)  in
              FStar_Util.format5
                "\n;;; Start module %s\n%s\n;;; End module %s (%s decls; total size %s)"
                s res s uu____50723 uu____50725
            else res
        | Caption c ->
            if print_captions
            then
              let uu____50734 =
                let uu____50736 =
                  FStar_All.pipe_right (FStar_Util.splitlines c)
                    (FStar_List.map
                       (fun s  -> Prims.op_Hat "; " (Prims.op_Hat s "\n")))
                   in
                FStar_All.pipe_right uu____50736 (FStar_String.concat "")  in
              Prims.op_Hat "\n" uu____50734
            else ""
        | DeclFun (f,argsorts,retsort,c) ->
            let l = FStar_List.map strSort argsorts  in
            let uu____50777 = caption_to_string print_captions c  in
            let uu____50779 = strSort retsort  in
            FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____50777 f
              (FStar_String.concat " " l) uu____50779
        | DefineFun (f,arg_sorts,retsort,body,c) ->
            let uu____50794 = name_macro_binders arg_sorts  in
            (match uu____50794 with
             | (names1,binders) ->
                 let body1 =
                   let uu____50818 =
                     FStar_List.map (fun x  -> mkFreeV x norng) names1  in
                   inst uu____50818 body  in
                 let uu____50823 = caption_to_string print_captions c  in
                 let uu____50825 = strSort retsort  in
                 let uu____50827 =
                   let uu____50829 = escape f  in
                   termToSmt print_captions uu____50829 body1  in
                 FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)"
                   uu____50823 f (FStar_String.concat " " binders)
                   uu____50825 uu____50827)
        | Assume a ->
            let fact_ids_to_string ids =
              FStar_All.pipe_right ids
                (FStar_List.map
                   (fun uu___409_50856  ->
                      match uu___409_50856 with
                      | Name n1 ->
                          let uu____50859 = FStar_Ident.text_of_lid n1  in
                          Prims.op_Hat "Name " uu____50859
                      | Namespace ns ->
                          let uu____50863 = FStar_Ident.text_of_lid ns  in
                          Prims.op_Hat "Namespace " uu____50863
                      | Tag t -> Prims.op_Hat "Tag " t))
               in
            let fids =
              if print_captions
              then
                let uu____50873 =
                  let uu____50875 = fact_ids_to_string a.assumption_fact_ids
                     in
                  FStar_String.concat "; " uu____50875  in
                FStar_Util.format1 ";;; Fact-ids: %s\n" uu____50873
              else ""  in
            let n1 = a.assumption_name  in
            let uu____50886 =
              caption_to_string print_captions a.assumption_caption  in
            let uu____50888 = termToSmt print_captions n1 a.assumption_term
               in
            FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____50886
              fids uu____50888 n1
        | Eval t ->
            let uu____50892 = termToSmt print_captions "eval" t  in
            FStar_Util.format1 "(eval %s)" uu____50892
        | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu____50899 -> ""
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
      let uu____50920 = FStar_Options.keep_query_captions ()  in
      declToSmt' uu____50920 z3options decl

and (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options  -> fun decl  -> declToSmt' false z3options decl

and (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options  ->
    fun decls  ->
      let uu____50931 = FStar_List.map (declToSmt z3options) decls  in
      FStar_All.pipe_right uu____50931 (FStar_String.concat "\n")

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
      let uu____51066 =
        let uu____51070 =
          FStar_All.pipe_right constrs
            (FStar_List.collect (constructor_to_decl norng))
           in
        FStar_All.pipe_right uu____51070
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____51066 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t (LexCons t1 x1 x2) (LexCons t2 y1 y2)))\n(or (Valid (Prims.precedes t1 t2 x1 y1))\n(and (= x1 y1)\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t x2 y2)))))))\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n"
       in
    Prims.op_Hat basic (Prims.op_Hat bcons lex_ordering)

let (mkBvConstructor : Prims.int -> decl Prims.list) =
  fun sz  ->
    let uu____51101 =
      let uu____51102 =
        let uu____51104 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51104  in
      let uu____51113 =
        let uu____51116 =
          let uu____51117 =
            let uu____51119 = boxBitVecFun sz  in
            FStar_Pervasives_Native.snd uu____51119  in
          (uu____51117, (BitVec_sort sz), true)  in
        [uu____51116]  in
      (uu____51102, uu____51113, Term_sort, ((Prims.parse_int "12") + sz),
        true)
       in
    FStar_All.pipe_right uu____51101 (constructor_to_decl norng)
  
let (__range_c : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (mk_Range_const : unit -> term) =
  fun uu____51151  ->
    let i = FStar_ST.op_Bang __range_c  in
    (let uu____51176 =
       let uu____51178 = FStar_ST.op_Bang __range_c  in
       uu____51178 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals __range_c uu____51176);
    (let uu____51223 =
       let uu____51231 =
         let uu____51234 = mkInteger' i norng  in [uu____51234]  in
       ("Range_const", uu____51231)  in
     mkApp uu____51223 norng)
  
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng 
let (mk_Term_app : term -> term -> FStar_Range.range -> term) =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let (mk_Term_uvar : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____51277 =
        let uu____51285 =
          let uu____51288 = mkInteger' i norng  in [uu____51288]  in
        ("Tm_uvar", uu____51285)  in
      mkApp uu____51277 r
  
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng 
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond  ->
    fun u  ->
      fun v1  ->
        fun t  ->
          match t.tm with
          | App (Var v',t1::[]) when (v1 = v') && cond -> t1
          | uu____51331 -> mkApp (u, [t]) t.rng
  
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u  ->
    fun v1  ->
      fun t  ->
        let uu____51355 = FStar_Options.smtencoding_elim_box ()  in
        elim_box uu____51355 u v1 t
  
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
      let uu____51450 =
        let uu____51452 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51452  in
      let uu____51461 =
        let uu____51463 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51463  in
      elim_box true uu____51450 uu____51461 t
  
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz  ->
    fun t  ->
      let uu____51486 =
        let uu____51488 = boxBitVecFun sz  in
        FStar_Pervasives_Native.snd uu____51488  in
      let uu____51497 =
        let uu____51499 = boxBitVecFun sz  in
        FStar_Pervasives_Native.fst uu____51499  in
      elim_box true uu____51486 uu____51497 t
  
let (boxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu____51523 -> FStar_Exn.raise FStar_Util.Impos
  
let (unboxTerm : sort -> term -> term) =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu____51538 -> FStar_Exn.raise FStar_Util.Impos
  
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t  ->
    match t.tm with
    | App (Var s,t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n1 ->
             let uu____51564 = FStar_Util.int_of_string n1  in
             FStar_Pervasives_Native.Some uu____51564
         | uu____51567 -> FStar_Pervasives_Native.None)
    | uu____51569 -> FStar_Pervasives_Native.None
  
let (mk_PreType : term -> term) = fun t  -> mkApp ("PreType", [t]) t.rng 
let (mk_Valid : term -> term) =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____51587::t1::t2::[]);
                       freevars = uu____51590; rng = uu____51591;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____51610::t1::t2::[]);
                       freevars = uu____51613; rng = uu____51614;_}::[])
        -> let uu____51633 = mkEq (t1, t2) norng  in mkNot uu____51633 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____51636; rng = uu____51637;_}::[])
        ->
        let uu____51656 =
          let uu____51661 = unboxInt t1  in
          let uu____51662 = unboxInt t2  in (uu____51661, uu____51662)  in
        mkLTE uu____51656 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____51665; rng = uu____51666;_}::[])
        ->
        let uu____51685 =
          let uu____51690 = unboxInt t1  in
          let uu____51691 = unboxInt t2  in (uu____51690, uu____51691)  in
        mkLT uu____51685 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____51694; rng = uu____51695;_}::[])
        ->
        let uu____51714 =
          let uu____51719 = unboxInt t1  in
          let uu____51720 = unboxInt t2  in (uu____51719, uu____51720)  in
        mkGTE uu____51714 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____51723; rng = uu____51724;_}::[])
        ->
        let uu____51743 =
          let uu____51748 = unboxInt t1  in
          let uu____51749 = unboxInt t2  in (uu____51748, uu____51749)  in
        mkGT uu____51743 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____51752; rng = uu____51753;_}::[])
        ->
        let uu____51772 =
          let uu____51777 = unboxBool t1  in
          let uu____51778 = unboxBool t2  in (uu____51777, uu____51778)  in
        mkAnd uu____51772 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____51781; rng = uu____51782;_}::[])
        ->
        let uu____51801 =
          let uu____51806 = unboxBool t1  in
          let uu____51807 = unboxBool t2  in (uu____51806, uu____51807)  in
        mkOr uu____51801 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____51809; rng = uu____51810;_}::[])
        -> let uu____51829 = unboxBool t1  in mkNot uu____51829 t1.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "FStar.BV.bvult",t0::t1::t2::[]);
                       freevars = uu____51833; rng = uu____51834;_}::[])
        when
        let uu____51853 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51853 ->
        let sz =
          let uu____51860 = getBoxedInteger t0  in
          match uu____51860 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51868 -> failwith "impossible"  in
        let uu____51874 =
          let uu____51879 = unboxBitVec sz t1  in
          let uu____51880 = unboxBitVec sz t2  in (uu____51879, uu____51880)
           in
        mkBvUlt uu____51874 t.rng
    | App
        (Var
         "Prims.equals",uu____51881::{
                                       tm = App
                                         (Var
                                          "FStar.BV.bvult",t0::t1::t2::[]);
                                       freevars = uu____51885;
                                       rng = uu____51886;_}::uu____51887::[])
        when
        let uu____51906 = getBoxedInteger t0  in
        FStar_Util.is_some uu____51906 ->
        let sz =
          let uu____51913 = getBoxedInteger t0  in
          match uu____51913 with
          | FStar_Pervasives_Native.Some sz -> sz
          | uu____51921 -> failwith "impossible"  in
        let uu____51927 =
          let uu____51932 = unboxBitVec sz t1  in
          let uu____51933 = unboxBitVec sz t2  in (uu____51932, uu____51933)
           in
        mkBvUlt uu____51927 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___1789_51938 = unboxBool t1  in
        {
          tm = (uu___1789_51938.tm);
          freevars = (uu___1789_51938.freevars);
          rng = (t.rng)
        }
    | uu____51939 -> mkApp ("Valid", [t]) t.rng
  
let (mk_HasType : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let (mk_HasTypeZ : term -> term -> term) =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let (mk_IsTyped : term -> term) = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____52000 = FStar_Options.unthrottle_inductives ()  in
        if uu____52000
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
    let uu____52133 =
      let uu____52134 = mkApp ("__uu__PartialApp", []) t.rng  in
      mk_ApplyTT uu____52134 t t.rng  in
    FStar_All.pipe_right uu____52133 mk_Valid
  
let (mk_String_const : Prims.int -> FStar_Range.range -> term) =
  fun i  ->
    fun r  ->
      let uu____52152 =
        let uu____52160 =
          let uu____52163 = mkInteger' i norng  in [uu____52163]  in
        ("FString_const", uu____52160)  in
      mkApp uu____52152 r
  
let (mk_Precedes : term -> term -> term -> term -> FStar_Range.range -> term)
  =
  fun x1  ->
    fun x2  ->
      fun x3  ->
        fun x4  ->
          fun r  ->
            let uu____52194 = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r
               in
            FStar_All.pipe_right uu____52194 mk_Valid
  
let (mk_LexCons : term -> term -> term -> FStar_Range.range -> term) =
  fun x1  ->
    fun x2  -> fun x3  -> fun r  -> mkApp ("LexCons", [x1; x2; x3]) r
  
let rec (n_fuel : Prims.int -> term) =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____52241 =
         let uu____52249 =
           let uu____52252 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____52252]  in
         ("SFuel", uu____52249)  in
       mkApp uu____52241 norng)
  
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
            let uu____52300 = mkAnd (p11, p21) r  in
            FStar_Pervasives_Native.Some uu____52300
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
      let uu____52363 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____52363
  
let (mk_or_l : term Prims.list -> FStar_Range.range -> term) =
  fun l  ->
    fun r  ->
      let uu____52383 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____52383
  
let (mk_haseq : term -> term) =
  fun t  ->
    let uu____52394 = mkApp ("Prims.hasEq", [t]) t.rng  in
    mk_Valid uu____52394
  
let (dummy_sort : sort) = Sort "Dummy_sort" 