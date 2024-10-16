open Prims
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
  fun projectee -> match projectee with | Bool_sort -> true | uu___ -> false
let (uu___is_Int_sort : sort -> Prims.bool) =
  fun projectee -> match projectee with | Int_sort -> true | uu___ -> false
let (uu___is_String_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | String_sort -> true | uu___ -> false
let (uu___is_Term_sort : sort -> Prims.bool) =
  fun projectee -> match projectee with | Term_sort -> true | uu___ -> false
let (uu___is_Fuel_sort : sort -> Prims.bool) =
  fun projectee -> match projectee with | Fuel_sort -> true | uu___ -> false
let (uu___is_BitVec_sort : sort -> Prims.bool) =
  fun projectee ->
    match projectee with | BitVec_sort _0 -> true | uu___ -> false
let (__proj__BitVec_sort__item___0 : sort -> Prims.int) =
  fun projectee -> match projectee with | BitVec_sort _0 -> _0
let (uu___is_Array : sort -> Prims.bool) =
  fun projectee -> match projectee with | Array _0 -> true | uu___ -> false
let (__proj__Array__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Array _0 -> _0
let (uu___is_Arrow : sort -> Prims.bool) =
  fun projectee -> match projectee with | Arrow _0 -> true | uu___ -> false
let (__proj__Arrow__item___0 : sort -> (sort * sort)) =
  fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Sort : sort -> Prims.bool) =
  fun projectee -> match projectee with | Sort _0 -> true | uu___ -> false
let (__proj__Sort__item___0 : sort -> Prims.string) =
  fun projectee -> match projectee with | Sort _0 -> _0
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
  fun projectee -> match projectee with | TrueOp -> true | uu___ -> false
let (uu___is_FalseOp : op -> Prims.bool) =
  fun projectee -> match projectee with | FalseOp -> true | uu___ -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu___ -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu___ -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu___ -> false
let (uu___is_Imp : op -> Prims.bool) =
  fun projectee -> match projectee with | Imp -> true | uu___ -> false
let (uu___is_Iff : op -> Prims.bool) =
  fun projectee -> match projectee with | Iff -> true | uu___ -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_LT : op -> Prims.bool) =
  fun projectee -> match projectee with | LT -> true | uu___ -> false
let (uu___is_LTE : op -> Prims.bool) =
  fun projectee -> match projectee with | LTE -> true | uu___ -> false
let (uu___is_GT : op -> Prims.bool) =
  fun projectee -> match projectee with | GT -> true | uu___ -> false
let (uu___is_GTE : op -> Prims.bool) =
  fun projectee -> match projectee with | GTE -> true | uu___ -> false
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu___ -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu___ -> false
let (uu___is_RealDiv : op -> Prims.bool) =
  fun projectee -> match projectee with | RealDiv -> true | uu___ -> false
let (uu___is_Mul : op -> Prims.bool) =
  fun projectee -> match projectee with | Mul -> true | uu___ -> false
let (uu___is_Minus : op -> Prims.bool) =
  fun projectee -> match projectee with | Minus -> true | uu___ -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu___ -> false
let (uu___is_BvAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAnd -> true | uu___ -> false
let (uu___is_BvXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BvXor -> true | uu___ -> false
let (uu___is_BvOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvOr -> true | uu___ -> false
let (uu___is_BvAdd : op -> Prims.bool) =
  fun projectee -> match projectee with | BvAdd -> true | uu___ -> false
let (uu___is_BvSub : op -> Prims.bool) =
  fun projectee -> match projectee with | BvSub -> true | uu___ -> false
let (uu___is_BvShl : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShl -> true | uu___ -> false
let (uu___is_BvShr : op -> Prims.bool) =
  fun projectee -> match projectee with | BvShr -> true | uu___ -> false
let (uu___is_BvUdiv : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUdiv -> true | uu___ -> false
let (uu___is_BvMod : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMod -> true | uu___ -> false
let (uu___is_BvMul : op -> Prims.bool) =
  fun projectee -> match projectee with | BvMul -> true | uu___ -> false
let (uu___is_BvUlt : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUlt -> true | uu___ -> false
let (uu___is_BvUext : op -> Prims.bool) =
  fun projectee -> match projectee with | BvUext _0 -> true | uu___ -> false
let (__proj__BvUext__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | BvUext _0 -> _0
let (uu___is_NatToBv : op -> Prims.bool) =
  fun projectee -> match projectee with | NatToBv _0 -> true | uu___ -> false
let (__proj__NatToBv__item___0 : op -> Prims.int) =
  fun projectee -> match projectee with | NatToBv _0 -> _0
let (uu___is_BvToNat : op -> Prims.bool) =
  fun projectee -> match projectee with | BvToNat -> true | uu___ -> false
let (uu___is_ITE : op -> Prims.bool) =
  fun projectee -> match projectee with | ITE -> true | uu___ -> false
let (uu___is_Var : op -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : op -> Prims.string) =
  fun projectee -> match projectee with | Var _0 -> _0
type qop =
  | Forall 
  | Exists 
let (uu___is_Forall : qop -> Prims.bool) =
  fun projectee -> match projectee with | Forall -> true | uu___ -> false
let (uu___is_Exists : qop -> Prims.bool) =
  fun projectee -> match projectee with | Exists -> true | uu___ -> false
type term' =
  | Integer of Prims.string 
  | String of Prims.string 
  | Real of Prims.string 
  | BoundV of Prims.int 
  | FreeV of fv 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int
  FStar_Pervasives_Native.option * sort Prims.list * term) 
  | Let of (term Prims.list * term) 
  | Labeled of (term * FStarC_Errors_Msg.error_message *
  FStarC_Compiler_Range_Type.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars: fv Prims.list FStarC_Syntax_Syntax.memo ;
  rng: FStarC_Compiler_Range_Type.range }
and fv =
  | FV of (Prims.string * sort * Prims.bool) 
let (uu___is_Integer : term' -> Prims.bool) =
  fun projectee -> match projectee with | Integer _0 -> true | uu___ -> false
let (__proj__Integer__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Integer _0 -> _0
let (uu___is_String : term' -> Prims.bool) =
  fun projectee -> match projectee with | String _0 -> true | uu___ -> false
let (__proj__String__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Real : term' -> Prims.bool) =
  fun projectee -> match projectee with | Real _0 -> true | uu___ -> false
let (__proj__Real__item___0 : term' -> Prims.string) =
  fun projectee -> match projectee with | Real _0 -> _0
let (uu___is_BoundV : term' -> Prims.bool) =
  fun projectee -> match projectee with | BoundV _0 -> true | uu___ -> false
let (__proj__BoundV__item___0 : term' -> Prims.int) =
  fun projectee -> match projectee with | BoundV _0 -> _0
let (uu___is_FreeV : term' -> Prims.bool) =
  fun projectee -> match projectee with | FreeV _0 -> true | uu___ -> false
let (__proj__FreeV__item___0 : term' -> fv) =
  fun projectee -> match projectee with | FreeV _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu___ -> false
let (__proj__App__item___0 : term' -> (op * term Prims.list)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Quant : term' -> Prims.bool) =
  fun projectee -> match projectee with | Quant _0 -> true | uu___ -> false
let (__proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * sort Prims.list * term))
  = fun projectee -> match projectee with | Quant _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu___ -> false
let (__proj__Let__item___0 : term' -> (term Prims.list * term)) =
  fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee -> match projectee with | Labeled _0 -> true | uu___ -> false
let (__proj__Labeled__item___0 :
  term' ->
    (term * FStarC_Errors_Msg.error_message *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_LblPos : term' -> Prims.bool) =
  fun projectee -> match projectee with | LblPos _0 -> true | uu___ -> false
let (__proj__LblPos__item___0 : term' -> (term * Prims.string)) =
  fun projectee -> match projectee with | LblPos _0 -> _0
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> tm
let (__proj__Mkterm__item__freevars :
  term -> fv Prims.list FStarC_Syntax_Syntax.memo) =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> freevars
let (__proj__Mkterm__item__rng : term -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | { tm; freevars; rng;_} -> rng
let (uu___is_FV : fv -> Prims.bool) = fun projectee -> true
let (__proj__FV__item___0 : fv -> (Prims.string * sort * Prims.bool)) =
  fun projectee -> match projectee with | FV _0 -> _0
type pat = term
type fvs = fv Prims.list
type caption = Prims.string FStar_Pervasives_Native.option
type binders = (Prims.string * sort) Prims.list
type constructor_field =
  {
  field_name: Prims.string ;
  field_sort: sort ;
  field_projectible: Prims.bool }
let (__proj__Mkconstructor_field__item__field_name :
  constructor_field -> Prims.string) =
  fun projectee ->
    match projectee with
    | { field_name; field_sort; field_projectible;_} -> field_name
let (__proj__Mkconstructor_field__item__field_sort :
  constructor_field -> sort) =
  fun projectee ->
    match projectee with
    | { field_name; field_sort; field_projectible;_} -> field_sort
let (__proj__Mkconstructor_field__item__field_projectible :
  constructor_field -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { field_name; field_sort; field_projectible;_} -> field_projectible
type constructor_t =
  {
  constr_name: Prims.string ;
  constr_fields: constructor_field Prims.list ;
  constr_sort: sort ;
  constr_id: Prims.int FStar_Pervasives_Native.option ;
  constr_base: Prims.bool }
let (__proj__Mkconstructor_t__item__constr_name :
  constructor_t -> Prims.string) =
  fun projectee ->
    match projectee with
    | { constr_name; constr_fields; constr_sort; constr_id; constr_base;_} ->
        constr_name
let (__proj__Mkconstructor_t__item__constr_fields :
  constructor_t -> constructor_field Prims.list) =
  fun projectee ->
    match projectee with
    | { constr_name; constr_fields; constr_sort; constr_id; constr_base;_} ->
        constr_fields
let (__proj__Mkconstructor_t__item__constr_sort : constructor_t -> sort) =
  fun projectee ->
    match projectee with
    | { constr_name; constr_fields; constr_sort; constr_id; constr_base;_} ->
        constr_sort
let (__proj__Mkconstructor_t__item__constr_id :
  constructor_t -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { constr_name; constr_fields; constr_sort; constr_id; constr_base;_} ->
        constr_id
let (__proj__Mkconstructor_t__item__constr_base :
  constructor_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { constr_name; constr_fields; constr_sort; constr_id; constr_base;_} ->
        constr_base
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStarC_Ident.lid 
  | Namespace of FStarC_Ident.lid 
  | Tag of Prims.string 
let (uu___is_Name : fact_db_id -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : fact_db_id -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Namespace : fact_db_id -> Prims.bool) =
  fun projectee ->
    match projectee with | Namespace _0 -> true | uu___ -> false
let (__proj__Namespace__item___0 : fact_db_id -> FStarC_Ident.lid) =
  fun projectee -> match projectee with | Namespace _0 -> _0
let (uu___is_Tag : fact_db_id -> Prims.bool) =
  fun projectee -> match projectee with | Tag _0 -> true | uu___ -> false
let (__proj__Tag__item___0 : fact_db_id -> Prims.string) =
  fun projectee -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term ;
  assumption_caption: caption ;
  assumption_name: Prims.string ;
  assumption_fact_ids: fact_db_id Prims.list ;
  assumption_free_names: Prims.string FStarC_Compiler_RBSet.t }
let (__proj__Mkassumption__item__assumption_term : assumption -> term) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids; assumption_free_names;_} -> assumption_term
let (__proj__Mkassumption__item__assumption_caption : assumption -> caption)
  =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids; assumption_free_names;_} -> assumption_caption
let (__proj__Mkassumption__item__assumption_name :
  assumption -> Prims.string) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids; assumption_free_names;_} -> assumption_name
let (__proj__Mkassumption__item__assumption_fact_ids :
  assumption -> fact_db_id Prims.list) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids; assumption_free_names;_} -> assumption_fact_ids
let (__proj__Mkassumption__item__assumption_free_names :
  assumption -> Prims.string FStarC_Compiler_RBSet.t) =
  fun projectee ->
    match projectee with
    | { assumption_term; assumption_caption; assumption_name;
        assumption_fact_ids; assumption_free_names;_} ->
        assumption_free_names
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
  | Push of Prims.int 
  | Pop of Prims.int 
  | CheckSat 
  | GetUnsatCore 
  | SetOption of (Prims.string * Prims.string) 
  | GetStatistics 
  | GetReasonUnknown 
let (uu___is_DefPrelude : decl -> Prims.bool) =
  fun projectee -> match projectee with | DefPrelude -> true | uu___ -> false
let (uu___is_DeclFun : decl -> Prims.bool) =
  fun projectee -> match projectee with | DeclFun _0 -> true | uu___ -> false
let (__proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption)) =
  fun projectee -> match projectee with | DeclFun _0 -> _0
let (uu___is_DefineFun : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineFun _0 -> true | uu___ -> false
let (__proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption)) =
  fun projectee -> match projectee with | DefineFun _0 -> _0
let (uu___is_Assume : decl -> Prims.bool) =
  fun projectee -> match projectee with | Assume _0 -> true | uu___ -> false
let (__proj__Assume__item___0 : decl -> assumption) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Caption : decl -> Prims.bool) =
  fun projectee -> match projectee with | Caption _0 -> true | uu___ -> false
let (__proj__Caption__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Caption _0 -> _0
let (uu___is_Module : decl -> Prims.bool) =
  fun projectee -> match projectee with | Module _0 -> true | uu___ -> false
let (__proj__Module__item___0 : decl -> (Prims.string * decl Prims.list)) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Eval : decl -> Prims.bool) =
  fun projectee -> match projectee with | Eval _0 -> true | uu___ -> false
let (__proj__Eval__item___0 : decl -> term) =
  fun projectee -> match projectee with | Eval _0 -> _0
let (uu___is_Echo : decl -> Prims.bool) =
  fun projectee -> match projectee with | Echo _0 -> true | uu___ -> false
let (__proj__Echo__item___0 : decl -> Prims.string) =
  fun projectee -> match projectee with | Echo _0 -> _0
let (uu___is_RetainAssumptions : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RetainAssumptions _0 -> true | uu___ -> false
let (__proj__RetainAssumptions__item___0 : decl -> Prims.string Prims.list) =
  fun projectee -> match projectee with | RetainAssumptions _0 -> _0
let (uu___is_Push : decl -> Prims.bool) =
  fun projectee -> match projectee with | Push _0 -> true | uu___ -> false
let (__proj__Push__item___0 : decl -> Prims.int) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_Pop : decl -> Prims.bool) =
  fun projectee -> match projectee with | Pop _0 -> true | uu___ -> false
let (__proj__Pop__item___0 : decl -> Prims.int) =
  fun projectee -> match projectee with | Pop _0 -> _0
let (uu___is_CheckSat : decl -> Prims.bool) =
  fun projectee -> match projectee with | CheckSat -> true | uu___ -> false
let (uu___is_GetUnsatCore : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetUnsatCore -> true | uu___ -> false
let (uu___is_SetOption : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOption _0 -> true | uu___ -> false
let (__proj__SetOption__item___0 : decl -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | SetOption _0 -> _0
let (uu___is_GetStatistics : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetStatistics -> true | uu___ -> false
let (uu___is_GetReasonUnknown : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | GetReasonUnknown -> true | uu___ -> false
type decls_elt =
  {
  sym_name: Prims.string FStar_Pervasives_Native.option ;
  key: Prims.string FStar_Pervasives_Native.option ;
  decls: decl Prims.list ;
  a_names: Prims.string Prims.list }
let (__proj__Mkdecls_elt__item__sym_name :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> sym_name
let (__proj__Mkdecls_elt__item__key :
  decls_elt -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> key
let (__proj__Mkdecls_elt__item__decls : decls_elt -> decl Prims.list) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> decls
let (__proj__Mkdecls_elt__item__a_names :
  decls_elt -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { sym_name; key; decls; a_names;_} -> a_names
type decls_t = decls_elt Prims.list
let (escape : Prims.string -> Prims.string) =
  fun s -> FStarC_Compiler_Util.replace_char s 39 95
let rec (strSort : sort -> Prims.string) =
  fun x ->
    match x with
    | Bool_sort -> "Bool"
    | Int_sort -> "Int"
    | Term_sort -> "Term"
    | String_sort -> "FString"
    | Fuel_sort -> "Fuel"
    | BitVec_sort n ->
        let uu___ = FStarC_Compiler_Util.string_of_int n in
        FStarC_Compiler_Util.format1 "(_ BitVec %s)" uu___
    | Array (s1, s2) ->
        let uu___ = strSort s1 in
        let uu___1 = strSort s2 in
        FStarC_Compiler_Util.format2 "(Array %s %s)" uu___ uu___1
    | Arrow (s1, s2) ->
        let uu___ = strSort s1 in
        let uu___1 = strSort s2 in
        FStarC_Compiler_Util.format2 "(%s -> %s)" uu___ uu___1
    | Sort s -> s
let (mk_decls :
  Prims.string ->
    Prims.string -> decl Prims.list -> decls_elt Prims.list -> decls_t)
  =
  fun name ->
    fun key ->
      fun decls ->
        fun aux_decls ->
          let uu___ =
            let uu___1 =
              let sm = FStarC_Compiler_Util.smap_create (Prims.of_int (20)) in
              FStarC_Compiler_List.iter
                (fun elt ->
                   FStarC_Compiler_List.iter
                     (fun s -> FStarC_Compiler_Util.smap_add sm s "0")
                     elt.a_names) aux_decls;
              FStarC_Compiler_List.iter
                (fun d ->
                   match d with
                   | Assume a ->
                       FStarC_Compiler_Util.smap_add sm a.assumption_name "0"
                   | uu___4 -> ()) decls;
              FStarC_Compiler_Util.smap_keys sm in
            {
              sym_name = (FStar_Pervasives_Native.Some name);
              key = (FStar_Pervasives_Native.Some key);
              decls;
              a_names = uu___1
            } in
          [uu___]
let (mk_decls_trivial : decl Prims.list -> decls_t) =
  fun decls ->
    let uu___ =
      let uu___1 =
        FStarC_Compiler_List.collect
          (fun uu___2 ->
             match uu___2 with
             | Assume a -> [a.assumption_name]
             | uu___3 -> []) decls in
      {
        sym_name = FStar_Pervasives_Native.None;
        key = FStar_Pervasives_Native.None;
        decls;
        a_names = uu___1
      } in
    [uu___]
let (decls_list_of : decls_t -> decl Prims.list) =
  fun l -> FStarC_Compiler_List.collect (fun elt -> elt.decls) l
let (mk_fv : (Prims.string * sort) -> fv) =
  fun uu___ -> match uu___ with | (x, y) -> FV (x, y, false)
let (fv_name : fv -> Prims.string) =
  fun x -> let uu___ = x in match uu___ with | FV (nm, uu___1, uu___2) -> nm
let (deq_fv : fv FStarC_Class_Deq.deq) =
  {
    FStarC_Class_Deq.op_Equals_Question =
      (fun fv1 ->
         fun fv2 ->
           let uu___ = fv_name fv1 in
           let uu___1 = fv_name fv2 in uu___ = uu___1)
  }
let (ord_fv : fv FStarC_Class_Ord.ord) =
  {
    FStarC_Class_Ord.super = deq_fv;
    FStarC_Class_Ord.cmp =
      (fun fv1 ->
         fun fv2 ->
           let uu___ =
             let uu___1 = fv_name fv1 in
             let uu___2 = fv_name fv2 in
             FStarC_Compiler_Util.compare uu___1 uu___2 in
           FStarC_Compiler_Order.order_from_int uu___)
  }
let (fv_sort : fv -> sort) =
  fun x ->
    let uu___ = x in match uu___ with | FV (uu___1, sort1, uu___2) -> sort1
let (fv_force : fv -> Prims.bool) =
  fun x ->
    let uu___ = x in match uu___ with | FV (uu___1, uu___2, force) -> force
type error_label =
  (fv * FStarC_Errors_Msg.error_message * FStarC_Compiler_Range_Type.range)
type error_labels = error_label Prims.list
let (fv_eq : fv -> fv -> Prims.bool) =
  fun x ->
    fun y ->
      let uu___ = fv_name x in let uu___1 = fv_name y in uu___ = uu___1
let (fvs_subset_of : fvs -> fvs -> Prims.bool) =
  fun x ->
    fun y ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Setlike.from_list ()
             (Obj.magic (FStarC_Compiler_RBSet.setlike_rbset ord_fv)) x) in
      let uu___1 =
        Obj.magic
          (FStarC_Class_Setlike.from_list ()
             (Obj.magic (FStarC_Compiler_RBSet.setlike_rbset ord_fv)) y) in
      FStarC_Class_Setlike.subset ()
        (Obj.magic (FStarC_Compiler_RBSet.setlike_rbset ord_fv))
        (Obj.magic uu___) (Obj.magic uu___1)
let (freevar_eq : term -> term -> Prims.bool) =
  fun x ->
    fun y ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1, FreeV y1) -> fv_eq x1 y1
      | uu___ -> false
let (freevar_sort : term -> sort) =
  fun uu___ ->
    match uu___ with
    | { tm = FreeV x; freevars = uu___1; rng = uu___2;_} -> fv_sort x
    | uu___1 -> failwith "impossible"
let (fv_of_term : term -> fv) =
  fun uu___ ->
    match uu___ with
    | { tm = FreeV fv1; freevars = uu___1; rng = uu___2;_} -> fv1
    | uu___1 -> failwith "impossible"
let rec (freevars : term -> fv Prims.list) =
  fun t ->
    match t.tm with
    | Integer uu___ -> []
    | String uu___ -> []
    | Real uu___ -> []
    | BoundV uu___ -> []
    | FreeV fv1 when fv_force fv1 -> []
    | FreeV fv1 -> [fv1]
    | App (uu___, tms) -> FStarC_Compiler_List.collect freevars tms
    | Quant (uu___, uu___1, uu___2, uu___3, t1) -> freevars t1
    | Labeled (t1, uu___, uu___1) -> freevars t1
    | LblPos (t1, uu___) -> freevars t1
    | Let (es, body) -> FStarC_Compiler_List.collect freevars (body :: es)
let (free_variables : term -> fvs) =
  fun t ->
    let uu___ = FStarC_Compiler_Effect.op_Bang t.freevars in
    match uu___ with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None ->
        let fvs1 =
          let uu___1 = freevars t in
          FStarC_Compiler_Util.remove_dups fv_eq uu___1 in
        (FStarC_Compiler_Effect.op_Colon_Equals t.freevars
           (FStar_Pervasives_Native.Some fvs1);
         fvs1)
let (free_top_level_names : term -> Prims.string FStarC_Compiler_RBSet.t) =
  fun t ->
    let rec free_top_level_names1 uu___1 uu___ =
      (fun acc ->
         fun t1 ->
           match t1.tm with
           | FreeV (FV (nm, uu___, uu___1)) ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Class_Setlike.add ()
                       (Obj.magic
                          (FStarC_Compiler_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) nm (Obj.magic acc)))
           | App (Var s, args) ->
               Obj.magic
                 (Obj.repr
                    (let acc1 =
                       Obj.magic
                         (FStarC_Class_Setlike.add ()
                            (Obj.magic
                               (FStarC_Compiler_RBSet.setlike_rbset
                                  FStarC_Class_Ord.ord_string)) s
                            (Obj.magic acc)) in
                     FStarC_Compiler_List.fold_left free_top_level_names1
                       acc1 args))
           | App (uu___, args) ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Compiler_List.fold_left free_top_level_names1 acc
                       args))
           | Quant (uu___, pats, uu___1, uu___2, body) ->
               Obj.magic
                 (Obj.repr
                    (let acc1 =
                       FStarC_Compiler_List.fold_left
                         (fun acc2 ->
                            fun pats1 ->
                              FStarC_Compiler_List.fold_left
                                free_top_level_names1 acc2 pats1) acc pats in
                     free_top_level_names1 acc1 body))
           | Let (tms, t2) ->
               Obj.magic
                 (Obj.repr
                    (let acc1 =
                       FStarC_Compiler_List.fold_left free_top_level_names1
                         acc tms in
                     free_top_level_names1 acc1 t2))
           | Labeled (t2, uu___, uu___1) ->
               Obj.magic (Obj.repr (free_top_level_names1 acc t2))
           | LblPos (t2, uu___) ->
               Obj.magic (Obj.repr (free_top_level_names1 acc t2))
           | uu___ -> Obj.magic (Obj.repr acc)) uu___1 uu___ in
    let uu___ =
      Obj.magic
        (FStarC_Class_Setlike.empty ()
           (Obj.magic
              (FStarC_Compiler_RBSet.setlike_rbset
                 FStarC_Class_Ord.ord_string)) ()) in
    free_top_level_names1 uu___ t
let (qop_to_string : qop -> Prims.string) =
  fun uu___ -> match uu___ with | Forall -> "forall" | Exists -> "exists"
let (op_to_string : op -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | TrueOp -> "true"
    | FalseOp -> "false"
    | Not -> "not"
    | And -> "and"
    | Or -> "or"
    | Imp -> "implies"
    | Iff -> "iff"
    | Eq -> "="
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="
    | Add -> "+"
    | Sub -> "-"
    | Div -> "div"
    | RealDiv -> "/"
    | Mul -> "*"
    | Minus -> "-"
    | Mod -> "mod"
    | ITE -> "ite"
    | BvAnd -> "bvand"
    | BvXor -> "bvxor"
    | BvOr -> "bvor"
    | BvAdd -> "bvadd"
    | BvSub -> "bvsub"
    | BvShl -> "bvshl"
    | BvShr -> "bvlshr"
    | BvUdiv -> "bvudiv"
    | BvMod -> "bvurem"
    | BvMul -> "bvmul"
    | BvUlt -> "bvult"
    | BvToNat -> "bv2int"
    | BvUext n ->
        let uu___1 = FStarC_Compiler_Util.string_of_int n in
        FStarC_Compiler_Util.format1 "(_ zero_extend %s)" uu___1
    | NatToBv n ->
        let uu___1 = FStarC_Compiler_Util.string_of_int n in
        FStarC_Compiler_Util.format1 "(_ int2bv %s)" uu___1
    | Var s -> s
let (weightToSmt : Prims.int FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        FStarC_Compiler_Util.format1 ":weight %s\n" uu___1
let rec (hash_of_term' : term' -> Prims.string) =
  fun t ->
    match t with
    | Integer i -> i
    | String s -> s
    | Real r -> r
    | BoundV i ->
        let uu___ = FStarC_Compiler_Util.string_of_int i in
        Prims.strcat "@" uu___
    | FreeV x ->
        let uu___ = fv_name x in
        let uu___1 =
          let uu___2 = let uu___3 = fv_sort x in strSort uu___3 in
          Prims.strcat ":" uu___2 in
        Prims.strcat uu___ uu___1
    | App (op1, tms) ->
        let uu___ =
          let uu___1 = op_to_string op1 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Compiler_List.map hash_of_term tms in
              FStarC_Compiler_String.concat " " uu___4 in
            Prims.strcat uu___3 ")" in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "(" uu___
    | Labeled (t1, r1, r2) ->
        let uu___ = hash_of_term t1 in
        let uu___1 =
          let uu___2 = FStarC_Errors_Msg.rendermsg r1 in
          let uu___3 = FStarC_Compiler_Range_Ops.string_of_range r2 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat uu___ uu___1
    | LblPos (t1, r) ->
        let uu___ =
          let uu___1 = hash_of_term t1 in
          Prims.strcat uu___1 (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu___
    | Quant (qop1, pats, wopt, sorts, body) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Compiler_List.map strSort sorts in
                FStarC_Compiler_String.concat " " uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = hash_of_term body in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = weightToSmt wopt in
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            let uu___13 =
                              FStarC_Compiler_List.map
                                (fun pats1 ->
                                   let uu___14 =
                                     FStarC_Compiler_List.map hash_of_term
                                       pats1 in
                                   FStarC_Compiler_String.concat " " uu___14)
                                pats in
                            FStarC_Compiler_String.concat "; " uu___13 in
                          Prims.strcat uu___12 "))" in
                        Prims.strcat " " uu___11 in
                      Prims.strcat uu___9 uu___10 in
                    Prims.strcat " " uu___8 in
                  Prims.strcat uu___6 uu___7 in
                Prims.strcat ")(! " uu___5 in
              Prims.strcat uu___3 uu___4 in
            Prims.strcat " (" uu___2 in
          Prims.strcat (qop_to_string qop1) uu___1 in
        Prims.strcat "(" uu___
    | Let (es, body) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Compiler_List.map hash_of_term es in
            FStarC_Compiler_String.concat " " uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = hash_of_term body in Prims.strcat uu___4 ")" in
            Prims.strcat ") " uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "(let (" uu___
and (hash_of_term : term -> Prims.string) = fun tm -> hash_of_term' tm.tm
let (mkBoxFunctions : Prims.string -> (Prims.string * Prims.string)) =
  fun s -> (s, (Prims.strcat s "_proj_0"))
let (boxIntFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxInt"
let (boxBoolFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxBool"
let (boxStringFun : (Prims.string * Prims.string)) =
  mkBoxFunctions "BoxString"
let (boxBitVecFun : Prims.int -> (Prims.string * Prims.string)) =
  fun sz ->
    let uu___ =
      let uu___1 = FStarC_Compiler_Util.string_of_int sz in
      Prims.strcat "BoxBitVec" uu___1 in
    mkBoxFunctions uu___
let (boxRealFun : (Prims.string * Prims.string)) = mkBoxFunctions "BoxReal"
let (isInjective : Prims.string -> Prims.bool) =
  fun s ->
    if (FStar_String.strlen s) >= (Prims.of_int (3))
    then
      (let uu___ =
         FStarC_Compiler_String.substring s Prims.int_zero (Prims.of_int (3)) in
       uu___ = "Box") &&
        (let uu___ =
           FStarC_Compiler_List.existsML (fun c -> c = 46)
             (FStar_String.list_of_string s) in
         Prims.op_Negation uu___)
    else false
let (mk : term' -> FStarC_Compiler_Range_Type.range -> term) =
  fun t ->
    fun r ->
      let uu___ = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu___; rng = r }
let (mkTrue : FStarC_Compiler_Range_Type.range -> term) =
  fun r -> mk (App (TrueOp, [])) r
let (mkFalse : FStarC_Compiler_Range_Type.range -> term) =
  fun r -> mk (App (FalseOp, [])) r
let (mkUnreachable : term) =
  mk (App ((Var "Unreachable"), [])) FStarC_Compiler_Range_Type.dummyRange
let (mkInteger : Prims.string -> FStarC_Compiler_Range_Type.range -> term) =
  fun i ->
    fun r ->
      let uu___ =
        let uu___1 = FStarC_Compiler_Util.ensure_decimal i in Integer uu___1 in
      mk uu___ r
let (mkInteger' : Prims.int -> FStarC_Compiler_Range_Type.range -> term) =
  fun i ->
    fun r ->
      let uu___ = FStarC_Compiler_Util.string_of_int i in mkInteger uu___ r
let (mkReal : Prims.string -> FStarC_Compiler_Range_Type.range -> term) =
  fun i -> fun r -> mk (Real i) r
let (mkBoundV : Prims.int -> FStarC_Compiler_Range_Type.range -> term) =
  fun i -> fun r -> mk (BoundV i) r
let (mkFreeV : fv -> FStarC_Compiler_Range_Type.range -> term) =
  fun x -> fun r -> mk (FreeV x) r
let (mkApp' :
  (op * term Prims.list) -> FStarC_Compiler_Range_Type.range -> term) =
  fun f -> fun r -> mk (App f) r
let (mkApp :
  (Prims.string * term Prims.list) ->
    FStarC_Compiler_Range_Type.range -> term)
  =
  fun uu___ ->
    fun r -> match uu___ with | (s, args) -> mk (App ((Var s), args)) r
let (mkNot : term -> FStarC_Compiler_Range_Type.range -> term) =
  fun t ->
    fun r ->
      match t.tm with
      | App (TrueOp, uu___) -> mkFalse r
      | App (FalseOp, uu___) -> mkTrue r
      | uu___ -> mkApp' (Not, [t]) r
let (mkAnd : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu___1), uu___2) -> t2
           | (uu___1, App (TrueOp, uu___2)) -> t1
           | (App (FalseOp, uu___1), uu___2) -> mkFalse r
           | (uu___1, App (FalseOp, uu___2)) -> mkFalse r
           | (App (And, ts1), App (And, ts2)) ->
               mkApp' (And, (FStarC_Compiler_List.op_At ts1 ts2)) r
           | (uu___1, App (And, ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And, ts1), uu___1) ->
               mkApp' (And, (FStarC_Compiler_List.op_At ts1 [t2])) r
           | uu___1 -> mkApp' (And, [t1; t2]) r)
let (mkOr : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp, uu___1), uu___2) -> mkTrue r
           | (uu___1, App (TrueOp, uu___2)) -> mkTrue r
           | (App (FalseOp, uu___1), uu___2) -> t2
           | (uu___1, App (FalseOp, uu___2)) -> t1
           | (App (Or, ts1), App (Or, ts2)) ->
               mkApp' (Or, (FStarC_Compiler_List.op_At ts1 ts2)) r
           | (uu___1, App (Or, ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or, ts1), uu___1) ->
               mkApp' (Or, (FStarC_Compiler_List.op_At ts1 [t2])) r
           | uu___1 -> mkApp' (Or, [t1; t2]) r)
let (mkImp : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu___1, App (TrueOp, uu___2)) -> mkTrue r
           | (App (FalseOp, uu___1), uu___2) -> mkTrue r
           | (App (TrueOp, uu___1), uu___2) -> t2
           | (uu___1, App (Imp, t1'::t2'::[])) ->
               let uu___2 =
                 let uu___3 = let uu___4 = mkAnd (t1, t1') r in [uu___4; t2'] in
                 (Imp, uu___3) in
               mkApp' uu___2 r
           | uu___1 -> mkApp' (Imp, [t1; t2]) r)
let (mk_bin_op :
  op -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun op1 ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (op1, [t1; t2]) r
let (mkMinus : term -> FStarC_Compiler_Range_Type.range -> term) =
  fun t -> fun r -> mkApp' (Minus, [t]) r
let (mkNatToBv :
  Prims.int -> term -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz -> fun t -> fun r -> mkApp' ((NatToBv sz), [t]) r
let (mkBvUext :
  Prims.int -> term -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz -> fun t -> fun r -> mkApp' ((BvUext sz), [t]) r
let (mkBvToNat : term -> FStarC_Compiler_Range_Type.range -> term) =
  fun t -> fun r -> mkApp' (BvToNat, [t]) r
let (mkBvAnd : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvAnd
let (mkBvXor : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvXor
let (mkBvOr : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvOr
let (mkBvAdd : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvAdd
let (mkBvSub : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvSub
let (mkBvShl :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (t1, t2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = mkNatToBv sz t2 r in [uu___4] in t1
                  :: uu___3 in
              (BvShl, uu___2) in
            mkApp' uu___1 r
let (mkBvShr :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (t1, t2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = mkNatToBv sz t2 r in [uu___4] in t1
                  :: uu___3 in
              (BvShr, uu___2) in
            mkApp' uu___1 r
let (mkBvUdiv :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (t1, t2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = mkNatToBv sz t2 r in [uu___4] in t1
                  :: uu___3 in
              (BvUdiv, uu___2) in
            mkApp' uu___1 r
let (mkBvMod :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (t1, t2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = mkNatToBv sz t2 r in [uu___4] in t1
                  :: uu___3 in
              (BvMod, uu___2) in
            mkApp' uu___1 r
let (mkBvMul :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (t1, t2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = mkNatToBv sz t2 r in [uu___4] in t1
                  :: uu___3 in
              (BvMul, uu___2) in
            mkApp' uu___1 r
let (mkBvShl' :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (BvShl, [t1; t2]) r
let (mkBvShr' :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (BvShr, [t1; t2]) r
let (mkBvMul' :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (BvMul, [t1; t2]) r
let (mkBvUdivUnsafe :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (BvUdiv, [t1; t2]) r
let (mkBvModUnsafe :
  Prims.int -> (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun sz ->
    fun uu___ ->
      fun r -> match uu___ with | (t1, t2) -> mkApp' (BvMod, [t1; t2]) r
let (mkBvUlt : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op BvUlt
let (mkIff : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Iff
let (mkEq : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (t1, t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (Var f1, s1::[]), App (Var f2, s2::[])) when
               (f1 = f2) && (isInjective f1) -> mk_bin_op Eq (s1, s2) r
           | uu___1 -> mk_bin_op Eq (t1, t2) r)
let (mkLT : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op LT
let (mkLTE : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op LTE
let (mkGT : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op GT
let (mkGTE : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op GTE
let (mkAdd : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Add
let (mkSub : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Sub
let (mkDiv : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Div
let (mkRealDiv : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op RealDiv
let (mkMul : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Mul
let (mkMod : (term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  mk_bin_op Mod
let (mkRealOfInt : term -> FStarC_Compiler_Range_Type.range -> term) =
  fun t -> fun r -> mkApp ("to_real", [t]) r
let (mkITE :
  (term * term * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (t1, t2, t3) ->
          (match t1.tm with
           | App (TrueOp, uu___1) -> t2
           | App (FalseOp, uu___1) -> t3
           | uu___1 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp, uu___2), App (TrueOp, uu___3)) -> mkTrue r
                | (App (TrueOp, uu___2), uu___3) ->
                    let uu___4 = let uu___5 = mkNot t1 t1.rng in (uu___5, t3) in
                    mkImp uu___4 r
                | (uu___2, App (TrueOp, uu___3)) -> mkImp (t1, t2) r
                | (uu___2, uu___3) -> mkApp' (ITE, [t1; t2; t3]) r))
let (mkCases : term Prims.list -> FStarC_Compiler_Range_Type.range -> term) =
  fun t ->
    fun r ->
      match t with
      | [] -> failwith "Impos"
      | hd::tl ->
          FStarC_Compiler_List.fold_left
            (fun out -> fun t1 -> mkAnd (out, t1) r) hd tl
let (check_pattern_ok : term -> term FStar_Pervasives_Native.option) =
  fun t ->
    let rec aux t1 =
      match t1.tm with
      | Integer uu___ -> FStar_Pervasives_Native.None
      | String uu___ -> FStar_Pervasives_Native.None
      | Real uu___ -> FStar_Pervasives_Native.None
      | BoundV uu___ -> FStar_Pervasives_Native.None
      | FreeV uu___ -> FStar_Pervasives_Native.None
      | Let (tms, tm) -> aux_l (tm :: tms)
      | App (head, terms) ->
          let head_ok =
            match head with
            | Var uu___ -> true
            | TrueOp -> true
            | FalseOp -> true
            | Not -> false
            | And -> false
            | Or -> false
            | Imp -> false
            | Iff -> false
            | Eq -> false
            | LT -> true
            | LTE -> true
            | GT -> true
            | GTE -> true
            | Add -> true
            | Sub -> true
            | Div -> true
            | RealDiv -> true
            | Mul -> true
            | Minus -> true
            | Mod -> true
            | BvAnd -> false
            | BvXor -> false
            | BvOr -> false
            | BvAdd -> false
            | BvSub -> false
            | BvShl -> false
            | BvShr -> false
            | BvUdiv -> false
            | BvMod -> false
            | BvMul -> false
            | BvUlt -> false
            | BvUext uu___ -> false
            | NatToBv uu___ -> false
            | BvToNat -> false
            | ITE -> false in
          if Prims.op_Negation head_ok
          then FStar_Pervasives_Native.Some t1
          else aux_l terms
      | Labeled (t2, uu___, uu___1) -> aux t2
      | Quant uu___ -> FStar_Pervasives_Native.Some t1
      | LblPos uu___ -> FStar_Pervasives_Native.Some t1
    and aux_l ts =
      match ts with
      | [] -> FStar_Pervasives_Native.None
      | t1::ts1 ->
          let uu___ = aux t1 in
          (match uu___ with
           | FStar_Pervasives_Native.Some t2 ->
               FStar_Pervasives_Native.Some t2
           | FStar_Pervasives_Native.None -> aux_l ts1) in
    aux t
let rec (print_smt_term : term -> Prims.string) =
  fun t ->
    match t.tm with
    | Integer n -> FStarC_Compiler_Util.format1 "(Integer %s)" n
    | String s -> FStarC_Compiler_Util.format1 "(String %s)" s
    | Real r -> FStarC_Compiler_Util.format1 "(Real %s)" r
    | BoundV n ->
        let uu___ = FStarC_Compiler_Util.string_of_int n in
        FStarC_Compiler_Util.format1 "(BoundV %s)" uu___
    | FreeV fv1 ->
        let uu___ = fv_name fv1 in
        FStarC_Compiler_Util.format1 "(FreeV %s)" uu___
    | App (op1, l) ->
        let uu___ = op_to_string op1 in
        let uu___1 = print_smt_term_list l in
        FStarC_Compiler_Util.format2 "(%s %s)" uu___ uu___1
    | Labeled (t1, r1, r2) ->
        let uu___ = FStarC_Errors_Msg.rendermsg r1 in
        let uu___1 = print_smt_term t1 in
        FStarC_Compiler_Util.format2 "(Labeled '%s' %s)" uu___ uu___1
    | LblPos (t1, s) ->
        let uu___ = print_smt_term t1 in
        FStarC_Compiler_Util.format2 "(LblPos %s %s)" s uu___
    | Quant (qop1, l, uu___, uu___1, t1) ->
        let uu___2 = print_smt_term_list_list l in
        let uu___3 = print_smt_term t1 in
        FStarC_Compiler_Util.format3 "(%s %s %s)" (qop_to_string qop1) uu___2
          uu___3
    | Let (es, body) ->
        let uu___ = print_smt_term_list es in
        let uu___1 = print_smt_term body in
        FStarC_Compiler_Util.format2 "(let %s %s)" uu___ uu___1
and (print_smt_term_list : term Prims.list -> Prims.string) =
  fun l ->
    let uu___ = FStarC_Compiler_List.map print_smt_term l in
    FStarC_Compiler_String.concat " " uu___
and (print_smt_term_list_list : term Prims.list Prims.list -> Prims.string) =
  fun l ->
    FStarC_Compiler_List.fold_left
      (fun s ->
         fun l1 ->
           let uu___ =
             let uu___1 =
               let uu___2 = print_smt_term_list l1 in
               Prims.strcat uu___2 " ] " in
             Prims.strcat "; [ " uu___1 in
           Prims.strcat s uu___) "" l
let (mkQuant :
  FStarC_Compiler_Range_Type.range ->
    Prims.bool ->
      (qop * term Prims.list Prims.list * Prims.int
        FStar_Pervasives_Native.option * sort Prims.list * term) -> term)
  =
  fun r ->
    fun check_pats ->
      fun uu___ ->
        match uu___ with
        | (qop1, pats, wopt, vars, body) ->
            let all_pats_ok pats1 =
              if Prims.op_Negation check_pats
              then pats1
              else
                (let uu___2 =
                   FStarC_Compiler_Util.find_map pats1
                     (fun x ->
                        FStarC_Compiler_Util.find_map x check_pattern_ok) in
                 match uu___2 with
                 | FStar_Pervasives_Native.None -> pats1
                 | FStar_Pervasives_Native.Some p ->
                     ((let uu___4 =
                         let uu___5 = print_smt_term p in
                         FStarC_Compiler_Util.format1
                           "Pattern (%s) contains illegal symbols; dropping it"
                           uu___5 in
                       FStarC_Errors.log_issue
                         FStarC_Class_HasRange.hasRange_range r
                         FStarC_Errors_Codes.Warning_SMTPatternIllFormed ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___4));
                      [])) in
            if (FStarC_Compiler_List.length vars) = Prims.int_zero
            then body
            else
              (match body.tm with
               | App (TrueOp, uu___2) -> body
               | uu___2 ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = all_pats_ok pats in
                       (qop1, uu___5, wopt, vars, body) in
                     Quant uu___4 in
                   mk uu___3 r)
let (mkLet :
  (term Prims.list * term) -> FStarC_Compiler_Range_Type.range -> term) =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (es, body) ->
          if (FStarC_Compiler_List.length es) = Prims.int_zero
          then body
          else mk (Let (es, body)) r
let (abstr : fv Prims.list -> term -> term) =
  fun fvs1 ->
    fun t ->
      let nvars = FStarC_Compiler_List.length fvs1 in
      let index_of fv1 =
        let uu___ = FStarC_Compiler_Util.try_find_index (fv_eq fv1) fvs1 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some (nvars - (i + Prims.int_one)) in
      let rec aux ix t1 =
        let uu___ = FStarC_Compiler_Effect.op_Bang t1.freevars in
        match uu___ with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu___1 ->
            (match t1.tm with
             | Integer uu___2 -> t1
             | String uu___2 -> t1
             | Real uu___2 -> t1
             | BoundV uu___2 -> t1
             | FreeV x ->
                 let uu___2 = index_of x in
                 (match uu___2 with
                  | FStar_Pervasives_Native.None -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op1, tms) ->
                 let uu___2 =
                   let uu___3 = FStarC_Compiler_List.map (aux ix) tms in
                   (op1, uu___3) in
                 mkApp' uu___2 t1.rng
             | Labeled (t2, r1, r2) ->
                 let uu___2 =
                   let uu___3 = let uu___4 = aux ix t2 in (uu___4, r1, r2) in
                   Labeled uu___3 in
                 mk uu___2 t2.rng
             | LblPos (t2, r) ->
                 let uu___2 =
                   let uu___3 = let uu___4 = aux ix t2 in (uu___4, r) in
                   LblPos uu___3 in
                 mk uu___2 t2.rng
             | Quant (qop1, pats, wopt, vars, body) ->
                 let n = FStarC_Compiler_List.length vars in
                 let uu___2 =
                   let uu___3 =
                     FStarC_Compiler_List.map
                       (FStarC_Compiler_List.map (aux (ix + n))) pats in
                   let uu___4 = aux (ix + n) body in
                   (qop1, uu___3, wopt, vars, uu___4) in
                 mkQuant t1.rng false uu___2
             | Let (es, body) ->
                 let uu___2 =
                   FStarC_Compiler_List.fold_left
                     (fun uu___3 ->
                        fun e ->
                          match uu___3 with
                          | (ix1, l) ->
                              let uu___4 =
                                let uu___5 = aux ix1 e in uu___5 :: l in
                              ((ix1 + Prims.int_one), uu___4)) (ix, []) es in
                 (match uu___2 with
                  | (ix1, es_rev) ->
                      let uu___3 =
                        let uu___4 = aux ix1 body in
                        ((FStarC_Compiler_List.rev es_rev), uu___4) in
                      mkLet uu___3 t1.rng)) in
      aux Prims.int_zero t
let (inst : term Prims.list -> term -> term) =
  fun tms ->
    fun t ->
      let tms1 = FStarC_Compiler_List.rev tms in
      let n = FStarC_Compiler_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu___ -> t1
        | String uu___ -> t1
        | Real uu___ -> t1
        | FreeV uu___ -> t1
        | BoundV i ->
            if (Prims.int_zero <= (i - shift)) && ((i - shift) < n)
            then FStarC_Compiler_List.nth tms1 (i - shift)
            else t1
        | App (op1, tms2) ->
            let uu___ =
              let uu___1 = FStarC_Compiler_List.map (aux shift) tms2 in
              (op1, uu___1) in
            mkApp' uu___ t1.rng
        | Labeled (t2, r1, r2) ->
            let uu___ =
              let uu___1 = let uu___2 = aux shift t2 in (uu___2, r1, r2) in
              Labeled uu___1 in
            mk uu___ t2.rng
        | LblPos (t2, r) ->
            let uu___ =
              let uu___1 = let uu___2 = aux shift t2 in (uu___2, r) in
              LblPos uu___1 in
            mk uu___ t2.rng
        | Quant (qop1, pats, wopt, vars, body) ->
            let m = FStarC_Compiler_List.length vars in
            let shift1 = shift + m in
            let uu___ =
              let uu___1 =
                FStarC_Compiler_List.map
                  (FStarC_Compiler_List.map (aux shift1)) pats in
              let uu___2 = aux shift1 body in
              (qop1, uu___1, wopt, vars, uu___2) in
            mkQuant t1.rng false uu___
        | Let (es, body) ->
            let uu___ =
              FStarC_Compiler_List.fold_left
                (fun uu___1 ->
                   fun e ->
                     match uu___1 with
                     | (ix, es1) ->
                         let uu___2 =
                           let uu___3 = aux shift e in uu___3 :: es1 in
                         ((shift + Prims.int_one), uu___2)) (shift, []) es in
            (match uu___ with
             | (shift1, es_rev) ->
                 let uu___1 =
                   let uu___2 = aux shift1 body in
                   ((FStarC_Compiler_List.rev es_rev), uu___2) in
                 mkLet uu___1 t1.rng) in
      aux Prims.int_zero t
let (subst : term -> fv -> term -> term) =
  fun t -> fun fv1 -> fun s -> let uu___ = abstr [fv1] t in inst [s] uu___
let (mkQuant' :
  FStarC_Compiler_Range_Type.range ->
    (qop * term Prims.list Prims.list * Prims.int
      FStar_Pervasives_Native.option * fv Prims.list * term) -> term)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (qop1, pats, wopt, vars, body) ->
          let uu___1 =
            let uu___2 =
              FStarC_Compiler_List.map
                (FStarC_Compiler_List.map (abstr vars)) pats in
            let uu___3 = FStarC_Compiler_List.map fv_sort vars in
            let uu___4 = abstr vars body in
            (qop1, uu___2, wopt, uu___3, uu___4) in
          mkQuant r true uu___1
let (mkForall :
  FStarC_Compiler_Range_Type.range ->
    (pat Prims.list Prims.list * fvs * term) -> term)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (pats, vars, body) ->
          mkQuant' r (Forall, pats, FStar_Pervasives_Native.None, vars, body)
let (mkForall'' :
  FStarC_Compiler_Range_Type.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      sort Prims.list * term) -> term)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (pats, wopt, sorts, body) ->
          mkQuant r true (Forall, pats, wopt, sorts, body)
let (mkForall' :
  FStarC_Compiler_Range_Type.range ->
    (pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option *
      fvs * term) -> term)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (pats, wopt, vars, body) ->
          mkQuant' r (Forall, pats, wopt, vars, body)
let (mkExists :
  FStarC_Compiler_Range_Type.range ->
    (pat Prims.list Prims.list * fvs * term) -> term)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (pats, vars, body) ->
          mkQuant' r (Exists, pats, FStar_Pervasives_Native.None, vars, body)
let (mkLet' :
  ((fv * term) Prims.list * term) -> FStarC_Compiler_Range_Type.range -> term)
  =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (bindings, body) ->
          let uu___1 = FStarC_Compiler_List.split bindings in
          (match uu___1 with
           | (vars, es) ->
               let uu___2 = let uu___3 = abstr vars body in (es, uu___3) in
               mkLet uu___2 r)
let (norng : FStarC_Compiler_Range_Type.range) =
  FStarC_Compiler_Range_Type.dummyRange
let (mkDefineFun :
  (Prims.string * fv Prims.list * sort * term * caption) -> decl) =
  fun uu___ ->
    match uu___ with
    | (nm, vars, s, tm, c) ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map fv_sort vars in
          let uu___3 = abstr vars tm in (nm, uu___2, s, uu___3, c) in
        DefineFun uu___1
let (constr_id_of_sort : sort -> Prims.string) =
  fun sort1 ->
    let uu___ = strSort sort1 in
    FStarC_Compiler_Util.format1 "%s_constr_id" uu___
let (fresh_token : (Prims.string * sort) -> Prims.int -> decl) =
  fun uu___ ->
    fun id ->
      match uu___ with
      | (tok_name, sort1) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let tm =
            let uu___1 =
              let uu___2 = mkInteger' id norng in
              let uu___3 =
                let uu___4 =
                  let uu___5 = constr_id_of_sort sort1 in
                  let uu___6 =
                    let uu___7 = mkApp (tok_name, []) norng in [uu___7] in
                  (uu___5, uu___6) in
                mkApp uu___4 norng in
              (uu___2, uu___3) in
            mkEq uu___1 norng in
          let a =
            let uu___1 = escape a_name in
            let uu___2 = free_top_level_names tm in
            {
              assumption_term = tm;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = uu___1;
              assumption_fact_ids = [];
              assumption_free_names = uu___2
            } in
          Assume a
let (fresh_constructor :
  FStarC_Compiler_Range_Type.range ->
    (Prims.string * sort Prims.list * sort * Prims.int) -> decl)
  =
  fun rng ->
    fun uu___ ->
      match uu___ with
      | (name, arg_sorts, sort1, id) ->
          let id1 = FStarC_Compiler_Util.string_of_int id in
          let bvars =
            FStarC_Compiler_List.mapi
              (fun i ->
                 fun s ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = FStarC_Compiler_Util.string_of_int i in
                         Prims.strcat "x_" uu___4 in
                       (uu___3, s) in
                     mk_fv uu___2 in
                   mkFreeV uu___1 norng) arg_sorts in
          let bvar_names = FStarC_Compiler_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let cid_app =
            let uu___1 =
              let uu___2 = constr_id_of_sort sort1 in (uu___2, [capp]) in
            mkApp uu___1 norng in
          let a_name = Prims.strcat "constructor_distinct_" name in
          let tm =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = mkInteger id1 norng in (uu___4, cid_app) in
                mkEq uu___3 norng in
              ([[capp]], bvar_names, uu___2) in
            mkForall rng uu___1 in
          let a =
            let uu___1 = escape a_name in
            let uu___2 = free_top_level_names tm in
            {
              assumption_term = tm;
              assumption_caption =
                (FStar_Pervasives_Native.Some "Constructor distinct");
              assumption_name = uu___1;
              assumption_fact_ids = [];
              assumption_free_names = uu___2
            } in
          Assume a
let (injective_constructor :
  FStarC_Compiler_Range_Type.range ->
    (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list)
  =
  fun rng ->
    fun uu___ ->
      match uu___ with
      | (name, fields, sort1) ->
          let n_bvars = FStarC_Compiler_List.length fields in
          let bvar_name i =
            let uu___1 = FStarC_Compiler_Util.string_of_int i in
            Prims.strcat "x_" uu___1 in
          let bvar_index i = n_bvars - (i + Prims.int_one) in
          let bvar i s =
            let uu___1 =
              let uu___2 = let uu___3 = bvar_name i in (uu___3, s) in
              mk_fv uu___2 in
            mkFreeV uu___1 in
          let bvars =
            FStarC_Compiler_List.mapi
              (fun i ->
                 fun f -> let uu___1 = bvar i f.field_sort in uu___1 norng)
              fields in
          let bvar_names = FStarC_Compiler_List.map fv_of_term bvars in
          let capp = mkApp (name, bvars) norng in
          let uu___1 =
            FStarC_Compiler_List.mapi
              (fun i ->
                 fun uu___2 ->
                   match uu___2 with
                   | { field_name = name1; field_sort = s;
                       field_projectible = projectible;_} ->
                       if projectible
                       then
                         let cproj_app = mkApp (name1, [capp]) norng in
                         let proj_name =
                           DeclFun
                             (name1, [sort1], s,
                               (FStar_Pervasives_Native.Some "Projector")) in
                         let tm =
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 = bvar i s in uu___7 norng in
                                 (cproj_app, uu___6) in
                               mkEq uu___5 norng in
                             ([[capp]], bvar_names, uu___4) in
                           mkForall rng uu___3 in
                         let a =
                           let uu___3 =
                             escape
                               (Prims.strcat "projection_inverse_" name1) in
                           let uu___4 = free_top_level_names tm in
                           {
                             assumption_term = tm;
                             assumption_caption =
                               (FStar_Pervasives_Native.Some
                                  "Projection inverse");
                             assumption_name = uu___3;
                             assumption_fact_ids = [];
                             assumption_free_names = uu___4
                           } in
                         [proj_name; Assume a]
                       else []) fields in
          FStarC_Compiler_List.flatten uu___1
let (discriminator_name : constructor_t -> Prims.string) =
  fun constr -> Prims.strcat "is-" constr.constr_name
let (constructor_to_decl :
  FStarC_Compiler_Range_Type.range -> constructor_t -> decl Prims.list) =
  fun rng ->
    fun constr ->
      let sort1 = constr.constr_sort in
      let field_sorts =
        FStarC_Compiler_List.map (fun f -> f.field_sort) constr.constr_fields in
      let cdecl =
        DeclFun
          ((constr.constr_name), field_sorts, (constr.constr_sort),
            (FStar_Pervasives_Native.Some "Constructor")) in
      let cid =
        match constr.constr_id with
        | FStar_Pervasives_Native.None -> []
        | FStar_Pervasives_Native.Some id ->
            let uu___ =
              fresh_constructor rng
                ((constr.constr_name), field_sorts, sort1, id) in
            [uu___] in
      let disc =
        let disc_name = discriminator_name constr in
        let xfv = mk_fv ("x", sort1) in
        let xx = mkFreeV xfv norng in
        let uu___ =
          let uu___1 =
            FStarC_Compiler_List.mapi
              (fun i ->
                 fun uu___2 ->
                   match uu___2 with
                   | { field_name = proj; field_sort = s;
                       field_projectible = projectible;_} ->
                       if projectible
                       then
                         let uu___3 = mkApp (proj, [xx]) norng in
                         (uu___3, [])
                       else
                         (let fi =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStarC_Compiler_Util.string_of_int i in
                                Prims.strcat "f_" uu___6 in
                              (uu___5, s) in
                            mk_fv uu___4 in
                          let uu___4 = mkFreeV fi norng in (uu___4, [fi])))
              constr.constr_fields in
          FStarC_Compiler_List.split uu___1 in
        match uu___ with
        | (proj_terms, ex_vars) ->
            let ex_vars1 = FStarC_Compiler_List.flatten ex_vars in
            let disc_inv_body =
              let uu___1 =
                let uu___2 = mkApp ((constr.constr_name), proj_terms) norng in
                (xx, uu___2) in
              mkEq uu___1 norng in
            let disc_inv_body1 =
              match ex_vars1 with
              | [] -> disc_inv_body
              | uu___1 -> mkExists norng ([], ex_vars1, disc_inv_body) in
            let disc_ax =
              match constr.constr_id with
              | FStar_Pervasives_Native.None -> disc_inv_body1
              | FStar_Pervasives_Native.Some id ->
                  let disc_eq =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = constr_id_of_sort constr.constr_sort in
                          (uu___4, [xx]) in
                        mkApp uu___3 norng in
                      let uu___3 =
                        let uu___4 = FStarC_Compiler_Util.string_of_int id in
                        mkInteger uu___4 norng in
                      (uu___2, uu___3) in
                    mkEq uu___1 norng in
                  mkAnd (disc_eq, disc_inv_body1) norng in
            let def =
              mkDefineFun
                (disc_name, [xfv], Bool_sort, disc_ax,
                  (FStar_Pervasives_Native.Some "Discriminator definition")) in
            def in
      let projs =
        injective_constructor rng
          ((constr.constr_name), (constr.constr_fields), sort1) in
      let base =
        if Prims.op_Negation constr.constr_base
        then []
        else
          (let arg_sorts =
             let uu___1 =
               FStarC_Compiler_List.filter (fun f -> f.field_projectible)
                 constr.constr_fields in
             FStarC_Compiler_List.map (fun uu___2 -> Term_sort) uu___1 in
           let base_name = Prims.strcat constr.constr_name "@base" in
           let decl1 =
             DeclFun
               (base_name, arg_sorts, Term_sort,
                 (FStar_Pervasives_Native.Some "Constructor base")) in
           let formals =
             FStarC_Compiler_List.mapi
               (fun i ->
                  fun uu___1 ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStarC_Compiler_Util.string_of_int i in
                        Prims.strcat "x" uu___4 in
                      (uu___3, Term_sort) in
                    mk_fv uu___2) constr.constr_fields in
           let constructed_term =
             let uu___1 =
               let uu___2 =
                 FStarC_Compiler_List.map (fun fv1 -> mkFreeV fv1 norng)
                   formals in
               ((constr.constr_name), uu___2) in
             mkApp uu___1 norng in
           let inj_formals =
             let uu___1 =
               FStarC_Compiler_List.map2
                 (fun f ->
                    fun fld -> if fld.field_projectible then [f] else [])
                 formals constr.constr_fields in
             FStarC_Compiler_List.flatten uu___1 in
           let base_term =
             let uu___1 =
               let uu___2 =
                 FStarC_Compiler_List.map (fun fv1 -> mkFreeV fv1 norng)
                   inj_formals in
               (base_name, uu___2) in
             mkApp uu___1 norng in
           let eq = mkEq (constructed_term, base_term) norng in
           let guard =
             mkApp ((discriminator_name constr), [constructed_term]) norng in
           let q =
             let uu___1 =
               let uu___2 = mkImp (guard, eq) norng in
               ([[constructed_term]], formals, uu___2) in
             mkForall rng uu___1 in
           let a =
             let uu___1 =
               escape (Prims.strcat "constructor_base_" constr.constr_name) in
             let uu___2 = free_top_level_names q in
             {
               assumption_term = q;
               assumption_caption =
                 (FStar_Pervasives_Native.Some "Constructor base");
               assumption_name = uu___1;
               assumption_fact_ids = [];
               assumption_free_names = uu___2
             } in
           [decl1; Assume a]) in
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_Util.format1 "<start constructor %s>"
              constr.constr_name in
          Caption uu___2 in
        [uu___1; cdecl] in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStarC_Compiler_Util.format1 "</end constructor %s>"
                      constr.constr_name in
                  Caption uu___7 in
                [uu___6] in
              FStarC_Compiler_List.op_At base uu___5 in
            FStarC_Compiler_List.op_At [disc] uu___4 in
          FStarC_Compiler_List.op_At projs uu___3 in
        FStarC_Compiler_List.op_At cid uu___2 in
      FStarC_Compiler_List.op_At uu___ uu___1
let (name_binders_inner :
  Prims.string FStar_Pervasives_Native.option ->
    fv Prims.list ->
      Prims.int ->
        sort Prims.list ->
          (fv Prims.list * Prims.string Prims.list * Prims.int))
  =
  fun prefix_opt ->
    fun outer_names ->
      fun start ->
        fun sorts ->
          let uu___ =
            FStarC_Compiler_List.fold_left
              (fun uu___1 ->
                 fun s ->
                   match uu___1 with
                   | (names, binders1, n) ->
                       let prefix =
                         match s with | Term_sort -> "@x" | uu___2 -> "@u" in
                       let prefix1 =
                         match prefix_opt with
                         | FStar_Pervasives_Native.None -> prefix
                         | FStar_Pervasives_Native.Some p ->
                             Prims.strcat p prefix in
                       let nm =
                         let uu___2 = FStarC_Compiler_Util.string_of_int n in
                         Prims.strcat prefix1 uu___2 in
                       let names1 =
                         let uu___2 = mk_fv (nm, s) in uu___2 :: names in
                       let b =
                         let uu___2 = strSort s in
                         FStarC_Compiler_Util.format2 "(%s %s)" nm uu___2 in
                       (names1, (b :: binders1), (n + Prims.int_one)))
              (outer_names, [], start) sorts in
          match uu___ with
          | (names, binders1, n) ->
              (names, (FStarC_Compiler_List.rev binders1), n)
let (name_macro_binders :
  sort Prims.list -> (fv Prims.list * Prims.string Prims.list)) =
  fun sorts ->
    let uu___ =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        Prims.int_zero sorts in
    match uu___ with
    | (names, binders1, n) -> ((FStarC_Compiler_List.rev names), binders1)
let (termToSmt : Prims.bool -> Prims.string -> term -> Prims.string) =
  let string_id_counter = FStarC_Compiler_Util.mk_ref Prims.int_zero in
  let string_cache = FStarC_Compiler_Util.smap_create (Prims.of_int (20)) in
  fun print_ranges ->
    fun enclosing_name ->
      fun t ->
        let next_qid =
          let ctr = FStarC_Compiler_Util.mk_ref Prims.int_zero in
          fun depth ->
            let n = FStarC_Compiler_Effect.op_Bang ctr in
            FStarC_Compiler_Util.incr ctr;
            if n = Prims.int_zero
            then enclosing_name
            else
              (let uu___2 = FStarC_Compiler_Util.string_of_int n in
               FStarC_Compiler_Util.format2 "%s.%s" enclosing_name uu___2) in
        let remove_guard_free pats =
          FStarC_Compiler_List.map
            (fun ps ->
               FStarC_Compiler_List.map
                 (fun tm ->
                    match tm.tm with
                    | App
                        (Var "Prims.guard_free",
                         { tm = BoundV uu___; freevars = uu___1;
                           rng = uu___2;_}::[])
                        -> tm
                    | App (Var "Prims.guard_free", p::[]) -> p
                    | uu___ -> tm) ps) pats in
        let rec aux' depth n names t1 =
          let aux1 = aux (depth + Prims.int_one) in
          match t1.tm with
          | Integer i -> i
          | Real r -> r
          | String s ->
              let id_opt = FStarC_Compiler_Util.smap_try_find string_cache s in
              (match id_opt with
               | FStar_Pervasives_Native.Some id -> id
               | FStar_Pervasives_Native.None ->
                   let id =
                     let uu___ =
                       FStarC_Compiler_Effect.op_Bang string_id_counter in
                     FStarC_Compiler_Util.string_of_int uu___ in
                   (FStarC_Compiler_Util.incr string_id_counter;
                    FStarC_Compiler_Util.smap_add string_cache s id;
                    id))
          | BoundV i ->
              let uu___ = FStarC_Compiler_List.nth names i in fv_name uu___
          | FreeV x when fv_force x ->
              let uu___ =
                let uu___1 = fv_name x in Prims.strcat uu___1 " Dummy_value)" in
              Prims.strcat "(" uu___
          | FreeV x -> fv_name x
          | App (op1, []) -> op_to_string op1
          | App (op1, tms) ->
              let uu___ = op_to_string op1 in
              let uu___1 =
                let uu___2 = FStarC_Compiler_List.map (aux1 n names) tms in
                FStarC_Compiler_String.concat "\n" uu___2 in
              FStarC_Compiler_Util.format2 "(%s %s)" uu___ uu___1
          | Labeled (t2, uu___, uu___1) -> aux1 n names t2
          | LblPos (t2, s) ->
              let uu___ = aux1 n names t2 in
              FStarC_Compiler_Util.format2 "(! %s :lblpos %s)" uu___ s
          | Quant (qop1, pats, wopt, sorts, body) ->
              let qid = next_qid () in
              let uu___ =
                name_binders_inner FStar_Pervasives_Native.None names n sorts in
              (match uu___ with
               | (names1, binders1, n1) ->
                   let binders2 = FStarC_Compiler_String.concat " " binders1 in
                   let pats1 = remove_guard_free pats in
                   let pats_str =
                     match pats1 with
                     | []::[] -> if print_ranges then ";;no pats" else ""
                     | [] -> if print_ranges then ";;no pats" else ""
                     | uu___1 ->
                         let uu___2 =
                           FStarC_Compiler_List.map
                             (fun pats2 ->
                                let uu___3 =
                                  let uu___4 =
                                    FStarC_Compiler_List.map
                                      (fun p ->
                                         let uu___5 = aux1 n1 names1 p in
                                         FStarC_Compiler_Util.format1 "%s"
                                           uu___5) pats2 in
                                  FStarC_Compiler_String.concat " " uu___4 in
                                FStarC_Compiler_Util.format1
                                  "\n:pattern (%s)" uu___3) pats1 in
                         FStarC_Compiler_String.concat "\n" uu___2 in
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = aux1 n1 names1 body in
                         let uu___5 =
                           let uu___6 = weightToSmt wopt in
                           [uu___6; pats_str; qid] in
                         uu___4 :: uu___5 in
                       binders2 :: uu___3 in
                     (qop_to_string qop1) :: uu___2 in
                   FStarC_Compiler_Util.format
                     "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))" uu___1)
          | Let (es, body) ->
              let uu___ =
                FStarC_Compiler_List.fold_left
                  (fun uu___1 ->
                     fun e ->
                       match uu___1 with
                       | (names0, binders1, n0) ->
                           let nm =
                             let uu___2 =
                               FStarC_Compiler_Util.string_of_int n0 in
                             Prims.strcat "@lb" uu___2 in
                           let names01 =
                             let uu___2 = mk_fv (nm, Term_sort) in uu___2 ::
                               names0 in
                           let b =
                             let uu___2 = aux1 n names e in
                             FStarC_Compiler_Util.format2 "(%s %s)" nm uu___2 in
                           (names01, (b :: binders1), (n0 + Prims.int_one)))
                  (names, [], n) es in
              (match uu___ with
               | (names1, binders1, n1) ->
                   let uu___1 = aux1 n1 names1 body in
                   FStarC_Compiler_Util.format2 "(let (%s)\n%s)"
                     (FStarC_Compiler_String.concat " " binders1) uu___1)
        and aux depth n names t1 =
          let s = aux' depth n names t1 in
          if print_ranges && (t1.rng <> norng)
          then
            let uu___ = FStarC_Compiler_Range_Ops.string_of_range t1.rng in
            let uu___1 = FStarC_Compiler_Range_Ops.string_of_use_range t1.rng in
            FStarC_Compiler_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu___
              uu___1 s
          else s in
        aux Prims.int_zero Prims.int_zero [] t
let (caption_to_string :
  Prims.bool -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun print_captions ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some c when print_captions ->
          let c1 =
            let uu___1 =
              FStarC_Compiler_List.map FStarC_Compiler_Util.trim_string
                (FStarC_Compiler_String.split [10] c) in
            FStarC_Compiler_String.concat " " uu___1 in
          Prims.strcat ";;;;;;;;;;;;;;;;" (Prims.strcat c1 "\n")
      | uu___1 -> ""
let rec (declToSmt' : Prims.bool -> Prims.string -> decl -> Prims.string) =
  fun print_captions ->
    fun z3options ->
      fun decl1 ->
        match decl1 with
        | DefPrelude -> mkPrelude z3options
        | Module (s, decls) ->
            let res =
              let uu___ =
                FStarC_Compiler_List.map
                  (declToSmt' print_captions z3options) decls in
              FStarC_Compiler_String.concat "\n" uu___ in
            let uu___ = FStarC_Options.keep_query_captions () in
            if uu___
            then
              let uu___1 =
                FStarC_Compiler_Util.string_of_int
                  (FStarC_Compiler_List.length decls) in
              let uu___2 =
                FStarC_Compiler_Util.string_of_int
                  (FStarC_Compiler_String.length res) in
              FStarC_Compiler_Util.format5
                "\n;;; Start %s\n%s\n;;; End %s (%s decls; total size %s)" s
                res s uu___1 uu___2
            else res
        | Caption c ->
            if print_captions
            then
              let uu___ =
                let uu___1 =
                  FStarC_Compiler_List.map
                    (fun s -> Prims.strcat "; " (Prims.strcat s "\n"))
                    (FStarC_Compiler_Util.splitlines c) in
                FStarC_Compiler_String.concat "" uu___1 in
              Prims.strcat "\n" uu___
            else ""
        | DeclFun (f, argsorts, retsort, c) ->
            let l = FStarC_Compiler_List.map strSort argsorts in
            let uu___ = caption_to_string print_captions c in
            let uu___1 = strSort retsort in
            FStarC_Compiler_Util.format4 "%s(declare-fun %s (%s) %s)" uu___ f
              (FStarC_Compiler_String.concat " " l) uu___1
        | DefineFun (f, arg_sorts, retsort, body, c) ->
            let uu___ = name_macro_binders arg_sorts in
            (match uu___ with
             | (names, binders1) ->
                 let body1 =
                   let uu___1 =
                     FStarC_Compiler_List.map (fun x -> mkFreeV x norng)
                       names in
                   inst uu___1 body in
                 let uu___1 = caption_to_string print_captions c in
                 let uu___2 = strSort retsort in
                 let uu___3 =
                   let uu___4 = escape f in
                   termToSmt print_captions uu___4 body1 in
                 FStarC_Compiler_Util.format5
                   "%s(define-fun %s (%s) %s\n %s)" uu___1 f
                   (FStarC_Compiler_String.concat " " binders1) uu___2 uu___3)
        | Assume a ->
            let fact_ids_to_string ids =
              FStarC_Compiler_List.map
                (fun uu___ ->
                   match uu___ with
                   | Name n ->
                       let uu___1 = FStarC_Ident.string_of_lid n in
                       Prims.strcat "Name " uu___1
                   | Namespace ns ->
                       let uu___1 = FStarC_Ident.string_of_lid ns in
                       Prims.strcat "Namespace " uu___1
                   | Tag t -> Prims.strcat "Tag " t) ids in
            let fids =
              if print_captions
              then
                let uu___ =
                  let uu___1 = fact_ids_to_string a.assumption_fact_ids in
                  FStarC_Compiler_String.concat "; " uu___1 in
                FStarC_Compiler_Util.format1 ";;; Fact-ids: %s\n" uu___
              else "" in
            let n = a.assumption_name in
            let uu___ = caption_to_string print_captions a.assumption_caption in
            let uu___1 = termToSmt print_captions n a.assumption_term in
            FStarC_Compiler_Util.format4 "%s%s(assert (! %s\n:named %s))"
              uu___ fids uu___1 n
        | Eval t ->
            let uu___ = termToSmt print_captions "eval" t in
            FStarC_Compiler_Util.format1 "(eval %s)" uu___
        | Echo s -> FStarC_Compiler_Util.format1 "(echo \"%s\")" s
        | RetainAssumptions uu___ -> ""
        | CheckSat ->
            "(echo \"<result>\")\n(check-sat)\n(echo \"</result>\")"
        | GetUnsatCore ->
            "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
        | Push n ->
            let uu___ =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
            FStarC_Compiler_Util.format1 "(push) ;; push{%s" uu___
        | Pop n ->
            let uu___ =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
            FStarC_Compiler_Util.format1 "(pop) ;; %s}pop" uu___
        | SetOption (s, v) ->
            FStarC_Compiler_Util.format2 "(set-option :%s %s)" s v
        | GetStatistics ->
            "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
        | GetReasonUnknown ->
            "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and (declToSmt : Prims.string -> decl -> Prims.string) =
  fun z3options ->
    fun decl1 ->
      let uu___ = FStarC_Options.keep_query_captions () in
      declToSmt' uu___ z3options decl1
and (mkPrelude : Prims.string -> Prims.string) =
  fun z3options ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-sort Dummy_sort)\n(declare-fun Dummy_value () Dummy_sort)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n(declare-fun IsTotFun (Term) Bool)\n\n                ;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Prec (Term Term) Bool)\n(assert (forall ((x Term) (y Term) (z Term))\n(! (implies (and (Prec x y) (Prec y z))\n(Prec x z))\n                                   :pattern ((Prec x z) (Prec x y)))))\n(assert (forall ((x Term) (y Term))\n(implies (Prec x y)\n(not (Prec y x)))))\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(declare-fun Prims.precedes (Term Term Term Term) Term)\n(declare-fun Range_const (Int) Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(declare-fun __uu__PartialApp () Term)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))\n(declare-fun _rmul (Real Real) Real)\n(declare-fun _rdiv (Real Real) Real)\n(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))\n(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))\n(define-fun Unreachable () Bool false)" in
    let as_constr uu___ =
      match uu___ with
      | (name, fields, sort1, id, _injective) ->
          let uu___1 =
            FStarC_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (field_name, field_sort, field_projectible) ->
                     { field_name; field_sort; field_projectible }) fields in
          {
            constr_name = name;
            constr_fields = uu___1;
            constr_sort = sort1;
            constr_id = (FStar_Pervasives_Native.Some id);
            constr_base = false
          } in
    let constrs =
      FStarC_Compiler_List.map as_constr
        [("FString_const", [("FString_const_proj_0", Int_sort, true)],
           String_sort, Prims.int_zero, true);
        ("Tm_type", [], Term_sort, (Prims.of_int (2)), true);
        ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
          (Prims.of_int (3)), false);
        ("Tm_unit", [], Term_sort, (Prims.of_int (6)), true);
        ((FStar_Pervasives_Native.fst boxIntFun),
          [((FStar_Pervasives_Native.snd boxIntFun), Int_sort, true)],
          Term_sort, (Prims.of_int (7)), true);
        ((FStar_Pervasives_Native.fst boxBoolFun),
          [((FStar_Pervasives_Native.snd boxBoolFun), Bool_sort, true)],
          Term_sort, (Prims.of_int (8)), true);
        ((FStar_Pervasives_Native.fst boxStringFun),
          [((FStar_Pervasives_Native.snd boxStringFun), String_sort, true)],
          Term_sort, (Prims.of_int (9)), true);
        ((FStar_Pervasives_Native.fst boxRealFun),
          [((FStar_Pervasives_Native.snd boxRealFun), (Sort "Real"), true)],
          Term_sort, (Prims.of_int (10)), true)] in
    let bcons =
      let uu___ =
        let uu___1 =
          FStarC_Compiler_List.collect (constructor_to_decl norng) constrs in
        FStarC_Compiler_List.map (declToSmt z3options) uu___1 in
      FStarC_Compiler_String.concat "\n" uu___ in
    let precedes_partial_app =
      "\n(declare-fun Prims.precedes@tok () Term)\n(assert\n(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))\n(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok\n@x0)\n@x1)\n@x2)\n@x3)\n(Prims.precedes @x0 @x1 @x2 @x3))\n\n:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok\n@x0)\n@x1)\n@x2)\n@x3)))))\n" in
    let lex_ordering =
      "\n(declare-fun Prims.lex_t () Term)\n(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))\n(! (iff (Valid (Prims.precedes t1 t2 e1 e2))\n(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))\n:pattern (Prims.precedes t1 t2 e1 e2))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) \n(Prec t1 t2))\n:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))\n" in
    let valid_intro =
      "(assert (forall ((e Term) (t Term))\n(! (implies (HasType e t)\n(Valid t))\n:pattern ((HasType e t)\n(Valid t))\n:qid __prelude_valid_intro)))\n" in
    let valid_elim =
      "(assert (forall ((t Term))\n(! (implies (Valid t)\n(exists ((e Term)) (HasType e t)))\n:pattern ((Valid t))\n:qid __prelude_valid_elim)))\n" in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Options.smtencoding_valid_intro () in
              if uu___5 then valid_intro else "" in
            let uu___5 =
              let uu___6 = FStarC_Options.smtencoding_valid_elim () in
              if uu___6 then valid_elim else "" in
            Prims.strcat uu___4 uu___5 in
          Prims.strcat lex_ordering uu___3 in
        Prims.strcat precedes_partial_app uu___2 in
      Prims.strcat bcons uu___1 in
    Prims.strcat basic uu___
let (declsToSmt : Prims.string -> decl Prims.list -> Prims.string) =
  fun z3options ->
    fun decls ->
      let uu___ = FStarC_Compiler_List.map (declToSmt z3options) decls in
      FStarC_Compiler_String.concat "\n" uu___
let (declToSmt_no_caps : Prims.string -> decl -> Prims.string) =
  fun z3options -> fun decl1 -> declToSmt' false z3options decl1
let (mkBvConstructor :
  Prims.int -> (decl Prims.list * Prims.string * Prims.string)) =
  fun sz ->
    let constr =
      let uu___ =
        let uu___1 = boxBitVecFun sz in FStar_Pervasives_Native.fst uu___1 in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = boxBitVecFun sz in
            FStar_Pervasives_Native.snd uu___4 in
          {
            field_name = uu___3;
            field_sort = (BitVec_sort sz);
            field_projectible = true
          } in
        [uu___2] in
      {
        constr_name = uu___;
        constr_fields = uu___1;
        constr_sort = Term_sort;
        constr_id = FStar_Pervasives_Native.None;
        constr_base = false
      } in
    let uu___ = constructor_to_decl norng constr in
    (uu___, (constr.constr_name), (discriminator_name constr))
let (__range_c : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (mk_Range_const : unit -> term) =
  fun uu___ ->
    let i = FStarC_Compiler_Effect.op_Bang __range_c in
    (let uu___2 =
       let uu___3 = FStarC_Compiler_Effect.op_Bang __range_c in
       uu___3 + Prims.int_one in
     FStarC_Compiler_Effect.op_Colon_Equals __range_c uu___2);
    (let uu___2 =
       let uu___3 = let uu___4 = mkInteger' i norng in [uu___4] in
       ("Range_const", uu___3) in
     mkApp uu___2 norng)
let (mk_Term_type : term) = mkApp ("Tm_type", []) norng
let (mk_Term_app : term -> term -> FStarC_Compiler_Range_Type.range -> term)
  = fun t1 -> fun t2 -> fun r -> mkApp ("Tm_app", [t1; t2]) r
let (mk_Term_uvar : Prims.int -> FStarC_Compiler_Range_Type.range -> term) =
  fun i ->
    fun r ->
      let uu___ =
        let uu___1 = let uu___2 = mkInteger' i norng in [uu___2] in
        ("Tm_uvar", uu___1) in
      mkApp uu___ r
let (mk_Term_unit : term) = mkApp ("Tm_unit", []) norng
let (elim_box : Prims.bool -> Prims.string -> Prims.string -> term -> term) =
  fun cond ->
    fun u ->
      fun v ->
        fun t ->
          match t.tm with
          | App (Var v', t1::[]) when (v = v') && cond -> t1
          | uu___ -> mkApp (u, [t]) t.rng
let (maybe_elim_box : Prims.string -> Prims.string -> term -> term) =
  fun u ->
    fun v ->
      fun t ->
        let uu___ = FStarC_Options.smtencoding_elim_box () in
        elim_box uu___ u v t
let (boxInt : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxIntFun)
      (FStar_Pervasives_Native.snd boxIntFun) t
let (unboxInt : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxIntFun)
      (FStar_Pervasives_Native.fst boxIntFun) t
let (boxBool : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxBoolFun)
      (FStar_Pervasives_Native.snd boxBoolFun) t
let (unboxBool : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxBoolFun)
      (FStar_Pervasives_Native.fst boxBoolFun) t
let (boxString : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxStringFun)
      (FStar_Pervasives_Native.snd boxStringFun) t
let (unboxString : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxStringFun)
      (FStar_Pervasives_Native.fst boxStringFun) t
let (boxReal : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.fst boxRealFun)
      (FStar_Pervasives_Native.snd boxRealFun) t
let (unboxReal : term -> term) =
  fun t ->
    maybe_elim_box (FStar_Pervasives_Native.snd boxRealFun)
      (FStar_Pervasives_Native.fst boxRealFun) t
let (boxBitVec : Prims.int -> term -> term) =
  fun sz ->
    fun t ->
      let uu___ =
        let uu___1 = boxBitVecFun sz in FStar_Pervasives_Native.fst uu___1 in
      let uu___1 =
        let uu___2 = boxBitVecFun sz in FStar_Pervasives_Native.snd uu___2 in
      elim_box true uu___ uu___1 t
let (unboxBitVec : Prims.int -> term -> term) =
  fun sz ->
    fun t ->
      let uu___ =
        let uu___1 = boxBitVecFun sz in FStar_Pervasives_Native.snd uu___1 in
      let uu___1 =
        let uu___2 = boxBitVecFun sz in FStar_Pervasives_Native.fst uu___2 in
      elim_box true uu___ uu___1 t
let (boxTerm : sort -> term -> term) =
  fun sort1 ->
    fun t ->
      match sort1 with
      | Int_sort -> boxInt t
      | Bool_sort -> boxBool t
      | String_sort -> boxString t
      | BitVec_sort sz -> boxBitVec sz t
      | Sort "Real" -> boxReal t
      | uu___ -> FStarC_Compiler_Effect.raise FStarC_Compiler_Util.Impos
let (unboxTerm : sort -> term -> term) =
  fun sort1 ->
    fun t ->
      match sort1 with
      | Int_sort -> unboxInt t
      | Bool_sort -> unboxBool t
      | String_sort -> unboxString t
      | BitVec_sort sz -> unboxBitVec sz t
      | Sort "Real" -> unboxReal t
      | uu___ -> FStarC_Compiler_Effect.raise FStarC_Compiler_Util.Impos
let (getBoxedInteger : term -> Prims.int FStar_Pervasives_Native.option) =
  fun t ->
    match t.tm with
    | App (Var s, t2::[]) when s = (FStar_Pervasives_Native.fst boxIntFun) ->
        (match t2.tm with
         | Integer n ->
             let uu___ = FStarC_Compiler_Util.int_of_string n in
             FStar_Pervasives_Native.Some uu___
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (mk_PreType : term -> term) = fun t -> mkApp ("PreType", [t]) t.rng
let (mk_Valid : term -> term) =
  fun t ->
    match t.tm with
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Equality", uu___::t1::t2::[]);
           freevars = uu___1; rng = uu___2;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_disEquality", uu___::t1::t2::[]);
           freevars = uu___1; rng = uu___2;_}::[])
        -> let uu___3 = mkEq (t1, t2) norng in mkNot uu___3 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThanOrEqual", t1::t2::[]);
           freevars = uu___; rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxInt t1 in
          let uu___4 = unboxInt t2 in (uu___3, uu___4) in
        mkLTE uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_LessThan", t1::t2::[]); freevars = uu___;
           rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxInt t1 in
          let uu___4 = unboxInt t2 in (uu___3, uu___4) in
        mkLT uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThanOrEqual", t1::t2::[]);
           freevars = uu___; rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxInt t1 in
          let uu___4 = unboxInt t2 in (uu___3, uu___4) in
        mkGTE uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_GreaterThan", t1::t2::[]);
           freevars = uu___; rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxInt t1 in
          let uu___4 = unboxInt t2 in (uu___3, uu___4) in
        mkGT uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_AmpAmp", t1::t2::[]); freevars = uu___;
           rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxBool t1 in
          let uu___4 = unboxBool t2 in (uu___3, uu___4) in
        mkAnd uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_BarBar", t1::t2::[]); freevars = uu___;
           rng = uu___1;_}::[])
        ->
        let uu___2 =
          let uu___3 = unboxBool t1 in
          let uu___4 = unboxBool t2 in (uu___3, uu___4) in
        mkOr uu___2 t.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "Prims.op_Negation", t1::[]); freevars = uu___;
           rng = uu___1;_}::[])
        -> let uu___2 = unboxBool t1 in mkNot uu___2 t1.rng
    | App
        (Var "Prims.b2t",
         { tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]); freevars = uu___;
           rng = uu___1;_}::[])
        when
        let uu___2 = getBoxedInteger t0 in
        FStarC_Compiler_Util.is_some uu___2 ->
        let sz =
          let uu___2 = getBoxedInteger t0 in
          match uu___2 with
          | FStar_Pervasives_Native.Some sz1 -> sz1
          | uu___3 -> failwith "impossible" in
        let uu___2 =
          let uu___3 = unboxBitVec sz t1 in
          let uu___4 = unboxBitVec sz t2 in (uu___3, uu___4) in
        mkBvUlt uu___2 t.rng
    | App
        (Var "Prims.equals",
         uu___::{ tm = App (Var "FStar.BV.bvult", t0::t1::t2::[]);
                  freevars = uu___1; rng = uu___2;_}::uu___3::[])
        when
        let uu___4 = getBoxedInteger t0 in
        FStarC_Compiler_Util.is_some uu___4 ->
        let sz =
          let uu___4 = getBoxedInteger t0 in
          match uu___4 with
          | FStar_Pervasives_Native.Some sz1 -> sz1
          | uu___5 -> failwith "impossible" in
        let uu___4 =
          let uu___5 = unboxBitVec sz t1 in
          let uu___6 = unboxBitVec sz t2 in (uu___5, uu___6) in
        mkBvUlt uu___4 t.rng
    | App (Var "Prims.b2t", t1::[]) ->
        let uu___ = unboxBool t1 in
        { tm = (uu___.tm); freevars = (uu___.freevars); rng = (t.rng) }
    | uu___ -> mkApp ("Valid", [t]) t.rng
let (mk_unit_type : term) = mkApp ("Prims.unit", []) norng
let (mk_subtype_of_unit : term -> term) =
  fun v -> mkApp ("Prims.subtype_of", [v; mk_unit_type]) v.rng
let (mk_HasType : term -> term -> term) =
  fun v -> fun t -> mkApp ("HasType", [v; t]) t.rng
let (mk_HasTypeZ : term -> term -> term) =
  fun v -> fun t -> mkApp ("HasTypeZ", [v; t]) t.rng
let (mk_IsTotFun : term -> term) = fun t -> mkApp ("IsTotFun", [t]) t.rng
let (mk_HasTypeFuel : term -> term -> term -> term) =
  fun f ->
    fun v ->
      fun t ->
        let uu___ = FStarC_Options.unthrottle_inductives () in
        if uu___
        then mk_HasType v t
        else mkApp ("HasTypeFuel", [f; v; t]) t.rng
let (mk_HasTypeWithFuel :
  term FStar_Pervasives_Native.option -> term -> term -> term) =
  fun f ->
    fun v ->
      fun t ->
        match f with
        | FStar_Pervasives_Native.None -> mk_HasType v t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v t
let (mk_NoHoist : term -> term -> term) =
  fun dummy -> fun b -> mkApp ("NoHoist", [dummy; b]) b.rng
let (mk_tester : Prims.string -> term -> term) =
  fun n -> fun t -> mkApp ((Prims.strcat "is-" n), [t]) t.rng
let (mk_ApplyTF : term -> term -> term) =
  fun t -> fun t' -> mkApp ("ApplyTF", [t; t']) t.rng
let (mk_ApplyTT : term -> term -> FStarC_Compiler_Range_Type.range -> term) =
  fun t -> fun t' -> fun r -> mkApp ("ApplyTT", [t; t']) r
let (kick_partial_app : term -> term) =
  fun t ->
    let uu___ =
      let uu___1 = mkApp ("__uu__PartialApp", []) t.rng in
      mk_ApplyTT uu___1 t t.rng in
    mk_Valid uu___
let (mk_String_const :
  Prims.string -> FStarC_Compiler_Range_Type.range -> term) =
  fun s ->
    fun r ->
      let uu___ =
        let uu___1 = let uu___2 = mk (String s) r in [uu___2] in
        ("FString_const", uu___1) in
      mkApp uu___ r
let (mk_Precedes :
  term -> term -> term -> term -> FStarC_Compiler_Range_Type.range -> term) =
  fun x1 ->
    fun x2 ->
      fun x3 ->
        fun x4 ->
          fun r ->
            let uu___ = mkApp ("Prims.precedes", [x1; x2; x3; x4]) r in
            mk_Valid uu___
let rec (n_fuel : Prims.int -> term) =
  fun n ->
    if n = Prims.int_zero
    then mkApp ("ZFuel", []) norng
    else
      (let uu___1 =
         let uu___2 = let uu___3 = n_fuel (n - Prims.int_one) in [uu___3] in
         ("SFuel", uu___2) in
       mkApp uu___1 norng)
let (mk_and_l : term Prims.list -> FStarC_Compiler_Range_Type.range -> term)
  =
  fun l ->
    fun r ->
      let uu___ = mkTrue r in
      FStarC_Compiler_List.fold_right (fun p1 -> fun p2 -> mkAnd (p1, p2) r)
        l uu___
let (mk_or_l : term Prims.list -> FStarC_Compiler_Range_Type.range -> term) =
  fun l ->
    fun r ->
      let uu___ = mkFalse r in
      FStarC_Compiler_List.fold_right (fun p1 -> fun p2 -> mkOr (p1, p2) r) l
        uu___
let (mk_haseq : term -> term) =
  fun t -> let uu___ = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu___
let (dummy_sort : sort) = Sort "Dummy_sort"
let (showable_smt_term : term FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = print_smt_term }
let (showable_decl : decl FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = (declToSmt_no_caps "") }
let rec (names_of_decl : decl -> Prims.string Prims.list) =
  fun d ->
    match d with
    | Assume a -> [a.assumption_name]
    | Module (uu___, ds) -> FStarC_Compiler_List.collect names_of_decl ds
    | uu___ -> []
let (decl_to_string_short : decl -> Prims.string) =
  fun d ->
    match d with
    | DefPrelude -> "prelude"
    | DeclFun (s, uu___, uu___1, uu___2) -> Prims.strcat "DeclFun " s
    | DefineFun (s, uu___, uu___1, uu___2, uu___3) ->
        Prims.strcat "DefineFun " s
    | Assume a -> Prims.strcat "Assumption " a.assumption_name
    | Caption s -> Prims.strcat "Caption " s
    | Module (s, uu___) -> Prims.strcat "Module " s
    | Eval uu___ -> "Eval"
    | Echo s -> Prims.strcat "Echo " s
    | RetainAssumptions uu___ -> "RetainAssumptions"
    | Push n ->
        let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
        FStarC_Compiler_Util.format1 "push %s" uu___
    | Pop n ->
        let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
        FStarC_Compiler_Util.format1 "pop %s" uu___
    | CheckSat -> "check-sat"
    | GetUnsatCore -> "get-unsat-core"
    | SetOption (s, v) ->
        Prims.strcat "SetOption " (Prims.strcat s (Prims.strcat " " v))
    | GetStatistics -> "get-statistics"
    | GetReasonUnknown -> "get-reason-unknown"