open Prims
let old_mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let _0_169 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "Tuple%s" _0_169  in
      let _0_170 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_170 r
  
let old_mk_tuple_data_lid :
  Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let _0_171 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "MkTuple%s" _0_171  in
      let _0_172 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_172 r
  
let old_mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n  ->
    fun r  ->
      let t =
        let _0_173 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "DTuple%s" _0_173  in
      let _0_174 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_174 r
  
let old_mk_dtuple_data_lid :
  Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let _0_175 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "MkDTuple%s" _0_175  in
      let _0_176 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_176 r
  
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let uu___is_Un : level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____32 -> false 
let uu___is_Expr : level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____36 -> false 
let uu___is_Type_level : level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____40 -> false
  
let uu___is_Kind : level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____44 -> false 
let uu___is_Formula : level -> Prims.bool =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____48 -> false
  
type imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | Nothing 
let uu___is_FsTypApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____52 -> false
  
let uu___is_Hash : imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____56 -> false 
let uu___is_UnivApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____60 -> false
  
let uu___is_Nothing : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____64 -> false
  
type arg_qualifier =
  | Implicit 
  | Equality 
let uu___is_Implicit : arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____68 -> false
  
let uu___is_Equality : arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____72 -> false
  
type aqual = arg_qualifier Prims.option
type let_qualifier =
  | NoLetQualifier 
  | Rec 
  | Mutable 
let uu___is_NoLetQualifier : let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____77 -> false
  
let uu___is_Rec : let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____81 -> false 
let uu___is_Mutable : let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____85 -> false
  
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (Prims.string * term Prims.list) 
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid * FStar_Ident.ident) 
  | Construct of (FStar_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | App of (term * term * imp) 
  | Let of (let_qualifier * (pattern * term) Prims.list * term) 
  | LetOpen of (FStar_Ident.lid * term) 
  | Seq of (term * term) 
  | If of (term * term * term) 
  | Match of (term * (pattern * term Prims.option * term) Prims.list) 
  | TryWith of (term * (pattern * term Prims.option * term) Prims.list) 
  | Ascribed of (term * term) 
  | Record of (term Prims.option * (FStar_Ident.lid * term) Prims.list) 
  | Project of (term * FStar_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of (binder Prims.list * term) 
  | QForall of (binder Prims.list * term Prims.list Prims.list * term) 
  | QExists of (binder Prims.list * term Prims.list Prims.list * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStar_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string Prims.option) 
  | Ensures of (term * Prims.string Prims.option) 
  | Labeled of (term * Prims.string * Prims.bool) 
  | Assign of (FStar_Ident.ident * term) 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident * term) 
  | TAnnotated of (FStar_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStar_Range.range ;
  blevel: level ;
  aqual: aqual }
and pattern' =
  | PatWild 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStar_Ident.ident * arg_qualifier Prims.option) 
  | PatName of FStar_Ident.lid 
  | PatTvar of (FStar_Ident.ident * arg_qualifier Prims.option) 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStar_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * term) 
  | PatOr of pattern Prims.list 
  | PatOp of Prims.string 
and pattern = {
  pat: pattern' ;
  prange: FStar_Range.range }
let uu___is_Wild : term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____370 -> false 
let uu___is_Const : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____375 -> false
  
let __proj__Const__item___0 : term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0 
let uu___is_Op : term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____390 -> false 
let __proj__Op__item___0 : term' -> (Prims.string * term Prims.list) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let uu___is_Tvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____411 -> false
  
let __proj__Tvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let uu___is_Uvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____423 -> false
  
let __proj__Uvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let uu___is_Var : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____435 -> false
  
let __proj__Var__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0 
let uu___is_Name : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____447 -> false
  
let __proj__Name__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Projector : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____461 -> false
  
let __proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let uu___is_Construct : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____484 -> false
  
let __proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let uu___is_Abs : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____514 -> false
  
let __proj__Abs__item___0 : term' -> (pattern Prims.list * term) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____538 -> false
  
let __proj__App__item___0 : term' -> (term * term * imp) =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____565 -> false
  
let __proj__Let__item___0 :
  term' -> (let_qualifier * (pattern * term) Prims.list * term) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_LetOpen : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____597 -> false
  
let __proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let uu___is_Seq : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____617 -> false
  
let __proj__Seq__item___0 : term' -> (term * term) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let uu___is_If : term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____638 -> false 
let __proj__If__item___0 : term' -> (term * term * term) =
  fun projectee  -> match projectee with | If _0 -> _0 
let uu___is_Match : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____666 -> false
  
let __proj__Match__item___0 :
  term' -> (term * (pattern * term Prims.option * term) Prims.list) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_TryWith : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____706 -> false
  
let __proj__TryWith__item___0 :
  term' -> (term * (pattern * term Prims.option * term) Prims.list) =
  fun projectee  -> match projectee with | TryWith _0 -> _0 
let uu___is_Ascribed : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____741 -> false
  
let __proj__Ascribed__item___0 : term' -> (term * term) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let uu___is_Record : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____765 -> false
  
let __proj__Record__item___0 :
  term' -> (term Prims.option * (FStar_Ident.lid * term) Prims.list) =
  fun projectee  -> match projectee with | Record _0 -> _0 
let uu___is_Project : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____797 -> false
  
let __proj__Project__item___0 : term' -> (term * FStar_Ident.lid) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let uu___is_Product : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____818 -> false
  
let __proj__Product__item___0 : term' -> (binder Prims.list * term) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let uu___is_Sum : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____842 -> false
  
let __proj__Sum__item___0 : term' -> (binder Prims.list * term) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let uu___is_QForall : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____869 -> false
  
let __proj__QForall__item___0 :
  term' -> (binder Prims.list * term Prims.list Prims.list * term) =
  fun projectee  -> match projectee with | QForall _0 -> _0 
let uu___is_QExists : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____905 -> false
  
let __proj__QExists__item___0 :
  term' -> (binder Prims.list * term Prims.list Prims.list * term) =
  fun projectee  -> match projectee with | QExists _0 -> _0 
let uu___is_Refine : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____937 -> false
  
let __proj__Refine__item___0 : term' -> (binder * term) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let uu___is_NamedTyp : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____957 -> false
  
let __proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let uu___is_Paren : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____975 -> false
  
let __proj__Paren__item___0 : term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let uu___is_Requires : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____990 -> false
  
let __proj__Requires__item___0 : term' -> (term * Prims.string Prims.option)
  = fun projectee  -> match projectee with | Requires _0 -> _0 
let uu___is_Ensures : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1014 -> false
  
let __proj__Ensures__item___0 : term' -> (term * Prims.string Prims.option) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1038 -> false
  
let __proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_Assign : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1061 -> false
  
let __proj__Assign__item___0 : term' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | Assign _0 -> _0 
let uu___is_Discrim : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1079 -> false
  
let __proj__Discrim__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let uu___is_Attributes : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1092 -> false
  
let __proj__Attributes__item___0 : term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let uu___is_Variable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1119 -> false
  
let __proj__Variable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let uu___is_TVariable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1131 -> false
  
let __proj__TVariable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let uu___is_Annotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1145 -> false
  
let __proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let uu___is_TAnnotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1165 -> false
  
let __proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let uu___is_NoName : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1183 -> false
  
let __proj__NoName__item___0 : binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let uu___is_PatWild : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1210 -> false
  
let uu___is_PatConst : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1215 -> false
  
let __proj__PatConst__item___0 : pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let uu___is_PatApp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1230 -> false
  
let __proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let uu___is_PatVar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1254 -> false
  
let __proj__PatVar__item___0 :
  pattern' -> (FStar_Ident.ident * arg_qualifier Prims.option) =
  fun projectee  -> match projectee with | PatVar _0 -> _0 
let uu___is_PatName : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1275 -> false
  
let __proj__PatName__item___0 : pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let uu___is_PatTvar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____1290 -> false
  
let __proj__PatTvar__item___0 :
  pattern' -> (FStar_Ident.ident * arg_qualifier Prims.option) =
  fun projectee  -> match projectee with | PatTvar _0 -> _0 
let uu___is_PatList : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____1312 -> false
  
let __proj__PatList__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let uu___is_PatTuple : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____1330 -> false
  
let __proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let uu___is_PatRecord : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____1354 -> false
  
let __proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let uu___is_PatAscribed : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____1377 -> false
  
let __proj__PatAscribed__item___0 : pattern' -> (pattern * term) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let uu___is_PatOr : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____1396 -> false
  
let __proj__PatOr__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let uu___is_PatOp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____1411 -> false
  
let __proj__PatOp__item___0 : pattern' -> Prims.string =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
type branch = (pattern * term Prims.option * term)
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string * (Prims.string * Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  Prims.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd Prims.option
  * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd Prims.option
  * (FStar_Ident.ident * term * fsdoc Prims.option) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd Prims.option
  * (FStar_Ident.ident * term Prims.option * fsdoc Prims.option * Prims.bool)
  Prims.list) 
let uu___is_TyconAbstract : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____1492 -> false
  
let __proj__TyconAbstract__item___0 :
  tycon -> (FStar_Ident.ident * binder Prims.list * knd Prims.option) =
  fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let uu___is_TyconAbbrev : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____1525 -> false
  
let __proj__TyconAbbrev__item___0 :
  tycon -> (FStar_Ident.ident * binder Prims.list * knd Prims.option * term)
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let uu___is_TyconRecord : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____1566 -> false
  
let __proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd Prims.option *
      (FStar_Ident.ident * term * fsdoc Prims.option) Prims.list)
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let uu___is_TyconVariant : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____1624 -> false
  
let __proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd Prims.option *
      (FStar_Ident.ident * term Prims.option * fsdoc Prims.option *
      Prims.bool) Prims.list)
  = fun projectee  -> match projectee with | TyconVariant _0 -> _0 
type qualifier =
  | Private 
  | Abstract 
  | Noeq 
  | Unopteq 
  | Assumption 
  | DefaultEffect 
  | TotalEffect 
  | Effect_qual 
  | New 
  | Inline 
  | Visible 
  | Unfold_for_unification_and_vcgen 
  | Inline_for_extraction 
  | Irreducible 
  | NoExtract 
  | Reifiable 
  | Reflectable 
  | Opaque 
  | Logic 
let uu___is_Private : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1674 -> false
  
let uu___is_Abstract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1678 -> false
  
let uu___is_Noeq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____1682 -> false
  
let uu___is_Unopteq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____1686 -> false
  
let uu___is_Assumption : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____1690 -> false
  
let uu___is_DefaultEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____1694 -> false
  
let uu___is_TotalEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____1698 -> false
  
let uu___is_Effect_qual : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____1702 -> false
  
let uu___is_New : qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____1706 -> false 
let uu___is_Inline : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____1710 -> false
  
let uu___is_Visible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____1714 -> false
  
let uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____1718 -> false
  
let uu___is_Inline_for_extraction : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____1722 -> false
  
let uu___is_Irreducible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____1726 -> false
  
let uu___is_NoExtract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1730 -> false
  
let uu___is_Reifiable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____1734 -> false
  
let uu___is_Reflectable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____1738 -> false
  
let uu___is_Opaque : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____1742 -> false
  
let uu___is_Logic : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____1746 -> false
  
type qualifiers = qualifier Prims.list
type attributes_ = term Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let uu___is_Qualifier : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____1763 -> false
  
let __proj__Qualifier__item___0 : decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let uu___is_DeclAttributes : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____1776 -> false
  
let __proj__DeclAttributes__item___0 : decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let uu___is_Doc : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____1791 -> false
  
let __proj__Doc__item___0 : decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let uu___is_NonReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____1814 -> false
  
let __proj__NonReifiableLift__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let uu___is_ReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____1828 -> false
  
let __proj__ReifiableLift__item___0 : lift_op -> (term * term) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let uu___is_LiftForFree : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____1846 -> false
  
let __proj__LiftForFree__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string Prims.option 
  | LightOff 
let uu___is_SetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____1886 -> false
  
let __proj__SetOptions__item___0 : pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let uu___is_ResetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____1899 -> false
  
let __proj__ResetOptions__item___0 : pragma -> Prims.string Prims.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let uu___is_LightOff : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____1913 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Main of term 
  | Tycon of (Prims.bool * (tycon * fsdoc Prims.option) Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term Prims.option) 
  | NewEffect of effect_decl 
  | NewEffectForFree of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc Prims.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list * decl Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let uu___is_TopLevelModule : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____2017 -> false
  
let __proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let uu___is_Open : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____2029 -> false
  
let __proj__Open__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0 
let uu___is_Include : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____2041 -> false
  
let __proj__Include__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0 
let uu___is_ModuleAbbrev : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____2055 -> false
  
let __proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let uu___is_TopLevelLet : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____2078 -> false
  
let __proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let uu___is_Main : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____2105 -> false
  
let __proj__Main__item___0 : decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0 
let uu___is_Tycon : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____2123 -> false
  
let __proj__Tycon__item___0 :
  decl' -> (Prims.bool * (tycon * fsdoc Prims.option) Prims.list) =
  fun projectee  -> match projectee with | Tycon _0 -> _0 
let uu___is_Val : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____2155 -> false
  
let __proj__Val__item___0 : decl' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let uu___is_Exception : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____2176 -> false
  
let __proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term Prims.option) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let uu___is_NewEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____2197 -> false
  
let __proj__NewEffect__item___0 : decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let uu___is_NewEffectForFree : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffectForFree _0 -> true | uu____2209 -> false
  
let __proj__NewEffectForFree__item___0 : decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffectForFree _0 -> _0 
let uu___is_SubEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____2221 -> false
  
let __proj__SubEffect__item___0 : decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let uu___is_Pragma : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____2233 -> false
  
let __proj__Pragma__item___0 : decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let uu___is_Fsdoc : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____2245 -> false
  
let __proj__Fsdoc__item___0 : decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let uu___is_Assume : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____2259 -> false
  
let __proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_DefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____2307 -> false
  
let __proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list * decl
      Prims.list)
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let uu___is_RedefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____2347 -> false
  
let __proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let uu___is_Module : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____2387 -> false
  
let __proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let uu___is_Interface : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____2412 -> false
  
let __proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool) =
  fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul Prims.list
type inputFragment = (file,decl Prims.list) FStar_Util.either
let check_id : FStar_Ident.ident -> Prims.unit =
  fun id  ->
    let first_char =
      FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1")
       in
    match (FStar_String.lowercase first_char) = first_char with
    | true  -> ()
    | uu____2440 ->
        Prims.raise
          (FStar_Errors.Error
             (let _0_177 =
                FStar_Util.format1
                  "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
                  id.FStar_Ident.idText
                 in
              (_0_177, (id.FStar_Ident.idRange))))
  
let at_most_one s r l =
  match l with
  | x::[] -> Some x
  | [] -> None
  | uu____2462 ->
      Prims.raise
        (FStar_Errors.Error
           (let _0_178 =
              FStar_Util.format1 "At most one %s is allowed on declarations"
                s
               in
            (_0_178, r)))
  
let mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____2481 =
            FStar_List.choose
              (fun uu___105_2478  ->
                 match uu___105_2478 with
                 | Doc d -> Some d
                 | uu____2481 -> None) decorations
             in
          at_most_one "fsdoc" r _0_179  in
        let attributes_ =
          let uu____2490 =
            FStar_List.choose
              (fun uu___105_2494  ->
                 match uu___105_2494 with
                 | DeclAttributes a -> Some a
                 | uu____2493 -> None) decorations
             in
          at_most_one "attribute set" r _0_180  in
        let attributes_ = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___106_2508  ->
               match uu___106_2508 with
               | Qualifier q -> Some q
               | uu____2503 -> None) decorations
           in
        { d; drange = r; doc; quals = qualifiers; attrs = attributes_ }
  
let mk_binder : binder' -> FStar_Range.range -> level -> aqual -> binder =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let mk_term : term' -> FStar_Range.range -> level -> term =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let mk_uminus : term -> FStar_Range.range -> level -> term =
  fun t  ->
    fun r  ->
      fun l  ->
        let t1 =
          match t.tm with
          | Const (FStar_Const.Const_int
              (s,Some (FStar_Const.Signed ,width))) ->
              Const
                (FStar_Const.Const_int
                   ((Prims.strcat "-" s), (Some (FStar_Const.Signed, width))))
          | uu____2547 -> Op ("-", [t])  in
        mk_term t r l
  
let mk_pattern : pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r } 
let un_curry_abs : pattern Prims.list -> term -> term' =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____2568 -> Abs (ps, body)
  
let mk_function :
  (pattern * term Prims.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Syntax_Syntax.next_id ()  in FStar_Ident.gen r1
           in
        let _0_185 =
          Abs
            (let _0_184 =
               let _0_183 =
                 Match
                   (let _0_182 =
                      let _0_181 = Var (FStar_Ident.lid_of_ids [x])  in
                      mk_term _0_181 r1 Expr  in
                    (_0_182, branches))
                  in
               mk_term _0_183 r2 Expr  in
             ([mk_pattern (PatVar (x, None)) r1], _0_184))
           in
        mk_term _0_185 r2 Expr
  
let un_function : pattern -> term -> (pattern * term) Prims.option =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____2636,Abs (pats,body)) ->
          Some ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____2621 -> None
  
let lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let _0_186 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path _0_186 r
  
let consPat : FStar_Range.range -> pattern -> pattern -> pattern' =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Syntax_Const.cons_lid) r), [hd; tl])
  
let consTerm : FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Syntax_Const.cons_lid, [(hd, Nothing); (tl, Nothing)])) r
          Expr
  
let lexConsTerm : FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Syntax_Const.lexcons_lid, [(hd, Nothing); (tl, Nothing)]))
          r Expr
  
let mkConsList : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Syntax_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl  -> consTerm r e tl) elts nil
  
let mkLexList : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Syntax_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl  -> lexConsTerm r e tl) elts
        nil
  
let ml_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Syntax_Const.effect_ML_lid) t.range Expr  in
    let t = mk_term (App (ml, t, Nothing)) t.range Expr  in t
  
let tot_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Syntax_Const.effect_Tot_lid) t.range Expr
       in
    let t = mk_term (App (ml, t, Nothing)) t.range Expr  in t
  
let mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2765 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____2773 ->
                 FStar_List.fold_left
                   (fun t  ->
                      fun uu____2749  ->
                        match uu____2749 with
                        | (a,imp) -> mk_term (App (t, a, imp)) r Un) t args)
  
let mkRefSet : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let uu____2790 =
        (FStar_Syntax_Const.tset_empty, FStar_Syntax_Const.tset_singleton,
          FStar_Syntax_Const.tset_union)
         in
      match uu____2762 with
      | (empty_lid,singleton_lid,union_lid) ->
          let empty =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr  in
          let ref_constr =
            mk_term
              (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.heap_ref r))
              r Expr
             in
          let singleton =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr
             in
          let union =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl  ->
                 let e = mkApp ref_constr [(e, Nothing)] r  in
                 let single_e = mkApp singleton [(e, Nothing)] r  in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
  
let mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2830 ->
            (match t.tm with
             | Name s ->
                 let _0_188 =
                   Construct
                     (let _0_187 =
                        FStar_List.map (fun a  -> (a, Nothing)) args  in
                      (s, _0_187))
                    in
                 mk_term _0_188 r Un
             | uu____2811 ->
                 FStar_List.fold_left
                   (fun t  -> fun a  -> mk_term (App (t, a, Nothing)) r Un) t
                   args)
  
let mkAdmitMagic : FStar_Range.range -> term =
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr  in
    let admit =
      let admit_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.admit_lid r)) r
          Expr
         in
      mkExplicitApp admit_name [unit_const] r  in
    let magic =
      let magic_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.magic_lid r)) r
          Expr
         in
      mkExplicitApp magic_name [unit_const] r  in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr  in admit_magic
  
let mkWildAdmitMagic r =
  let _0_189 = mkAdmitMagic r  in ((mk_pattern PatWild r), None, _0_189) 
let focusBranches branches r =
  let should_filter = FStar_Util.for_some Prims.fst branches  in
  match should_filter with
  | true  ->
      (FStar_Errors.warn r "Focusing on only some cases";
       (let focussed =
          let _0_190 = FStar_List.filter Prims.fst branches  in
          FStar_All.pipe_right _0_190 (FStar_List.map Prims.snd)  in
        let _0_192 = let _0_191 = mkWildAdmitMagic r  in [_0_191]  in
        FStar_List.append focussed _0_192))
  | uu____2937 -> FStar_All.pipe_right branches (FStar_List.map Prims.snd) 
let focusLetBindings lbs r =
  let should_filter = FStar_Util.for_some Prims.fst lbs  in
  match should_filter with
  | true  ->
      (FStar_Errors.warn r
         "Focusing on only some cases in this (mutually) recursive definition";
       FStar_List.map
         (fun uu____3006  ->
            match uu____3006 with
            | (f,lb) ->
                (match f with
                 | true  -> lb
                 | uu____3021 ->
                     let _0_193 = mkAdmitMagic r  in ((Prims.fst lb), _0_193)))
         lbs)
  | uu____3022 -> FStar_All.pipe_right lbs (FStar_List.map Prims.snd) 
let mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let _0_194 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t _0_194 r
  
let mkTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r  in
      let _0_195 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons) r Expr) _0_195 r
  
let mkDTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r  in
      let _0_196 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons) r Expr) _0_196 r
  
let mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool -> term Prims.option -> FStar_Range.range -> aqual -> binder
  =
  fun id  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id, t)) m Type_level implicit  in
              match refopt with
              | None  -> b
              | Some phi ->
                  (match should_bind_var with
                   | true  ->
                       mk_binder
                         (Annotated
                            (id, (mk_term (Refine (b, phi)) m Type_level))) m
                         Type_level implicit
                   | uu____3105 ->
                       let x = FStar_Ident.gen t.range  in
                       let b =
                         mk_binder (Annotated (x, t)) m Type_level implicit
                          in
                       mk_binder
                         (Annotated
                            (id, (mk_term (Refine (b, phi)) m Type_level))) m
                         Type_level implicit)
  
let mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term Prims.option ->
          FStar_Range.range -> FStar_Range.range -> pattern
  =
  fun pat  ->
    fun t  ->
      fun should_bind_pat  ->
        fun phi_opt  ->
          fun t_range  ->
            fun range  ->
              let t1 =
                match phi_opt with
                | None  -> t
                | Some phi ->
                    (match should_bind_pat with
                     | true  ->
                         (match pat.pat with
                          | PatVar (x,uu____3131) ->
                              mk_term
                                (Refine
                                   ((mk_binder (Annotated (x, t)) t_range
                                       Type_level None), phi)) range
                                Type_level
                          | uu____3134 ->
                              let x = FStar_Ident.gen t_range  in
                              let phi =
                                let x_var =
                                  let _0_197 =
                                    Var (FStar_Ident.lid_of_ids [x])  in
                                  mk_term _0_197 phi.range Formula  in
                                let pat_branch = (pat, None, phi)  in
                                let otherwise_branch =
                                  let _0_199 =
                                    let _0_198 =
                                      Name
                                        (FStar_Ident.lid_of_path ["False"]
                                           phi.range)
                                       in
                                    mk_term _0_198 phi.range Formula  in
                                  ((mk_pattern PatWild phi.range), None,
                                    _0_199)
                                   in
                                mk_term
                                  (Match
                                     (x_var, [pat_branch; otherwise_branch]))
                                  phi.range Formula
                                 in
                              mk_term
                                (Refine
                                   ((mk_binder (Annotated (x, t)) t_range
                                       Type_level None), phi)) range
                                Type_level)
                     | uu____3167 ->
                         let x = FStar_Ident.gen t.range  in
                         mk_term
                           (Refine
                              ((mk_binder (Annotated (x, t)) t_range
                                  Type_level None), phi)) range Type_level)
                 in
              mk_pattern (PatAscribed (pat, t)) range
  
let rec extract_named_refinement :
  term -> (FStar_Ident.ident * term * term Prims.option) Prims.option =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) -> Some (x, t, None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____3268; blevel = uu____3269;
           aqual = uu____3270;_},t')
        -> Some (x, t, (Some t'))
    | Paren t -> extract_named_refinement t
    | uu____3201 -> None
  
let rec as_mlist :
  modul Prims.list ->
    ((FStar_Ident.lid * decl) * decl Prims.list) ->
      decl Prims.list -> modul Prims.list
  =
  fun out  ->
    fun cur  ->
      fun ds  ->
        let uu____3231 = cur  in
        match uu____3231 with
        | ((m_name,m_decl),cur) ->
            (match ds with
             | [] ->
                 FStar_List.rev
                   ((Module (m_name, (m_decl :: (FStar_List.rev cur1)))) ::
                   out)
             | d::ds1 ->
                 (match d.d with
                  | TopLevelModule m' ->
                      as_mlist
                        ((Module (m_name, (m_decl :: (FStar_List.rev cur))))
                        :: out) ((m', d), []) ds
                  | uu____3256 ->
                      as_mlist out ((m_name, m_decl), (d :: cur)) ds))
  
let as_frag :
  Prims.bool ->
    FStar_Range.range ->
      decl ->
        decl Prims.list ->
          (modul Prims.list,decl Prims.list) FStar_Util.either
  =
  fun is_light  ->
    fun light_range  ->
      fun d  ->
        fun ds  ->
          match d.d with
          | TopLevelModule m ->
              let ds =
                match is_light with
                | true  ->
                    let _0_200 = mk_decl (Pragma LightOff) light_range []  in
                    _0_200 :: ds
                | uu____3290 -> ds  in
              let ms = as_mlist [] ((m, d), []) ds  in
              ((let uu____3297 = FStar_List.tl ms  in
                match uu____3297 with
                | (Module (m',uu____3300))::uu____3301 ->
                    let msg =
                      "Support for more than one module in a file is deprecated"
                       in
                    let _0_201 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid m')
                       in
                    FStar_Util.print2_warning "%s (Warning): %s\n" _0_201 msg
                | uu____3306 -> ());
               FStar_Util.Inl ms)
          | uu____3310 ->
              let ds = d :: ds  in
              (FStar_List.iter
                 (fun uu___107_3393  ->
                    match uu___107_3393 with
                    | { d = TopLevelModule uu____3394; drange = r;
                        doc = uu____3396; quals = uu____3397;
                        attrs = uu____3398;_} ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected module declaration", r))
                    | uu____3321 -> ()) ds;
               FStar_Util.Inr ds)
  
let compile_op : Prims.int -> Prims.string -> Prims.string =
  fun arity  ->
    fun s  ->
      let name_of_char uu___108_3412 =
        match uu___108_3412 with
        | '&' -> "Amp"
        | '@' -> "At"
        | '+' -> "Plus"
        | '-' when arity = (Prims.parse_int "1") -> "Minus"
        | '-' -> "Subtraction"
        | '/' -> "Slash"
        | '<' -> "Less"
        | '=' -> "Equals"
        | '>' -> "Greater"
        | '_' -> "Underscore"
        | '|' -> "Bar"
        | '!' -> "Bang"
        | '^' -> "Hat"
        | '%' -> "Percent"
        | '*' -> "Star"
        | '?' -> "Question"
        | ':' -> "Colon"
        | uu____3334 -> "UNKNOWN"  in
      match s with
      | ".[]<-" -> "op_String_Assignment"
      | ".()<-" -> "op_Array_Assignment"
      | ".[]" -> "op_String_Access"
      | ".()" -> "op_Array_Access"
      | uu____3335 ->
          let _0_204 =
            let _0_203 =
              let _0_202 = FStar_String.list_of_string s  in
              FStar_List.map name_of_char _0_202  in
            FStar_String.concat "_" _0_203  in
          Prims.strcat "op_" _0_204
  
let compile_op' : Prims.string -> Prims.string =
  fun s  -> compile_op (~- (Prims.parse_int "1")) s 
let string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string =
  fun uu____3346  ->
    match uu____3346 with
    | (comment,keywords) ->
        let uu____3444 =
          let uu____3445 =
            FStar_List.map
              (fun uu____3362  ->
                 match uu____3362 with
                 | (k,v) -> Prims.strcat k (Prims.strcat "->" v)) keywords
             in
          FStar_String.concat "," _0_205  in
        Prims.strcat comment _0_206
  
let string_of_let_qualifier : let_qualifier -> Prims.string =
  fun uu___110_3369  ->
    match uu___110_3369 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
  
let to_string_l sep f l =
  let _0_207 = FStar_List.map f l  in FStar_String.concat sep _0_207 
let imp_to_string : imp -> Prims.string =
  fun uu___111_3396  ->
    match uu___111_3396 with | Hash  -> "#" | uu____3397 -> ""
  
let rec term_to_string : term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____3408) ->
        let _0_208 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" _0_208
    | Ensures (t,uu____3412) ->
        let _0_209 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" _0_209
    | Labeled (t,l,uu____3417) ->
        let _0_210 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l _0_210
    | Const c -> FStar_Syntax_Print.const_to_string c
    | Op (s,xs) ->
        let _0_212 =
          let _0_211 =
            FStar_List.map (fun x  -> FStar_All.pipe_right x term_to_string)
              xs
             in
          FStar_String.concat ", " _0_211  in
        FStar_Util.format2 "%s(%s)" s _0_212
    | Tvar id|Uvar id -> id.FStar_Ident.idText
    | Var l|Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____3529 =
          to_string_l " "
            (fun uu____3532  ->
               match uu____3532 with
               | (a,imp) ->
                   let _0_213 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) _0_213) args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _0_214
    | Abs (pats,t) ->
        let _0_216 = to_string_l " " pat_to_string pats  in
        let _0_215 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" _0_216 _0_215
    | App (t1,t2,imp) ->
        let _0_218 = FStar_All.pipe_right t1 term_to_string  in
        let _0_217 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" _0_218 (imp_to_string imp) _0_217
    | Let (Rec ,lbs,body) ->
        let uu____3557 =
          to_string_l " and "
            (fun uu____3560  ->
               match uu____3560 with
               | (p,b) ->
                   let _0_220 = FStar_All.pipe_right p pat_to_string  in
                   let _0_219 = FStar_All.pipe_right b term_to_string  in
                   FStar_Util.format2 "%s=%s" _0_220 _0_219) lbs
           in
        let _0_221 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format2 "let rec %s in %s" _0_222 _0_221
    | Let (q,(pat,tm)::[],body) ->
        let _0_225 = FStar_All.pipe_right pat pat_to_string  in
        let _0_224 = FStar_All.pipe_right tm term_to_string  in
        let _0_223 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____3579 uu____3580 uu____3581
    | Seq (t1,t2) ->
        let _0_227 = FStar_All.pipe_right t1 term_to_string  in
        let _0_226 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" _0_227 _0_226
    | If (t1,t2,t3) ->
        let _0_230 = FStar_All.pipe_right t1 term_to_string  in
        let _0_229 = FStar_All.pipe_right t2 term_to_string  in
        let _0_228 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" _0_230 _0_229 _0_228
    | Match (t,branches) ->
        let _0_236 = FStar_All.pipe_right t term_to_string  in
        let _0_235 =
          to_string_l " | "
            (fun uu____3610  ->
               match uu____3610 with
               | (p,w,e) ->
                   let _0_234 = FStar_All.pipe_right p pat_to_string  in
                   let _0_233 =
                     match w with
                     | None  -> ""
                     | Some e ->
                         let _0_231 = term_to_string e  in
                         FStar_Util.format1 "when %s" _0_231
                      in
                   let _0_232 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" _0_234 _0_233 _0_232)
            branches
           in
        FStar_Util.format2 "match %s with %s" _0_236 _0_235
    | Ascribed (t1,t2) ->
        let _0_238 = FStar_All.pipe_right t1 term_to_string  in
        let _0_237 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" _0_238 _0_237
    | Record (Some e,fields) ->
        let _0_241 = FStar_All.pipe_right e term_to_string  in
        let _0_240 =
          to_string_l " "
            (fun uu____3519  ->
               match uu____3519 with
               | (l,e) ->
                   let _0_239 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str _0_239)
            fields
           in
        FStar_Util.format2 "{%s with %s}" _0_241 _0_240
    | Record (None ,fields) ->
        let uu____3664 =
          to_string_l " "
            (fun uu____3667  ->
               match uu____3667 with
               | (l,e) ->
                   let _0_242 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str _0_242)
            fields
           in
        FStar_Util.format1 "{%s}" _0_243
    | Project (e,l) ->
        let _0_244 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" _0_244 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let _0_246 = FStar_All.pipe_right b binder_to_string  in
        let _0_245 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" _0_246 _0_245
    | Product (b::[],t) when x.level = Kind ->
        let _0_248 = FStar_All.pipe_right b binder_to_string  in
        let _0_247 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" _0_248 _0_247
    | Sum (binders,t) ->
        let _0_251 =
          let _0_249 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string)
             in
          FStar_All.pipe_right _0_249 (FStar_String.concat " * ")  in
        let _0_250 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s * %s" _0_251 _0_250
    | QForall (bs,pats,t) ->
        let _0_254 = to_string_l " " binder_to_string bs  in
        let _0_253 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let _0_252 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" _0_254 _0_253 _0_252
    | QExists (bs,pats,t) ->
        let _0_257 = to_string_l " " binder_to_string bs  in
        let _0_256 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let _0_255 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" _0_257 _0_256 _0_255
    | Refine (b,t) ->
        let _0_259 = FStar_All.pipe_right b binder_to_string  in
        let _0_258 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" _0_259 _0_258
    | NamedTyp (x,t) ->
        let _0_260 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _0_260
    | Paren t ->
        let _0_261 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" _0_261
    | Product (bs,t) ->
        let _0_264 =
          let _0_262 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right _0_262 (FStar_String.concat ",")  in
        let _0_263 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" _0_264 _0_263
    | t -> "_"

and binder_to_string : binder -> Prims.string =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t)|Annotated (i,t) ->
          let _0_265 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _0_265
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let _0_266 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" _0_266 s

and aqual_to_string : aqual -> Prims.string =
  fun uu___112_3604  ->
    match uu___112_3604 with
    | Some (Equality ) -> "$"
    | Some (Implicit ) -> "#"
    | uu____3605 -> ""

and pat_to_string : pattern -> Prims.string =
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Syntax_Print.const_to_string c
    | PatApp (p,ps) ->
        let _0_268 = FStar_All.pipe_right p pat_to_string  in
        let _0_267 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" _0_268 _0_267
    | PatTvar (i,aq)|PatVar (i,aq) ->
        let _0_269 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" _0_269 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let _0_270 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" _0_270
    | PatTuple (l,false ) ->
        let _0_271 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" _0_271
    | PatTuple (l,true ) ->
        let _0_272 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" _0_272
    | PatRecord l ->
        let uu____3796 =
          to_string_l "; "
            (fun uu____3799  ->
               match uu____3799 with
               | (f,e) ->
                   let _0_273 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str _0_273) l
           in
        FStar_Util.format1 "{%s}" _0_274
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" op
    | PatAscribed (p,t) ->
        let _0_276 = FStar_All.pipe_right p pat_to_string  in
        let _0_275 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" _0_276 _0_275

let rec head_id_of_pat : pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____3650) ->
        let _0_277 = FStar_Ident.lid_of_ids [i]  in [_0_277]
    | PatApp (p,uu____3654) -> head_id_of_pat p
    | PatAscribed (p,uu____3658) -> head_id_of_pat p
    | uu____3659 -> []
  
let lids_of_let defs =
  FStar_All.pipe_right defs
    (FStar_List.collect
       (fun uu____3680  ->
          match uu____3680 with | (p,uu____3685) -> head_id_of_pat p))
  
let id_of_tycon : tycon -> Prims.string =
  fun uu___113_3688  ->
    match uu___113_3688 with
    | TyconAbstract (i,_,_)
      |TyconAbbrev (i,_,_,_)|TyconRecord (i,_,_,_)|TyconVariant (i,_,_,_) ->
        i.FStar_Ident.idText
  
let decl_to_string : decl -> Prims.string =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.strcat "module " l.FStar_Ident.str
    | Open l -> Prims.strcat "open " l.FStar_Ident.str
    | Include l -> Prims.strcat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____3729,pats) ->
        let _0_280 =
          let _0_279 =
            let _0_278 = lids_of_let pats  in
            FStar_All.pipe_right _0_278
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right _0_279 (FStar_String.concat ", ")  in
        Prims.strcat "let " _0_280
    | Main uu____3741 -> "main ..."
    | Assume (i,uu____3743) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____3744,tys) ->
        let _0_282 =
          let _0_281 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____3763  ->
                    match uu____3763 with | (x,uu____3768) -> id_of_tycon x))
             in
          FStar_All.pipe_right _0_281 (FStar_String.concat ", ")  in
        Prims.strcat "type " _0_282
    | Val (i,uu____3772) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____3774) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,_,_,_))|NewEffect (RedefineEffect (i,_,_))
        -> Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffectForFree (DefineEffect (i,_,_,_,_))|NewEffectForFree
      (RedefineEffect (i,_,_)) ->
        Prims.strcat "new_effect_for_free " i.FStar_Ident.idText
    | SubEffect uu____3799 -> "sub_effect"
    | Pragma uu____3800 -> "pragma"
    | Fsdoc uu____3801 -> "fsdoc"
  
let modul_to_string : modul -> Prims.string =
  fun m  ->
    match m with
    | Module (_,decls)|Interface (_,decls,_) ->
        let _0_283 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right _0_283 (FStar_String.concat "\n")
  
let error msg tm r =
  let tm = FStar_All.pipe_right tm term_to_string  in
  let tm =
    match (FStar_String.length tm) >= (Prims.parse_int "80") with
    | true  ->
        let _0_284 =
          FStar_Util.substring tm (Prims.parse_int "0")
            (Prims.parse_int "77")
           in
        Prims.strcat _0_284 "..."
    | uu____3838 -> tm  in
  Prims.raise
    (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm)), r))
  