open Prims
let old_mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let uu____8 = FStar_Util.string_of_int n in
        FStar_Util.format1 "Tuple%s" uu____8 in
      let uu____9 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____9 r
let old_mk_tuple_data_lid:
  Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let uu____17 = FStar_Util.string_of_int n in
        FStar_Util.format1 "MkTuple%s" uu____17 in
      let uu____18 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____18 r
let old_mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let uu____26 = FStar_Util.string_of_int n in
        FStar_Util.format1 "DTuple%s" uu____26 in
      let uu____27 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____27 r
let old_mk_dtuple_data_lid:
  Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let uu____35 = FStar_Util.string_of_int n in
        FStar_Util.format1 "MkDTuple%s" uu____35 in
      let uu____36 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____36 r
type level =
  | Un
  | Expr
  | Type_level
  | Kind
  | Formula
let uu___is_Un: level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____40 -> false
let uu___is_Expr: level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____44 -> false
let uu___is_Type_level: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____48 -> false
let uu___is_Kind: level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____52 -> false
let uu___is_Formula: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____56 -> false
type imp =
  | FsTypApp
  | Hash
  | UnivApp
  | Nothing
let uu___is_FsTypApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____60 -> false
let uu___is_Hash: imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____64 -> false
let uu___is_UnivApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____68 -> false
let uu___is_Nothing: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____72 -> false
type arg_qualifier =
  | Implicit
  | Equality
let uu___is_Implicit: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____76 -> false
let uu___is_Equality: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____80 -> false
type aqual = arg_qualifier Prims.option
type let_qualifier =
  | NoLetQualifier
  | Rec
  | Mutable
let uu___is_NoLetQualifier: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____85 -> false
let uu___is_Rec: let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____89 -> false
let uu___is_Mutable: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____93 -> false
type term' =
  | Wild
  | Const of FStar_Const.sconst
  | Op of (Prims.string* term Prims.list)
  | Tvar of FStar_Ident.ident
  | Uvar of FStar_Ident.ident
  | Var of FStar_Ident.lid
  | Name of FStar_Ident.lid
  | Projector of (FStar_Ident.lid* FStar_Ident.ident)
  | Construct of (FStar_Ident.lid* (term* imp) Prims.list)
  | Abs of (pattern Prims.list* term)
  | App of (term* term* imp)
  | Let of (let_qualifier* (pattern* term) Prims.list* term)
  | LetOpen of (FStar_Ident.lid* term)
  | Seq of (term* term)
  | If of (term* term* term)
  | Match of (term* (pattern* term Prims.option* term) Prims.list)
  | TryWith of (term* (pattern* term Prims.option* term) Prims.list)
  | Ascribed of (term* term)
  | Record of (term Prims.option* (FStar_Ident.lid* term) Prims.list)
  | Project of (term* FStar_Ident.lid)
  | Product of (binder Prims.list* term)
  | Sum of (binder Prims.list* term)
  | QForall of (binder Prims.list* term Prims.list Prims.list* term)
  | QExists of (binder Prims.list* term Prims.list Prims.list* term)
  | Refine of (binder* term)
  | NamedTyp of (FStar_Ident.ident* term)
  | Paren of term
  | Requires of (term* Prims.string Prims.option)
  | Ensures of (term* Prims.string Prims.option)
  | Labeled of (term* Prims.string* Prims.bool)
  | Assign of (FStar_Ident.ident* term)
  | Discrim of FStar_Ident.lid
  | Attributes of term Prims.list
and term = {
  tm: term';
  range: FStar_Range.range;
  level: level;}
and binder' =
  | Variable of FStar_Ident.ident
  | TVariable of FStar_Ident.ident
  | Annotated of (FStar_Ident.ident* term)
  | TAnnotated of (FStar_Ident.ident* term)
  | NoName of term
and binder =
  {
  b: binder';
  brange: FStar_Range.range;
  blevel: level;
  aqual: aqual;}
and pattern' =
  | PatWild
  | PatConst of FStar_Const.sconst
  | PatApp of (pattern* pattern Prims.list)
  | PatVar of (FStar_Ident.ident* arg_qualifier Prims.option)
  | PatName of FStar_Ident.lid
  | PatTvar of (FStar_Ident.ident* arg_qualifier Prims.option)
  | PatList of pattern Prims.list
  | PatTuple of (pattern Prims.list* Prims.bool)
  | PatRecord of (FStar_Ident.lid* pattern) Prims.list
  | PatAscribed of (pattern* term)
  | PatOr of pattern Prims.list
  | PatOp of Prims.string
and pattern = {
  pat: pattern';
  prange: FStar_Range.range;}
let uu___is_Wild: term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____378 -> false
let uu___is_Const: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____383 -> false
let __proj__Const__item___0: term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_Op: term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____398 -> false
let __proj__Op__item___0: term' -> (Prims.string* term Prims.list) =
  fun projectee  -> match projectee with | Op _0 -> _0
let uu___is_Tvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____419 -> false
let __proj__Tvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0
let uu___is_Uvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____431 -> false
let __proj__Uvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0
let uu___is_Var: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____443 -> false
let __proj__Var__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Name: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____455 -> false
let __proj__Name__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Projector: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____469 -> false
let __proj__Projector__item___0:
  term' -> (FStar_Ident.lid* FStar_Ident.ident) =
  fun projectee  -> match projectee with | Projector _0 -> _0
let uu___is_Construct: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____492 -> false
let __proj__Construct__item___0:
  term' -> (FStar_Ident.lid* (term* imp) Prims.list) =
  fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Abs: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____522 -> false
let __proj__Abs__item___0: term' -> (pattern Prims.list* term) =
  fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____546 -> false
let __proj__App__item___0: term' -> (term* term* imp) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____573 -> false
let __proj__Let__item___0:
  term' -> (let_qualifier* (pattern* term) Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_LetOpen: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____605 -> false
let __proj__LetOpen__item___0: term' -> (FStar_Ident.lid* term) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0
let uu___is_Seq: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____625 -> false
let __proj__Seq__item___0: term' -> (term* term) =
  fun projectee  -> match projectee with | Seq _0 -> _0
let uu___is_If: term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____646 -> false
let __proj__If__item___0: term' -> (term* term* term) =
  fun projectee  -> match projectee with | If _0 -> _0
let uu___is_Match: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____674 -> false
let __proj__Match__item___0:
  term' -> (term* (pattern* term Prims.option* term) Prims.list) =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_TryWith: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____714 -> false
let __proj__TryWith__item___0:
  term' -> (term* (pattern* term Prims.option* term) Prims.list) =
  fun projectee  -> match projectee with | TryWith _0 -> _0
let uu___is_Ascribed: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____749 -> false
let __proj__Ascribed__item___0: term' -> (term* term) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0
let uu___is_Record: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____773 -> false
let __proj__Record__item___0:
  term' -> (term Prims.option* (FStar_Ident.lid* term) Prims.list) =
  fun projectee  -> match projectee with | Record _0 -> _0
let uu___is_Project: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____805 -> false
let __proj__Project__item___0: term' -> (term* FStar_Ident.lid) =
  fun projectee  -> match projectee with | Project _0 -> _0
let uu___is_Product: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____826 -> false
let __proj__Product__item___0: term' -> (binder Prims.list* term) =
  fun projectee  -> match projectee with | Product _0 -> _0
let uu___is_Sum: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____850 -> false
let __proj__Sum__item___0: term' -> (binder Prims.list* term) =
  fun projectee  -> match projectee with | Sum _0 -> _0
let uu___is_QForall: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____877 -> false
let __proj__QForall__item___0:
  term' -> (binder Prims.list* term Prims.list Prims.list* term) =
  fun projectee  -> match projectee with | QForall _0 -> _0
let uu___is_QExists: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____913 -> false
let __proj__QExists__item___0:
  term' -> (binder Prims.list* term Prims.list Prims.list* term) =
  fun projectee  -> match projectee with | QExists _0 -> _0
let uu___is_Refine: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____945 -> false
let __proj__Refine__item___0: term' -> (binder* term) =
  fun projectee  -> match projectee with | Refine _0 -> _0
let uu___is_NamedTyp: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____965 -> false
let __proj__NamedTyp__item___0: term' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0
let uu___is_Paren: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____983 -> false
let __proj__Paren__item___0: term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0
let uu___is_Requires: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____998 -> false
let __proj__Requires__item___0: term' -> (term* Prims.string Prims.option) =
  fun projectee  -> match projectee with | Requires _0 -> _0
let uu___is_Ensures: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1022 -> false
let __proj__Ensures__item___0: term' -> (term* Prims.string Prims.option) =
  fun projectee  -> match projectee with | Ensures _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1046 -> false
let __proj__Labeled__item___0: term' -> (term* Prims.string* Prims.bool) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_Assign: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1069 -> false
let __proj__Assign__item___0: term' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Assign _0 -> _0
let uu___is_Discrim: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1087 -> false
let __proj__Discrim__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0
let uu___is_Attributes: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1100 -> false
let __proj__Attributes__item___0: term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0
let uu___is_Variable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1127 -> false
let __proj__Variable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0
let uu___is_TVariable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1139 -> false
let __proj__TVariable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0
let uu___is_Annotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1153 -> false
let __proj__Annotated__item___0: binder' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Annotated _0 -> _0
let uu___is_TAnnotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1173 -> false
let __proj__TAnnotated__item___0: binder' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0
let uu___is_NoName: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1191 -> false
let __proj__NoName__item___0: binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0
let uu___is_PatWild: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1218 -> false
let uu___is_PatConst: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1223 -> false
let __proj__PatConst__item___0: pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0
let uu___is_PatApp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1238 -> false
let __proj__PatApp__item___0: pattern' -> (pattern* pattern Prims.list) =
  fun projectee  -> match projectee with | PatApp _0 -> _0
let uu___is_PatVar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1262 -> false
let __proj__PatVar__item___0:
  pattern' -> (FStar_Ident.ident* arg_qualifier Prims.option) =
  fun projectee  -> match projectee with | PatVar _0 -> _0
let uu___is_PatName: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1283 -> false
let __proj__PatName__item___0: pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0
let uu___is_PatTvar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____1298 -> false
let __proj__PatTvar__item___0:
  pattern' -> (FStar_Ident.ident* arg_qualifier Prims.option) =
  fun projectee  -> match projectee with | PatTvar _0 -> _0
let uu___is_PatList: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____1320 -> false
let __proj__PatList__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0
let uu___is_PatTuple: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____1338 -> false
let __proj__PatTuple__item___0: pattern' -> (pattern Prims.list* Prims.bool)
  = fun projectee  -> match projectee with | PatTuple _0 -> _0
let uu___is_PatRecord: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____1362 -> false
let __proj__PatRecord__item___0:
  pattern' -> (FStar_Ident.lid* pattern) Prims.list =
  fun projectee  -> match projectee with | PatRecord _0 -> _0
let uu___is_PatAscribed: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____1385 -> false
let __proj__PatAscribed__item___0: pattern' -> (pattern* term) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0
let uu___is_PatOr: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____1404 -> false
let __proj__PatOr__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0
let uu___is_PatOp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____1419 -> false
let __proj__PatOp__item___0: pattern' -> Prims.string =
  fun projectee  -> match projectee with | PatOp _0 -> _0
type branch = (pattern* term Prims.option* term)
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string* (Prims.string* Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident* binder Prims.list* knd
  Prims.option)
  | TyconAbbrev of (FStar_Ident.ident* binder Prims.list* knd Prims.option*
  term)
  | TyconRecord of (FStar_Ident.ident* binder Prims.list* knd Prims.option*
  (FStar_Ident.ident* term* fsdoc Prims.option) Prims.list)
  | TyconVariant of (FStar_Ident.ident* binder Prims.list* knd Prims.option*
  (FStar_Ident.ident* term Prims.option* fsdoc Prims.option* Prims.bool)
  Prims.list)
let uu___is_TyconAbstract: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____1500 -> false
let __proj__TyconAbstract__item___0:
  tycon -> (FStar_Ident.ident* binder Prims.list* knd Prims.option) =
  fun projectee  -> match projectee with | TyconAbstract _0 -> _0
let uu___is_TyconAbbrev: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____1533 -> false
let __proj__TyconAbbrev__item___0:
  tycon -> (FStar_Ident.ident* binder Prims.list* knd Prims.option* term) =
  fun projectee  -> match projectee with | TyconAbbrev _0 -> _0
let uu___is_TyconRecord: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____1574 -> false
let __proj__TyconRecord__item___0:
  tycon ->
    (FStar_Ident.ident* binder Prims.list* knd Prims.option*
      (FStar_Ident.ident* term* fsdoc Prims.option) Prims.list)
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0
let uu___is_TyconVariant: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____1632 -> false
let __proj__TyconVariant__item___0:
  tycon ->
    (FStar_Ident.ident* binder Prims.list* knd Prims.option*
      (FStar_Ident.ident* term Prims.option* fsdoc Prims.option* Prims.bool)
      Prims.list)
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
let uu___is_Private: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1682 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1686 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____1690 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____1694 -> false
let uu___is_Assumption: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____1698 -> false
let uu___is_DefaultEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____1702 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____1706 -> false
let uu___is_Effect_qual: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____1710 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____1714 -> false
let uu___is_Inline: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____1718 -> false
let uu___is_Visible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____1722 -> false
let uu___is_Unfold_for_unification_and_vcgen: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____1726 -> false
let uu___is_Inline_for_extraction: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____1730 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____1734 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1738 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____1742 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____1746 -> false
let uu___is_Opaque: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____1750 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____1754 -> false
type qualifiers = qualifier Prims.list
type attributes_ = term Prims.list
type decoration =
  | Qualifier of qualifier
  | DeclAttributes of term Prims.list
  | Doc of fsdoc
let uu___is_Qualifier: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____1771 -> false
let __proj__Qualifier__item___0: decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0
let uu___is_DeclAttributes: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____1784 -> false
let __proj__DeclAttributes__item___0: decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0
let uu___is_Doc: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____1799 -> false
let __proj__Doc__item___0: decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0
type lift_op =
  | NonReifiableLift of term
  | ReifiableLift of (term* term)
  | LiftForFree of term
let uu___is_NonReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____1822 -> false
let __proj__NonReifiableLift__item___0: lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0
let uu___is_ReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____1836 -> false
let __proj__ReifiableLift__item___0: lift_op -> (term* term) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0
let uu___is_LiftForFree: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____1854 -> false
let __proj__LiftForFree__item___0: lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid;
  mdest: FStar_Ident.lid;
  lift_op: lift_op;}
type pragma =
  | SetOptions of Prims.string
  | ResetOptions of Prims.string Prims.option
  | LightOff
let uu___is_SetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____1894 -> false
let __proj__SetOptions__item___0: pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____1907 -> false
let __proj__ResetOptions__item___0: pragma -> Prims.string Prims.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let uu___is_LightOff: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____1921 -> false
type decl' =
  | TopLevelModule of FStar_Ident.lid
  | Open of FStar_Ident.lid
  | Include of FStar_Ident.lid
  | ModuleAbbrev of (FStar_Ident.ident* FStar_Ident.lid)
  | TopLevelLet of (let_qualifier* (pattern* term) Prims.list)
  | Main of term
  | Tycon of (Prims.bool* (tycon* fsdoc Prims.option) Prims.list)
  | Val of (FStar_Ident.ident* term)
  | Exception of (FStar_Ident.ident* term Prims.option)
  | NewEffect of effect_decl
  | NewEffectForFree of effect_decl
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
  | Assume of (FStar_Ident.ident* term)
and decl =
  {
  d: decl';
  drange: FStar_Range.range;
  doc: fsdoc Prims.option;
  quals: qualifiers;
  attrs: attributes_;}
and effect_decl =
  | DefineEffect of (FStar_Ident.ident* binder Prims.list* term* decl
  Prims.list* decl Prims.list)
  | RedefineEffect of (FStar_Ident.ident* binder Prims.list* term)
let uu___is_TopLevelModule: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____2025 -> false
let __proj__TopLevelModule__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0
let uu___is_Open: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____2037 -> false
let __proj__Open__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0
let uu___is_Include: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____2049 -> false
let __proj__Include__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0
let uu___is_ModuleAbbrev: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____2063 -> false
let __proj__ModuleAbbrev__item___0:
  decl' -> (FStar_Ident.ident* FStar_Ident.lid) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0
let uu___is_TopLevelLet: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____2086 -> false
let __proj__TopLevelLet__item___0:
  decl' -> (let_qualifier* (pattern* term) Prims.list) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0
let uu___is_Main: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____2113 -> false
let __proj__Main__item___0: decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0
let uu___is_Tycon: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____2131 -> false
let __proj__Tycon__item___0:
  decl' -> (Prims.bool* (tycon* fsdoc Prims.option) Prims.list) =
  fun projectee  -> match projectee with | Tycon _0 -> _0
let uu___is_Val: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____2163 -> false
let __proj__Val__item___0: decl' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Val _0 -> _0
let uu___is_Exception: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____2184 -> false
let __proj__Exception__item___0:
  decl' -> (FStar_Ident.ident* term Prims.option) =
  fun projectee  -> match projectee with | Exception _0 -> _0
let uu___is_NewEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____2205 -> false
let __proj__NewEffect__item___0: decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0
let uu___is_NewEffectForFree: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffectForFree _0 -> true | uu____2217 -> false
let __proj__NewEffectForFree__item___0: decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffectForFree _0 -> _0
let uu___is_SubEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____2229 -> false
let __proj__SubEffect__item___0: decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0
let uu___is_Pragma: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____2241 -> false
let __proj__Pragma__item___0: decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0
let uu___is_Fsdoc: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____2253 -> false
let __proj__Fsdoc__item___0: decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0
let uu___is_Assume: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____2267 -> false
let __proj__Assume__item___0: decl' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_DefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____2315 -> false
let __proj__DefineEffect__item___0:
  effect_decl ->
    (FStar_Ident.ident* binder Prims.list* term* decl Prims.list* decl
      Prims.list)
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0
let uu___is_RedefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____2355 -> false
let __proj__RedefineEffect__item___0:
  effect_decl -> (FStar_Ident.ident* binder Prims.list* term) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid* decl Prims.list)
  | Interface of (FStar_Ident.lid* decl Prims.list* Prims.bool)
let uu___is_Module: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____2395 -> false
let __proj__Module__item___0: modul -> (FStar_Ident.lid* decl Prims.list) =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Interface: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____2420 -> false
let __proj__Interface__item___0:
  modul -> (FStar_Ident.lid* decl Prims.list* Prims.bool) =
  fun projectee  -> match projectee with | Interface _0 -> _0
type file = modul Prims.list
type inputFragment = (file,decl Prims.list) FStar_Util.either
let check_id: FStar_Ident.ident -> Prims.unit =
  fun id  ->
    let first_char =
      FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1") in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____2449 =
         let uu____2450 =
           let uu____2453 =
             FStar_Util.format1
               "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
               id.FStar_Ident.idText in
           (uu____2453, (id.FStar_Ident.idRange)) in
         FStar_Errors.Error uu____2450 in
       Prims.raise uu____2449)
let at_most_one s r l =
  match l with
  | x::[] -> Some x
  | [] -> None
  | uu____2475 ->
      let uu____2477 =
        let uu____2478 =
          let uu____2481 =
            FStar_Util.format1 "At most one %s is allowed on declarations" s in
          (uu____2481, r) in
        FStar_Errors.Error uu____2478 in
      Prims.raise uu____2477
let mk_decl: decl' -> FStar_Range.range -> decoration Prims.list -> decl =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc =
          let uu____2496 =
            FStar_List.choose
              (fun uu___105_2498  ->
                 match uu___105_2498 with
                 | Doc d -> Some d
                 | uu____2501 -> None) decorations in
          at_most_one "fsdoc" r uu____2496 in
        let attributes_ =
          let uu____2505 =
            FStar_List.choose
              (fun uu___106_2509  ->
                 match uu___106_2509 with
                 | DeclAttributes a -> Some a
                 | uu____2515 -> None) decorations in
          at_most_one "attribute set" r uu____2505 in
        let attributes_ = FStar_Util.dflt [] attributes_ in
        let qualifiers =
          FStar_List.choose
            (fun uu___107_2523  ->
               match uu___107_2523 with
               | Qualifier q -> Some q
               | uu____2526 -> None) decorations in
        { d; drange = r; doc; quals = qualifiers; attrs = attributes_ }
let mk_binder: binder' -> FStar_Range.range -> level -> aqual -> binder =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
let mk_term: term' -> FStar_Range.range -> level -> term =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l }
let mk_uminus: term -> FStar_Range.range -> level -> term =
  fun t  ->
    fun r  ->
      fun l  ->
        let t =
          match t.tm with
          | Const (FStar_Const.Const_int
              (s,Some (FStar_Const.Signed ,width))) ->
              Const
                (FStar_Const.Const_int
                   ((Prims.strcat "-" s), (Some (FStar_Const.Signed, width))))
          | uu____2570 -> Op ("-", [t]) in
        mk_term t r l
let mk_pattern: pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r }
let un_curry_abs: pattern Prims.list -> term -> term' =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____2591 -> Abs (ps, body)
let mk_function:
  (pattern* term Prims.option* term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Syntax_Syntax.next_id () in FStar_Ident.gen r1 in
        let uu____2614 =
          let uu____2615 =
            let uu____2619 =
              let uu____2620 =
                let uu____2621 =
                  let uu____2629 =
                    let uu____2630 =
                      let uu____2631 = FStar_Ident.lid_of_ids [x] in
                      Var uu____2631 in
                    mk_term uu____2630 r1 Expr in
                  (uu____2629, branches) in
                Match uu____2621 in
              mk_term uu____2620 r2 Expr in
            ([mk_pattern (PatVar (x, None)) r1], uu____2619) in
          Abs uu____2615 in
        mk_term uu____2614 r2 Expr
let un_function: pattern -> term -> (pattern* term) Prims.option =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____2651,Abs (pats,body)) ->
          Some ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____2662 -> None
let lid_with_range:
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let uu____2673 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____2673 r
let consPat: FStar_Range.range -> pattern -> pattern -> pattern' =
  fun r  ->
    fun hd  ->
      fun tl  ->
        PatApp
          ((mk_pattern (PatName FStar_Syntax_Const.cons_lid) r), [hd; tl])
let consTerm: FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd  ->
      fun tl  ->
        mk_term
          (Construct
             (FStar_Syntax_Const.cons_lid, [(hd, Nothing); (tl, Nothing)])) r
          Expr
let lexConsTerm: FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd  ->
      fun tl  ->
        mk_term
          (Construct
             (FStar_Syntax_Const.lexcons_lid, [(hd, Nothing); (tl, Nothing)]))
          r Expr
let mkConsList: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Syntax_Const.nil_lid, [])) r Expr in
      FStar_List.fold_right (fun e  -> fun tl  -> consTerm r e tl) elts nil
let mkLexList: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Syntax_Const.lextop_lid, [])) r Expr in
      FStar_List.fold_right (fun e  -> fun tl  -> lexConsTerm r e tl) elts
        nil
let ml_comp: term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Syntax_Const.effect_ML_lid) t.range Expr in
    let t = mk_term (App (ml, t, Nothing)) t.range Expr in t
let tot_comp: term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Syntax_Const.effect_Tot_lid) t.range Expr in
    let t = mk_term (App (ml, t, Nothing)) t.range Expr in t
let mkApp: term -> (term* imp) Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2780 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____2788 ->
                 FStar_List.fold_left
                   (fun t  ->
                      fun uu____2792  ->
                        match uu____2792 with
                        | (a,imp) -> mk_term (App (t, a, imp)) r Un) t args)
let mkRefSet: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let uu____2805 =
        (FStar_Syntax_Const.tset_empty, FStar_Syntax_Const.tset_singleton,
          FStar_Syntax_Const.tset_union) in
      match uu____2805 with
      | (empty_lid,singleton_lid,union_lid) ->
          let empty =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr in
          let ref_constr =
            mk_term
              (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.heap_ref r))
              r Expr in
          let singleton =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr in
          let union =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr in
          FStar_List.fold_right
            (fun e  ->
               fun tl  ->
                 let e = mkApp ref_constr [(e, Nothing)] r in
                 let single_e = mkApp singleton [(e, Nothing)] r in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
let mkExplicitApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2845 ->
            (match t.tm with
             | Name s ->
                 let uu____2848 =
                   let uu____2849 =
                     let uu____2855 =
                       FStar_List.map (fun a  -> (a, Nothing)) args in
                     (s, uu____2855) in
                   Construct uu____2849 in
                 mk_term uu____2848 r Un
             | uu____2865 ->
                 FStar_List.fold_left
                   (fun t  -> fun a  -> mk_term (App (t, a, Nothing)) r Un) t
                   args)
let mkAdmitMagic: FStar_Range.range -> term =
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr in
    let admit =
      let admit_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.admit_lid r)) r
          Expr in
      mkExplicitApp admit_name [unit_const] r in
    let magic =
      let magic_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Syntax_Const.magic_lid r)) r
          Expr in
      mkExplicitApp magic_name [unit_const] r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic r =
  let uu____2888 = mkAdmitMagic r in
  ((mk_pattern PatWild r), None, uu____2888)
let focusBranches branches r =
  let should_filter = FStar_Util.for_some Prims.fst branches in
  if should_filter
  then
    (FStar_Errors.warn r "Focusing on only some cases";
     (let focussed =
        let uu____2944 = FStar_List.filter Prims.fst branches in
        FStar_All.pipe_right uu____2944 (FStar_List.map Prims.snd) in
      let uu____2988 = let uu____2994 = mkWildAdmitMagic r in [uu____2994] in
      FStar_List.append focussed uu____2988))
  else FStar_All.pipe_right branches (FStar_List.map Prims.snd)
let focusLetBindings lbs r =
  let should_filter = FStar_Util.for_some Prims.fst lbs in
  if should_filter
  then
    (FStar_Errors.warn r
       "Focusing on only some cases in this (mutually) recursive definition";
     FStar_List.map
       (fun uu____3080  ->
          match uu____3080 with
          | (f,lb) ->
              if f
              then lb
              else
                (let uu____3096 = mkAdmitMagic r in
                 ((Prims.fst lb), uu____3096))) lbs)
  else FStar_All.pipe_right lbs (FStar_List.map Prims.snd)
let mkFsTypApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____3125 = FStar_List.map (fun a  -> (a, FsTypApp)) args in
        mkApp t uu____3125 r
let mkTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____3144 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____3144 r
let mkDTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons =
        FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____3163 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____3163 r
let mkRefinedBinder:
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
              let b = mk_binder (Annotated (id, t)) m Type_level implicit in
              match refopt with
              | None  -> b
              | Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range in
                     let b =
                       mk_binder (Annotated (x, t)) m Type_level implicit in
                     mk_binder
                       (Annotated
                          (id, (mk_term (Refine (b, phi)) m Type_level))) m
                       Type_level implicit)
let mkRefinedPattern:
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
              let t =
                match phi_opt with
                | None  -> t
                | Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____3218) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level None), phi)) range Type_level
                       | uu____3221 ->
                           let x = FStar_Ident.gen t_range in
                           let phi =
                             let x_var =
                               let uu____3225 =
                                 let uu____3226 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____3226 in
                               mk_term uu____3225 phi.range Formula in
                             let pat_branch = (pat, None, phi) in
                             let otherwise_branch =
                               let uu____3238 =
                                 let uu____3239 =
                                   let uu____3240 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____3240 in
                                 mk_term uu____3239 phi.range Formula in
                               ((mk_pattern PatWild phi.range), None,
                                 uu____3238) in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level None), phi)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                None), phi)) range Type_level) in
              mk_pattern (PatAscribed (pat, t)) range
let rec extract_named_refinement:
  term -> (FStar_Ident.ident* term* term Prims.option) Prims.option =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) -> Some (x, t, None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____3283; blevel = uu____3284;
           aqual = uu____3285;_},t')
        -> Some (x, t, (Some t'))
    | Paren t -> extract_named_refinement t
    | uu____3293 -> None
let rec as_mlist:
  modul Prims.list ->
    ((FStar_Ident.lid* decl)* decl Prims.list) ->
      decl Prims.list -> modul Prims.list
  =
  fun out  ->
    fun cur  ->
      fun ds  ->
        let uu____3323 = cur in
        match uu____3323 with
        | ((m_name,m_decl),cur) ->
            (match ds with
             | [] ->
                 FStar_List.rev
                   ((Module (m_name, (m_decl :: (FStar_List.rev cur)))) ::
                   out)
             | d::ds ->
                 (match d.d with
                  | TopLevelModule m' ->
                      as_mlist
                        ((Module (m_name, (m_decl :: (FStar_List.rev cur))))
                        :: out) ((m', d), []) ds
                  | uu____3348 ->
                      as_mlist out ((m_name, m_decl), (d :: cur)) ds))
let as_frag:
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
                if is_light
                then
                  let uu____3382 = mk_decl (Pragma LightOff) light_range [] in
                  uu____3382 :: ds
                else ds in
              let ms = as_mlist [] ((m, d), []) ds in
              ((let uu____3390 = FStar_List.tl ms in
                match uu____3390 with
                | (Module (m',uu____3393))::uu____3394 ->
                    let msg =
                      "Support for more than one module in a file is deprecated" in
                    let uu____3399 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid m') in
                    FStar_Util.print2_warning "%s (Warning): %s\n" uu____3399
                      msg
                | uu____3400 -> ());
               FStar_Util.Inl ms)
          | uu____3404 ->
              let ds = d :: ds in
              (FStar_List.iter
                 (fun uu___108_3408  ->
                    match uu___108_3408 with
                    | { d = TopLevelModule uu____3409; drange = r;
                        doc = uu____3411; quals = uu____3412;
                        attrs = uu____3413;_} ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected module declaration", r))
                    | uu____3415 -> ()) ds;
               FStar_Util.Inr ds)
let compile_op: Prims.int -> Prims.string -> Prims.string =
  fun arity  ->
    fun s  ->
      let name_of_char uu___109_3427 =
        match uu___109_3427 with
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
        | uu____3428 -> "UNKNOWN" in
      match s with
      | ".[]<-" -> "op_String_Assignment"
      | ".()<-" -> "op_Array_Assignment"
      | ".[]" -> "op_String_Access"
      | ".()" -> "op_Array_Access"
      | uu____3429 ->
          let uu____3430 =
            let uu____3431 =
              let uu____3433 = FStar_String.list_of_string s in
              FStar_List.map name_of_char uu____3433 in
            FStar_String.concat "_" uu____3431 in
          Prims.strcat "op_" uu____3430
let compile_op': Prims.string -> Prims.string =
  fun s  -> compile_op (- (Prims.parse_int "1")) s
let string_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) -> Prims.string =
  fun uu____3445  ->
    match uu____3445 with
    | (comment,keywords) ->
        let uu____3459 =
          let uu____3460 =
            FStar_List.map
              (fun uu____3464  ->
                 match uu____3464 with
                 | (k,v) -> Prims.strcat k (Prims.strcat "->" v)) keywords in
          FStar_String.concat "," uu____3460 in
        Prims.strcat comment uu____3459
let string_of_let_qualifier: let_qualifier -> Prims.string =
  fun uu___110_3471  ->
    match uu___110_3471 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
let to_string_l sep f l =
  let uu____3496 = FStar_List.map f l in FStar_String.concat sep uu____3496
let imp_to_string: imp -> Prims.string =
  fun uu___111_3500  ->
    match uu___111_3500 with | Hash  -> "#" | uu____3501 -> ""
let rec term_to_string: term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____3512) ->
        let uu____3515 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____3515
    | Ensures (t,uu____3517) ->
        let uu____3520 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____3520
    | Labeled (t,l,uu____3523) ->
        let uu____3524 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____3524
    | Const c -> FStar_Syntax_Print.const_to_string c
    | Op (s,xs) ->
        let uu____3530 =
          let uu____3531 =
            FStar_List.map (fun x  -> FStar_All.pipe_right x term_to_string)
              xs in
          FStar_String.concat ", " uu____3531 in
        FStar_Util.format2 "%s(%s)" s uu____3530
    | Tvar id|Uvar id -> id.FStar_Ident.idText
    | Var l|Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____3544 =
          to_string_l " "
            (fun uu____3547  ->
               match uu____3547 with
               | (a,imp) ->
                   let uu____3552 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____3552)
            args in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____3544
    | Abs (pats,t) ->
        let uu____3557 = to_string_l " " pat_to_string pats in
        let uu____3558 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____3557 uu____3558
    | App (t1,t2,imp) ->
        let uu____3562 = FStar_All.pipe_right t1 term_to_string in
        let uu____3563 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____3562 (imp_to_string imp)
          uu____3563
    | Let (Rec ,lbs,body) ->
        let uu____3572 =
          to_string_l " and "
            (fun uu____3575  ->
               match uu____3575 with
               | (p,b) ->
                   let uu____3580 = FStar_All.pipe_right p pat_to_string in
                   let uu____3581 = FStar_All.pipe_right b term_to_string in
                   FStar_Util.format2 "%s=%s" uu____3580 uu____3581) lbs in
        let uu____3582 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format2 "let rec %s in %s" uu____3572 uu____3582
    | Let (q,(pat,tm)::[],body) ->
        let uu____3594 = FStar_All.pipe_right pat pat_to_string in
        let uu____3595 = FStar_All.pipe_right tm term_to_string in
        let uu____3596 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____3594 uu____3595 uu____3596
    | Seq (t1,t2) ->
        let uu____3599 = FStar_All.pipe_right t1 term_to_string in
        let uu____3600 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____3599 uu____3600
    | If (t1,t2,t3) ->
        let uu____3604 = FStar_All.pipe_right t1 term_to_string in
        let uu____3605 = FStar_All.pipe_right t2 term_to_string in
        let uu____3606 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____3604 uu____3605
          uu____3606
    | Match (t,branches) ->
        let uu____3619 = FStar_All.pipe_right t term_to_string in
        let uu____3620 =
          to_string_l " | "
            (fun uu____3625  ->
               match uu____3625 with
               | (p,w,e) ->
                   let uu____3635 = FStar_All.pipe_right p pat_to_string in
                   let uu____3636 =
                     match w with
                     | None  -> ""
                     | Some e ->
                         let uu____3638 = term_to_string e in
                         FStar_Util.format1 "when %s" uu____3638 in
                   let uu____3639 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____3635 uu____3636
                     uu____3639) branches in
        FStar_Util.format2 "match %s with %s" uu____3619 uu____3620
    | Ascribed (t1,t2) ->
        let uu____3642 = FStar_All.pipe_right t1 term_to_string in
        let uu____3643 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____3642 uu____3643
    | Record (Some e,fields) ->
        let uu____3653 = FStar_All.pipe_right e term_to_string in
        let uu____3654 =
          to_string_l " "
            (fun uu____3657  ->
               match uu____3657 with
               | (l,e) ->
                   let uu____3662 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____3662)
            fields in
        FStar_Util.format2 "{%s with %s}" uu____3653 uu____3654
    | Record (None ,fields) ->
        let uu____3671 =
          to_string_l " "
            (fun uu____3674  ->
               match uu____3674 with
               | (l,e) ->
                   let uu____3679 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____3679)
            fields in
        FStar_Util.format1 "{%s}" uu____3671
    | Project (e,l) ->
        let uu____3682 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format2 "%s.%s" uu____3682 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd::tl,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____3696 = FStar_All.pipe_right b binder_to_string in
        let uu____3697 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____3696 uu____3697
    | Product (b::[],t) when x.level = Kind ->
        let uu____3701 = FStar_All.pipe_right b binder_to_string in
        let uu____3702 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____3701 uu____3702
    | Sum (binders,t) ->
        let uu____3707 =
          let uu____3708 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____3708 (FStar_String.concat " * ") in
        let uu____3713 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s * %s" uu____3707 uu____3713
    | QForall (bs,pats,t) ->
        let uu____3723 = to_string_l " " binder_to_string bs in
        let uu____3724 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____3726 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____3723 uu____3724
          uu____3726
    | QExists (bs,pats,t) ->
        let uu____3736 = to_string_l " " binder_to_string bs in
        let uu____3737 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____3739 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____3736 uu____3737
          uu____3739
    | Refine (b,t) ->
        let uu____3742 = FStar_All.pipe_right b binder_to_string in
        let uu____3743 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____3742 uu____3743
    | NamedTyp (x,t) ->
        let uu____3746 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" x.FStar_Ident.idText uu____3746
    | Paren t ->
        let uu____3748 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____3748
    | Product (bs,t) ->
        let uu____3753 =
          let uu____3754 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____3754 (FStar_String.concat ",") in
        let uu____3759 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____3753
          uu____3759
    | t -> "_"
and binder_to_string: binder -> Prims.string =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t)|Annotated (i,t) ->
          let uu____3767 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____3767
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____3769 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____3769 s
and aqual_to_string: aqual -> Prims.string =
  fun uu___112_3770  ->
    match uu___112_3770 with
    | Some (Equality ) -> "$"
    | Some (Implicit ) -> "#"
    | uu____3771 -> ""
and pat_to_string: pattern -> Prims.string =
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Syntax_Print.const_to_string c
    | PatApp (p,ps) ->
        let uu____3778 = FStar_All.pipe_right p pat_to_string in
        let uu____3779 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____3778 uu____3779
    | PatTvar (i,aq)|PatVar (i,aq) ->
        let uu____3786 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____3786 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____3790 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____3790
    | PatTuple (l,false ) ->
        let uu____3794 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____3794
    | PatTuple (l,true ) ->
        let uu____3798 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____3798
    | PatRecord l ->
        let uu____3803 =
          to_string_l "; "
            (fun uu____3806  ->
               match uu____3806 with
               | (f,e) ->
                   let uu____3811 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____3811) l in
        FStar_Util.format1 "{%s}" uu____3803
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" op
    | PatAscribed (p,t) ->
        let uu____3817 = FStar_All.pipe_right p pat_to_string in
        let uu____3818 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____3817 uu____3818
let rec head_id_of_pat: pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____3826) ->
        let uu____3829 = FStar_Ident.lid_of_ids [i] in [uu____3829]
    | PatApp (p,uu____3831) -> head_id_of_pat p
    | PatAscribed (p,uu____3835) -> head_id_of_pat p
    | uu____3836 -> []
let lids_of_let defs =
  FStar_All.pipe_right defs
    (FStar_List.collect
       (fun uu____3857  ->
          match uu____3857 with | (p,uu____3862) -> head_id_of_pat p))
let id_of_tycon: tycon -> Prims.string =
  fun uu___113_3865  ->
    match uu___113_3865 with
    | TyconAbstract (i,_,_)
      |TyconAbbrev (i,_,_,_)|TyconRecord (i,_,_,_)|TyconVariant (i,_,_,_) ->
        i.FStar_Ident.idText
let decl_to_string: decl -> Prims.string =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.strcat "module " l.FStar_Ident.str
    | Open l -> Prims.strcat "open " l.FStar_Ident.str
    | Include l -> Prims.strcat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____3906,pats) ->
        let uu____3914 =
          let uu____3915 =
            let uu____3917 = lids_of_let pats in
            FStar_All.pipe_right uu____3917
              (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
          FStar_All.pipe_right uu____3915 (FStar_String.concat ", ") in
        Prims.strcat "let " uu____3914
    | Main uu____3923 -> "main ..."
    | Assume (i,uu____3925) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____3926,tys) ->
        let uu____3936 =
          let uu____3937 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____3947  ->
                    match uu____3947 with | (x,uu____3952) -> id_of_tycon x)) in
          FStar_All.pipe_right uu____3937 (FStar_String.concat ", ") in
        Prims.strcat "type " uu____3936
    | Val (i,uu____3957) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____3959) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,_,_,_,_))|NewEffect (RedefineEffect (i,_,_))
        -> Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffectForFree (DefineEffect (i,_,_,_,_))|NewEffectForFree
      (RedefineEffect (i,_,_)) ->
        Prims.strcat "new_effect_for_free " i.FStar_Ident.idText
    | SubEffect uu____3984 -> "sub_effect"
    | Pragma uu____3985 -> "pragma"
    | Fsdoc uu____3986 -> "fsdoc"
let modul_to_string: modul -> Prims.string =
  fun m  ->
    match m with
    | Module (_,decls)|Interface (_,decls,_) ->
        let uu____3998 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____3998 (FStar_String.concat "\n")
let error msg tm r =
  let tm = FStar_All.pipe_right tm term_to_string in
  let tm =
    if (FStar_String.length tm) >= (Prims.parse_int "80")
    then
      let uu____4025 =
        FStar_Util.substring tm (Prims.parse_int "0") (Prims.parse_int "77") in
      Prims.strcat uu____4025 "..."
    else tm in
  Prims.raise
    (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm)), r))