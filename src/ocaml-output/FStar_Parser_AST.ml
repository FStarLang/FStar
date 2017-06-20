open Prims
type level =
  | Un
  | Expr
  | Type_level
  | Kind
  | Formula
let uu___is_Un: level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____5 -> false
let uu___is_Expr: level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____10 -> false
let uu___is_Type_level: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____15 -> false
let uu___is_Kind: level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____20 -> false
let uu___is_Formula: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____25 -> false
type imp =
  | FsTypApp
  | Hash
  | UnivApp
  | Nothing
let uu___is_FsTypApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____30 -> false
let uu___is_Hash: imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____35 -> false
let uu___is_UnivApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____40 -> false
let uu___is_Nothing: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____45 -> false
type arg_qualifier =
  | Implicit
  | Equality
let uu___is_Implicit: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____50 -> false
let uu___is_Equality: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____55 -> false
type aqual = arg_qualifier option
type let_qualifier =
  | NoLetQualifier
  | Rec
  | Mutable
let uu___is_NoLetQualifier: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____61 -> false
let uu___is_Rec: let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____66 -> false
let uu___is_Mutable: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____71 -> false
type term' =
  | Wild
  | Const of FStar_Const.sconst
  | Op of (FStar_Ident.ident* term Prims.list)
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
  | Bind of (FStar_Ident.ident* term* term)
  | If of (term* term* term)
  | Match of (term* (pattern* term option* term) Prims.list)
  | TryWith of (term* (pattern* term option* term) Prims.list)
  | Ascribed of (term* term* term option)
  | Record of (term option* (FStar_Ident.lid* term) Prims.list)
  | Project of (term* FStar_Ident.lid)
  | Product of (binder Prims.list* term)
  | Sum of (binder Prims.list* term)
  | QForall of (binder Prims.list* term Prims.list Prims.list* term)
  | QExists of (binder Prims.list* term Prims.list Prims.list* term)
  | Refine of (binder* term)
  | NamedTyp of (FStar_Ident.ident* term)
  | Paren of term
  | Requires of (term* Prims.string option)
  | Ensures of (term* Prims.string option)
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
  | PatVar of (FStar_Ident.ident* arg_qualifier option)
  | PatName of FStar_Ident.lid
  | PatTvar of (FStar_Ident.ident* arg_qualifier option)
  | PatList of pattern Prims.list
  | PatTuple of (pattern Prims.list* Prims.bool)
  | PatRecord of (FStar_Ident.lid* pattern) Prims.list
  | PatAscribed of (pattern* term)
  | PatOr of pattern Prims.list
  | PatOp of FStar_Ident.ident
and pattern = {
  pat: pattern';
  prange: FStar_Range.range;}
let uu___is_Wild: term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____423 -> false
let uu___is_Const: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____429 -> false
let __proj__Const__item___0: term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_Op: term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____446 -> false
let __proj__Op__item___0: term' -> (FStar_Ident.ident* term Prims.list) =
  fun projectee  -> match projectee with | Op _0 -> _0
let uu___is_Tvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____469 -> false
let __proj__Tvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0
let uu___is_Uvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____483 -> false
let __proj__Uvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0
let uu___is_Var: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____497 -> false
let __proj__Var__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Name: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____511 -> false
let __proj__Name__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Projector: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____527 -> false
let __proj__Projector__item___0:
  term' -> (FStar_Ident.lid* FStar_Ident.ident) =
  fun projectee  -> match projectee with | Projector _0 -> _0
let uu___is_Construct: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____552 -> false
let __proj__Construct__item___0:
  term' -> (FStar_Ident.lid* (term* imp) Prims.list) =
  fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Abs: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____584 -> false
let __proj__Abs__item___0: term' -> (pattern Prims.list* term) =
  fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____610 -> false
let __proj__App__item___0: term' -> (term* term* imp) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____639 -> false
let __proj__Let__item___0:
  term' -> (let_qualifier* (pattern* term) Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_LetOpen: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____673 -> false
let __proj__LetOpen__item___0: term' -> (FStar_Ident.lid* term) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0
let uu___is_Seq: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____695 -> false
let __proj__Seq__item___0: term' -> (term* term) =
  fun projectee  -> match projectee with | Seq _0 -> _0
let uu___is_Bind: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____718 -> false
let __proj__Bind__item___0: term' -> (FStar_Ident.ident* term* term) =
  fun projectee  -> match projectee with | Bind _0 -> _0
let uu___is_If: term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____744 -> false
let __proj__If__item___0: term' -> (term* term* term) =
  fun projectee  -> match projectee with | If _0 -> _0
let uu___is_Match: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____774 -> false
let __proj__Match__item___0:
  term' -> (term* (pattern* term option* term) Prims.list) =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_TryWith: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____816 -> false
let __proj__TryWith__item___0:
  term' -> (term* (pattern* term option* term) Prims.list) =
  fun projectee  -> match projectee with | TryWith _0 -> _0
let uu___is_Ascribed: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____855 -> false
let __proj__Ascribed__item___0: term' -> (term* term* term option) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0
let uu___is_Record: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____887 -> false
let __proj__Record__item___0:
  term' -> (term option* (FStar_Ident.lid* term) Prims.list) =
  fun projectee  -> match projectee with | Record _0 -> _0
let uu___is_Project: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____921 -> false
let __proj__Project__item___0: term' -> (term* FStar_Ident.lid) =
  fun projectee  -> match projectee with | Project _0 -> _0
let uu___is_Product: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____944 -> false
let __proj__Product__item___0: term' -> (binder Prims.list* term) =
  fun projectee  -> match projectee with | Product _0 -> _0
let uu___is_Sum: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____970 -> false
let __proj__Sum__item___0: term' -> (binder Prims.list* term) =
  fun projectee  -> match projectee with | Sum _0 -> _0
let uu___is_QForall: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____999 -> false
let __proj__QForall__item___0:
  term' -> (binder Prims.list* term Prims.list Prims.list* term) =
  fun projectee  -> match projectee with | QForall _0 -> _0
let uu___is_QExists: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1037 -> false
let __proj__QExists__item___0:
  term' -> (binder Prims.list* term Prims.list Prims.list* term) =
  fun projectee  -> match projectee with | QExists _0 -> _0
let uu___is_Refine: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1071 -> false
let __proj__Refine__item___0: term' -> (binder* term) =
  fun projectee  -> match projectee with | Refine _0 -> _0
let uu___is_NamedTyp: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1093 -> false
let __proj__NamedTyp__item___0: term' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0
let uu___is_Paren: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1113 -> false
let __proj__Paren__item___0: term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0
let uu___is_Requires: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1130 -> false
let __proj__Requires__item___0: term' -> (term* Prims.string option) =
  fun projectee  -> match projectee with | Requires _0 -> _0
let uu___is_Ensures: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1156 -> false
let __proj__Ensures__item___0: term' -> (term* Prims.string option) =
  fun projectee  -> match projectee with | Ensures _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1182 -> false
let __proj__Labeled__item___0: term' -> (term* Prims.string* Prims.bool) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_Assign: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1207 -> false
let __proj__Assign__item___0: term' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Assign _0 -> _0
let uu___is_Discrim: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1227 -> false
let __proj__Discrim__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0
let uu___is_Attributes: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1242 -> false
let __proj__Attributes__item___0: term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0
let uu___is_Variable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1274 -> false
let __proj__Variable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0
let uu___is_TVariable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1288 -> false
let __proj__TVariable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0
let uu___is_Annotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1304 -> false
let __proj__Annotated__item___0: binder' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Annotated _0 -> _0
let uu___is_TAnnotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1326 -> false
let __proj__TAnnotated__item___0: binder' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0
let uu___is_NoName: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1346 -> false
let __proj__NoName__item___0: binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0
let uu___is_PatWild: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1379 -> false
let uu___is_PatConst: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1385 -> false
let __proj__PatConst__item___0: pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0
let uu___is_PatApp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1402 -> false
let __proj__PatApp__item___0: pattern' -> (pattern* pattern Prims.list) =
  fun projectee  -> match projectee with | PatApp _0 -> _0
let uu___is_PatVar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1428 -> false
let __proj__PatVar__item___0:
  pattern' -> (FStar_Ident.ident* arg_qualifier option) =
  fun projectee  -> match projectee with | PatVar _0 -> _0
let uu___is_PatName: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1451 -> false
let __proj__PatName__item___0: pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0
let uu___is_PatTvar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____1468 -> false
let __proj__PatTvar__item___0:
  pattern' -> (FStar_Ident.ident* arg_qualifier option) =
  fun projectee  -> match projectee with | PatTvar _0 -> _0
let uu___is_PatList: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____1492 -> false
let __proj__PatList__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0
let uu___is_PatTuple: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____1512 -> false
let __proj__PatTuple__item___0: pattern' -> (pattern Prims.list* Prims.bool)
  = fun projectee  -> match projectee with | PatTuple _0 -> _0
let uu___is_PatRecord: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____1538 -> false
let __proj__PatRecord__item___0:
  pattern' -> (FStar_Ident.lid* pattern) Prims.list =
  fun projectee  -> match projectee with | PatRecord _0 -> _0
let uu___is_PatAscribed: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____1563 -> false
let __proj__PatAscribed__item___0: pattern' -> (pattern* term) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0
let uu___is_PatOr: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____1584 -> false
let __proj__PatOr__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0
let uu___is_PatOp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____1601 -> false
let __proj__PatOp__item___0: pattern' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | PatOp _0 -> _0
type branch = (pattern* term option* term)
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string* (Prims.string* Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident* binder Prims.list* knd option)
  | TyconAbbrev of (FStar_Ident.ident* binder Prims.list* knd option* term)
  | TyconRecord of (FStar_Ident.ident* binder Prims.list* knd option*
  (FStar_Ident.ident* term* fsdoc option) Prims.list)
  | TyconVariant of (FStar_Ident.ident* binder Prims.list* knd option*
  (FStar_Ident.ident* term option* fsdoc option* Prims.bool) Prims.list)
let uu___is_TyconAbstract: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____1690 -> false
let __proj__TyconAbstract__item___0:
  tycon -> (FStar_Ident.ident* binder Prims.list* knd option) =
  fun projectee  -> match projectee with | TyconAbstract _0 -> _0
let uu___is_TyconAbbrev: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____1725 -> false
let __proj__TyconAbbrev__item___0:
  tycon -> (FStar_Ident.ident* binder Prims.list* knd option* term) =
  fun projectee  -> match projectee with | TyconAbbrev _0 -> _0
let uu___is_TyconRecord: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____1768 -> false
let __proj__TyconRecord__item___0:
  tycon ->
    (FStar_Ident.ident* binder Prims.list* knd option* (FStar_Ident.ident*
      term* fsdoc option) Prims.list)
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0
let uu___is_TyconVariant: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____1828 -> false
let __proj__TyconVariant__item___0:
  tycon ->
    (FStar_Ident.ident* binder Prims.list* knd option* (FStar_Ident.ident*
      term option* fsdoc option* Prims.bool) Prims.list)
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
    match projectee with | Private  -> true | uu____1880 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1885 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____1890 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____1895 -> false
let uu___is_Assumption: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____1900 -> false
let uu___is_DefaultEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____1905 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____1910 -> false
let uu___is_Effect_qual: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____1915 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____1920 -> false
let uu___is_Inline: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____1925 -> false
let uu___is_Visible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____1930 -> false
let uu___is_Unfold_for_unification_and_vcgen: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____1935 -> false
let uu___is_Inline_for_extraction: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____1940 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____1945 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1950 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____1955 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____1960 -> false
let uu___is_Opaque: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____1965 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____1970 -> false
type qualifiers = qualifier Prims.list
type attributes_ = term Prims.list
type decoration =
  | Qualifier of qualifier
  | DeclAttributes of term Prims.list
  | Doc of fsdoc
let uu___is_Qualifier: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____1991 -> false
let __proj__Qualifier__item___0: decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0
let uu___is_DeclAttributes: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____2006 -> false
let __proj__DeclAttributes__item___0: decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0
let uu___is_Doc: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____2023 -> false
let __proj__Doc__item___0: decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0
type lift_op =
  | NonReifiableLift of term
  | ReifiableLift of (term* term)
  | LiftForFree of term
let uu___is_NonReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____2051 -> false
let __proj__NonReifiableLift__item___0: lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0
let uu___is_ReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____2067 -> false
let __proj__ReifiableLift__item___0: lift_op -> (term* term) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0
let uu___is_LiftForFree: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____2087 -> false
let __proj__LiftForFree__item___0: lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid;
  mdest: FStar_Ident.lid;
  lift_op: lift_op;}
type pragma =
  | SetOptions of Prims.string
  | ResetOptions of Prims.string option
  | LightOff
let uu___is_SetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____2137 -> false
let __proj__SetOptions__item___0: pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____2152 -> false
let __proj__ResetOptions__item___0: pragma -> Prims.string option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let uu___is_LightOff: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____2168 -> false
type decl' =
  | TopLevelModule of FStar_Ident.lid
  | Open of FStar_Ident.lid
  | Include of FStar_Ident.lid
  | ModuleAbbrev of (FStar_Ident.ident* FStar_Ident.lid)
  | TopLevelLet of (let_qualifier* (pattern* term) Prims.list)
  | Main of term
  | Tycon of (Prims.bool* (tycon* fsdoc option) Prims.list)
  | Val of (FStar_Ident.ident* term)
  | Exception of (FStar_Ident.ident* term option)
  | NewEffect of effect_decl
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
  | Assume of (FStar_Ident.ident* term)
and decl =
  {
  d: decl';
  drange: FStar_Range.range;
  doc: fsdoc option;
  quals: qualifiers;
  attrs: attributes_;}
and effect_decl =
  | DefineEffect of (FStar_Ident.ident* binder Prims.list* term* decl
  Prims.list)
  | RedefineEffect of (FStar_Ident.ident* binder Prims.list* term)
let uu___is_TopLevelModule: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____2289 -> false
let __proj__TopLevelModule__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0
let uu___is_Open: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____2303 -> false
let __proj__Open__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0
let uu___is_Include: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____2317 -> false
let __proj__Include__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0
let uu___is_ModuleAbbrev: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____2333 -> false
let __proj__ModuleAbbrev__item___0:
  decl' -> (FStar_Ident.ident* FStar_Ident.lid) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0
let uu___is_TopLevelLet: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____2358 -> false
let __proj__TopLevelLet__item___0:
  decl' -> (let_qualifier* (pattern* term) Prims.list) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0
let uu___is_Main: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____2387 -> false
let __proj__Main__item___0: decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0
let uu___is_Tycon: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____2407 -> false
let __proj__Tycon__item___0:
  decl' -> (Prims.bool* (tycon* fsdoc option) Prims.list) =
  fun projectee  -> match projectee with | Tycon _0 -> _0
let uu___is_Val: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____2441 -> false
let __proj__Val__item___0: decl' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Val _0 -> _0
let uu___is_Exception: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____2464 -> false
let __proj__Exception__item___0: decl' -> (FStar_Ident.ident* term option) =
  fun projectee  -> match projectee with | Exception _0 -> _0
let uu___is_NewEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____2487 -> false
let __proj__NewEffect__item___0: decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0
let uu___is_SubEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____2501 -> false
let __proj__SubEffect__item___0: decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0
let uu___is_Pragma: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____2515 -> false
let __proj__Pragma__item___0: decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0
let uu___is_Fsdoc: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____2529 -> false
let __proj__Fsdoc__item___0: decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0
let uu___is_Assume: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____2545 -> false
let __proj__Assume__item___0: decl' -> (FStar_Ident.ident* term) =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_DefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____2598 -> false
let __proj__DefineEffect__item___0:
  effect_decl ->
    (FStar_Ident.ident* binder Prims.list* term* decl Prims.list)
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0
let uu___is_RedefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____2634 -> false
let __proj__RedefineEffect__item___0:
  effect_decl -> (FStar_Ident.ident* binder Prims.list* term) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid* decl Prims.list)
  | Interface of (FStar_Ident.lid* decl Prims.list* Prims.bool)
let uu___is_Module: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____2678 -> false
let __proj__Module__item___0: modul -> (FStar_Ident.lid* decl Prims.list) =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Interface: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____2705 -> false
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
      (let uu____2736 =
         let uu____2737 =
           let uu____2740 =
             FStar_Util.format1
               "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
               id.FStar_Ident.idText in
           (uu____2740, (id.FStar_Ident.idRange)) in
         FStar_Errors.Error uu____2737 in
       raise uu____2736)
let at_most_one s r l =
  match l with
  | x::[] -> Some x
  | [] -> None
  | uu____2766 ->
      let uu____2768 =
        let uu____2769 =
          let uu____2772 =
            FStar_Util.format1 "At most one %s is allowed on declarations" s in
          (uu____2772, r) in
        FStar_Errors.Error uu____2769 in
      raise uu____2768
let mk_decl: decl' -> FStar_Range.range -> decoration Prims.list -> decl =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____2790 =
            FStar_List.choose
              (fun uu___75_2792  ->
                 match uu___75_2792 with
                 | Doc d1 -> Some d1
                 | uu____2795 -> None) decorations in
          at_most_one "fsdoc" r uu____2790 in
        let attributes_ =
          let uu____2799 =
            FStar_List.choose
              (fun uu___76_2803  ->
                 match uu___76_2803 with
                 | DeclAttributes a -> Some a
                 | uu____2809 -> None) decorations in
          at_most_one "attribute set" r uu____2799 in
        let attributes_1 = FStar_Util.dflt [] attributes_ in
        let qualifiers =
          FStar_List.choose
            (fun uu___77_2817  ->
               match uu___77_2817 with
               | Qualifier q -> Some q
               | uu____2820 -> None) decorations in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
let mk_binder: binder' -> FStar_Range.range -> level -> aqual -> binder =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
let mk_term: term' -> FStar_Range.range -> level -> term =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l }
let mk_uminus:
  term -> FStar_Range.range -> FStar_Range.range -> level -> term =
  fun t  ->
    fun rminus  ->
      fun r  ->
        fun l  ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s,Some (FStar_Const.Signed ,width))) ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.strcat "-" s),
                       (Some (FStar_Const.Signed, width))))
            | uu____2878 -> Op ((FStar_Ident.mk_ident ("-", rminus)), [t]) in
          mk_term t1 r l
let mk_pattern: pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r }
let un_curry_abs: pattern Prims.list -> term -> term' =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____2903 -> Abs (ps, body)
let mk_function:
  (pattern* term option* term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id () in FStar_Ident.gen r1 in
        let uu____2929 =
          let uu____2930 =
            let uu____2934 =
              let uu____2935 =
                let uu____2936 =
                  let uu____2944 =
                    let uu____2945 =
                      let uu____2946 = FStar_Ident.lid_of_ids [x] in
                      Var uu____2946 in
                    mk_term uu____2945 r1 Expr in
                  (uu____2944, branches) in
                Match uu____2936 in
              mk_term uu____2935 r2 Expr in
            ([mk_pattern (PatVar (x, None)) r1], uu____2934) in
          Abs uu____2930 in
        mk_term uu____2929 r2 Expr
let un_function: pattern -> term -> (pattern* term) option =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____2968,Abs (pats,body)) ->
          Some ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____2979 -> None
let lid_with_range:
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let uu____2992 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____2992 r
let consPat: FStar_Range.range -> pattern -> pattern -> pattern' =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
let consTerm: FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
let lexConsTerm: FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
let mkConsList: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
let mkLexList: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
let ml_comp: term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let tot_comp: term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let mkApp: term -> (term* imp) Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____3117 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____3125 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____3129  ->
                        match uu____3129 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
let mkRefSet: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let uu____3144 =
        (FStar_Parser_Const.tset_empty, FStar_Parser_Const.tset_singleton,
          FStar_Parser_Const.tset_union) in
      match uu____3144 with
      | (empty_lid,singleton_lid,union_lid) ->
          let empty1 =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr in
          let ref_constr =
            mk_term
              (Var (FStar_Ident.set_lid_range FStar_Parser_Const.heap_ref r))
              r Expr in
          let singleton1 =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr in
          let union1 =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp ref_constr [(e, Nothing)] r in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
let mkExplicitApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____3187 ->
            (match t.tm with
             | Name s ->
                 let uu____3190 =
                   let uu____3191 =
                     let uu____3197 =
                       FStar_List.map (fun a  -> (a, Nothing)) args in
                     (s, uu____3197) in
                   Construct uu____3191 in
                 mk_term uu____3190 r Un
             | uu____3207 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
let mkAdmitMagic: FStar_Range.range -> term =
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr in
    let admit1 =
      let admit_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r)) r
          Expr in
      mkExplicitApp admit_name [unit_const] r in
    let magic1 =
      let magic_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r)) r
          Expr in
      mkExplicitApp magic_name [unit_const] r in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr in admit_magic
let mkWildAdmitMagic r =
  let uu____3233 = mkAdmitMagic r in
  ((mk_pattern PatWild r), None, uu____3233)
let focusBranches branches r =
  let should_filter = FStar_Util.for_some FStar_Pervasives.fst branches in
  if should_filter
  then
    (FStar_Errors.warn r "Focusing on only some cases";
     (let focussed =
        let uu____3292 = FStar_List.filter FStar_Pervasives.fst branches in
        FStar_All.pipe_right uu____3292 (FStar_List.map FStar_Pervasives.snd) in
      let uu____3336 = let uu____3342 = mkWildAdmitMagic r in [uu____3342] in
      FStar_List.append focussed uu____3336))
  else FStar_All.pipe_right branches (FStar_List.map FStar_Pervasives.snd)
let focusLetBindings lbs r =
  let should_filter = FStar_Util.for_some FStar_Pervasives.fst lbs in
  if should_filter
  then
    (FStar_Errors.warn r
       "Focusing on only some cases in this (mutually) recursive definition";
     FStar_List.map
       (fun uu____3431  ->
          match uu____3431 with
          | (f,lb) ->
              if f
              then lb
              else
                (let uu____3447 = mkAdmitMagic r in ((fst lb), uu____3447)))
       lbs)
  else FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives.snd)
let mkFsTypApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____3479 = FStar_List.map (fun a  -> (a, FsTypApp)) args in
        mkApp t uu____3479 r
let mkTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____3503 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____3503 r
let mkDTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____3527 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____3527 r
let mkRefinedBinder:
  FStar_Ident.ident ->
    term -> Prims.bool -> term option -> FStar_Range.range -> aqual -> binder
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
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit in
                     mk_binder
                       (Annotated
                          (id, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
let mkRefinedPattern:
  pattern ->
    term ->
      Prims.bool ->
        term option -> FStar_Range.range -> FStar_Range.range -> pattern
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
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____3594) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level None), phi)) range Type_level
                       | uu____3597 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____3601 =
                                 let uu____3602 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____3602 in
                               mk_term uu____3601 phi.range Formula in
                             let pat_branch = (pat, None, phi) in
                             let otherwise_branch =
                               let uu____3614 =
                                 let uu____3615 =
                                   let uu____3616 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____3616 in
                                 mk_term uu____3615 phi.range Formula in
                               ((mk_pattern PatWild phi.range), None,
                                 uu____3614) in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level None), phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                None), phi)) range Type_level) in
              mk_pattern (PatAscribed (pat, t1)) range
let rec extract_named_refinement:
  term -> (FStar_Ident.ident* term* term option) option =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) -> Some (x, t, None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____3660; blevel = uu____3661;
           aqual = uu____3662;_},t')
        -> Some (x, t, (Some t'))
    | Paren t -> extract_named_refinement t
    | uu____3670 -> None
let rec as_mlist:
  modul Prims.list ->
    ((FStar_Ident.lid* decl)* decl Prims.list) ->
      decl Prims.list -> modul Prims.list
  =
  fun out  ->
    fun cur  ->
      fun ds  ->
        let uu____3703 = cur in
        match uu____3703 with
        | ((m_name,m_decl),cur1) ->
            (match ds with
             | [] ->
                 FStar_List.rev
                   ((Module (m_name, (m_decl :: (FStar_List.rev cur1)))) ::
                   out)
             | d::ds1 ->
                 (match d.d with
                  | TopLevelModule m' ->
                      as_mlist
                        ((Module (m_name, (m_decl :: (FStar_List.rev cur1))))
                        :: out) ((m', d), []) ds1
                  | uu____3728 ->
                      as_mlist out ((m_name, m_decl), (d :: cur1)) ds1))
let as_frag:
  Prims.bool ->
    FStar_Range.range ->
      decl Prims.list -> (modul Prims.list,decl Prims.list) FStar_Util.either
  =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____3754 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> raise FStar_Errors.Empty_frag in
        match uu____3754 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____3784 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____3784 :: ds1
                   else ds1 in
                 let ms = as_mlist [] ((m, d), []) ds2 in
                 ((let uu____3792 = FStar_List.tl ms in
                   match uu____3792 with
                   | (Module (m',uu____3795))::uu____3796 ->
                       let msg =
                         "Support for more than one module in a file is deprecated" in
                       let uu____3801 =
                         FStar_Range.string_of_range
                           (FStar_Ident.range_of_lid m') in
                       FStar_Util.print2_warning "%s (Warning): %s\n"
                         uu____3801 msg
                   | uu____3802 -> ());
                  FStar_Util.Inl ms)
             | uu____3806 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___78_3810  ->
                       match uu___78_3810 with
                       | { d = TopLevelModule uu____3811; drange = r;
                           doc = uu____3813; quals = uu____3814;
                           attrs = uu____3815;_} ->
                           raise
                             (FStar_Errors.Error
                                ("Unexpected module declaration", r))
                       | uu____3817 -> ()) ds2;
                  FStar_Util.Inr ds2))
let compile_op: Prims.int -> Prims.string -> Prims.string =
  fun arity  ->
    fun s  ->
      let name_of_char uu___79_3831 =
        match uu___79_3831 with
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
        | uu____3832 -> "UNKNOWN" in
      match s with
      | ".[]<-" -> "op_String_Assignment"
      | ".()<-" -> "op_Array_Assignment"
      | ".[]" -> "op_String_Access"
      | ".()" -> "op_Array_Access"
      | uu____3833 ->
          let uu____3834 =
            let uu____3835 =
              let uu____3837 = FStar_String.list_of_string s in
              FStar_List.map name_of_char uu____3837 in
            FStar_String.concat "_" uu____3835 in
          Prims.strcat "op_" uu____3834
let compile_op': Prims.string -> Prims.string =
  fun s  -> compile_op (- (Prims.parse_int "1")) s
let string_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) -> Prims.string =
  fun uu____3851  ->
    match uu____3851 with
    | (comment,keywords) ->
        let uu____3865 =
          let uu____3866 =
            FStar_List.map
              (fun uu____3870  ->
                 match uu____3870 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords in
          FStar_String.concat "," uu____3866 in
        Prims.strcat comment uu____3865
let string_of_let_qualifier: let_qualifier -> Prims.string =
  fun uu___80_3878  ->
    match uu___80_3878 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
let to_string_l sep f l =
  let uu____3907 = FStar_List.map f l in FStar_String.concat sep uu____3907
let imp_to_string: imp -> Prims.string =
  fun uu___81_3912  ->
    match uu___81_3912 with | Hash  -> "#" | uu____3913 -> ""
let rec term_to_string: term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____3924) ->
        let uu____3927 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____3927
    | Ensures (t,uu____3929) ->
        let uu____3932 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____3932
    | Labeled (t,l,uu____3935) ->
        let uu____3936 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____3936
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____3942 =
          let uu____3943 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs in
          FStar_String.concat ", " uu____3943 in
        FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____3942
    | Tvar id -> id.FStar_Ident.idText
    | Uvar id -> id.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____3958 =
          to_string_l " "
            (fun uu____3961  ->
               match uu____3961 with
               | (a,imp) ->
                   let uu____3966 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____3966)
            args in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____3958
    | Abs (pats,t) ->
        let uu____3971 = to_string_l " " pat_to_string pats in
        let uu____3972 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____3971 uu____3972
    | App (t1,t2,imp) ->
        let uu____3976 = FStar_All.pipe_right t1 term_to_string in
        let uu____3977 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____3976 (imp_to_string imp)
          uu____3977
    | Let (Rec ,lbs,body) ->
        let uu____3986 =
          to_string_l " and "
            (fun uu____3989  ->
               match uu____3989 with
               | (p,b) ->
                   let uu____3994 = FStar_All.pipe_right p pat_to_string in
                   let uu____3995 = FStar_All.pipe_right b term_to_string in
                   FStar_Util.format2 "%s=%s" uu____3994 uu____3995) lbs in
        let uu____3996 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format2 "let rec %s in %s" uu____3986 uu____3996
    | Let (q,(pat,tm)::[],body) ->
        let uu____4008 = FStar_All.pipe_right pat pat_to_string in
        let uu____4009 = FStar_All.pipe_right tm term_to_string in
        let uu____4010 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____4008 uu____4009 uu____4010
    | Seq (t1,t2) ->
        let uu____4013 = FStar_All.pipe_right t1 term_to_string in
        let uu____4014 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____4013 uu____4014
    | If (t1,t2,t3) ->
        let uu____4018 = FStar_All.pipe_right t1 term_to_string in
        let uu____4019 = FStar_All.pipe_right t2 term_to_string in
        let uu____4020 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____4018 uu____4019
          uu____4020
    | Match (t,branches) ->
        let uu____4033 = FStar_All.pipe_right t term_to_string in
        let uu____4034 =
          to_string_l " | "
            (fun uu____4039  ->
               match uu____4039 with
               | (p,w,e) ->
                   let uu____4049 = FStar_All.pipe_right p pat_to_string in
                   let uu____4050 =
                     match w with
                     | None  -> ""
                     | Some e1 ->
                         let uu____4052 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____4052 in
                   let uu____4053 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____4049 uu____4050
                     uu____4053) branches in
        FStar_Util.format2 "match %s with %s" uu____4033 uu____4034
    | Ascribed (t1,t2,None ) ->
        let uu____4057 = FStar_All.pipe_right t1 term_to_string in
        let uu____4058 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____4057 uu____4058
    | Ascribed (t1,t2,Some tac) ->
        let uu____4063 = FStar_All.pipe_right t1 term_to_string in
        let uu____4064 = FStar_All.pipe_right t2 term_to_string in
        let uu____4065 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____4063 uu____4064 uu____4065
    | Record (Some e,fields) ->
        let uu____4075 = FStar_All.pipe_right e term_to_string in
        let uu____4076 =
          to_string_l " "
            (fun uu____4079  ->
               match uu____4079 with
               | (l,e1) ->
                   let uu____4084 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____4084)
            fields in
        FStar_Util.format2 "{%s with %s}" uu____4075 uu____4076
    | Record (None ,fields) ->
        let uu____4093 =
          to_string_l " "
            (fun uu____4096  ->
               match uu____4096 with
               | (l,e) ->
                   let uu____4101 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____4101)
            fields in
        FStar_Util.format1 "{%s}" uu____4093
    | Project (e,l) ->
        let uu____4104 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format2 "%s.%s" uu____4104 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____4118 = FStar_All.pipe_right b binder_to_string in
        let uu____4119 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____4118 uu____4119
    | Product (b::[],t) when x.level = Kind ->
        let uu____4123 = FStar_All.pipe_right b binder_to_string in
        let uu____4124 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____4123 uu____4124
    | Sum (binders,t) ->
        let uu____4129 =
          let uu____4130 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____4130 (FStar_String.concat " * ") in
        let uu____4135 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s * %s" uu____4129 uu____4135
    | QForall (bs,pats,t) ->
        let uu____4145 = to_string_l " " binder_to_string bs in
        let uu____4146 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____4148 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____4145 uu____4146
          uu____4148
    | QExists (bs,pats,t) ->
        let uu____4158 = to_string_l " " binder_to_string bs in
        let uu____4159 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____4161 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____4158 uu____4159
          uu____4161
    | Refine (b,t) ->
        let uu____4164 = FStar_All.pipe_right b binder_to_string in
        let uu____4165 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____4164 uu____4165
    | NamedTyp (x1,t) ->
        let uu____4168 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____4168
    | Paren t ->
        let uu____4170 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____4170
    | Product (bs,t) ->
        let uu____4175 =
          let uu____4176 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____4176 (FStar_String.concat ",") in
        let uu____4181 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____4175
          uu____4181
    | t -> "_"
and binder_to_string: binder -> Prims.string =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____4189 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____4189
      | Annotated (i,t) ->
          let uu____4192 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____4192
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____4194 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____4194 s
and aqual_to_string: aqual -> Prims.string =
  fun uu___82_4195  ->
    match uu___82_4195 with
    | Some (Equality ) -> "$"
    | Some (Implicit ) -> "#"
    | uu____4196 -> ""
and pat_to_string: pattern -> Prims.string =
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____4203 = FStar_All.pipe_right p pat_to_string in
        let uu____4204 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____4203 uu____4204
    | PatTvar (i,aq) ->
        let uu____4209 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____4209 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____4214 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____4214 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____4218 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____4218
    | PatTuple (l,false ) ->
        let uu____4222 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____4222
    | PatTuple (l,true ) ->
        let uu____4226 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____4226
    | PatRecord l ->
        let uu____4231 =
          to_string_l "; "
            (fun uu____4234  ->
               match uu____4234 with
               | (f,e) ->
                   let uu____4239 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____4239) l in
        FStar_Util.format1 "{%s}" uu____4231
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op)
    | PatAscribed (p,t) ->
        let uu____4245 = FStar_All.pipe_right p pat_to_string in
        let uu____4246 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____4245 uu____4246
let rec head_id_of_pat: pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____4255) ->
        let uu____4258 = FStar_Ident.lid_of_ids [i] in [uu____4258]
    | PatApp (p1,uu____4260) -> head_id_of_pat p1
    | PatAscribed (p1,uu____4264) -> head_id_of_pat p1
    | uu____4265 -> []
let lids_of_let defs =
  FStar_All.pipe_right defs
    (FStar_List.collect
       (fun uu____4288  ->
          match uu____4288 with | (p,uu____4293) -> head_id_of_pat p))
let id_of_tycon: tycon -> Prims.string =
  fun uu___83_4297  ->
    match uu___83_4297 with
    | TyconAbstract (i,uu____4299,uu____4300) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____4306,uu____4307,uu____4308) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____4314,uu____4315,uu____4316) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____4332,uu____4333,uu____4334) ->
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
    | TopLevelLet (uu____4362,pats) ->
        let uu____4370 =
          let uu____4371 =
            let uu____4373 = lids_of_let pats in
            FStar_All.pipe_right uu____4373
              (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
          FStar_All.pipe_right uu____4371 (FStar_String.concat ", ") in
        Prims.strcat "let " uu____4370
    | Main uu____4379 -> "main ..."
    | Assume (i,uu____4381) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____4382,tys) ->
        let uu____4392 =
          let uu____4393 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____4403  ->
                    match uu____4403 with | (x,uu____4408) -> id_of_tycon x)) in
          FStar_All.pipe_right uu____4393 (FStar_String.concat ", ") in
        Prims.strcat "type " uu____4392
    | Val (i,uu____4413) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____4415) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____4419,uu____4420,uu____4421)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____4427,uu____4428)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | SubEffect uu____4431 -> "sub_effect"
    | Pragma uu____4432 -> "pragma"
    | Fsdoc uu____4433 -> "fsdoc"
let modul_to_string: modul -> Prims.string =
  fun m  ->
    match m with
    | Module (uu____4438,decls) ->
        let uu____4442 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____4442 (FStar_String.concat "\n")
    | Interface (uu____4447,decls,uu____4449) ->
        let uu____4452 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____4452 (FStar_String.concat "\n")
let error msg tm r =
  let tm1 = FStar_All.pipe_right tm term_to_string in
  let tm2 =
    if (FStar_String.length tm1) >= (Prims.parse_int "80")
    then
      let uu____4486 =
        FStar_Util.substring tm1 (Prims.parse_int "0") (Prims.parse_int "77") in
      Prims.strcat uu____4486 "..."
    else tm1 in
  raise (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm2)), r))