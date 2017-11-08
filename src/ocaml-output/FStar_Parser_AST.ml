open Prims
type level =
  | Un
  | Expr
  | Type_level
  | Kind
  | Formula[@@deriving show]
let uu___is_Un: level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____4 -> false
let uu___is_Expr: level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____8 -> false
let uu___is_Type_level: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____12 -> false
let uu___is_Kind: level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____16 -> false
let uu___is_Formula: level -> Prims.bool =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____20 -> false
type imp =
  | FsTypApp
  | Hash
  | UnivApp
  | Nothing[@@deriving show]
let uu___is_FsTypApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____24 -> false
let uu___is_Hash: imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____28 -> false
let uu___is_UnivApp: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____32 -> false
let uu___is_Nothing: imp -> Prims.bool =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____36 -> false
type arg_qualifier =
  | Implicit
  | Equality[@@deriving show]
let uu___is_Implicit: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____40 -> false
let uu___is_Equality: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____44 -> false
type aqual = arg_qualifier FStar_Pervasives_Native.option[@@deriving show]
type let_qualifier =
  | NoLetQualifier
  | Rec
  | Mutable[@@deriving show]
let uu___is_NoLetQualifier: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____50 -> false
let uu___is_Rec: let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____54 -> false
let uu___is_Mutable: let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____58 -> false
type term' =
  | Wild
  | Const of FStar_Const.sconst
  | Op of (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  | Tvar of FStar_Ident.ident
  | Uvar of FStar_Ident.ident
  | Var of FStar_Ident.lid
  | Name of FStar_Ident.lid
  | Projector of (FStar_Ident.lid,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2
  | Construct of
  (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Abs of (pattern Prims.list,term) FStar_Pervasives_Native.tuple2
  | App of (term,term,imp) FStar_Pervasives_Native.tuple3
  | Let of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
  term) FStar_Pervasives_Native.tuple3
  | LetOpen of (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2
  | Seq of (term,term) FStar_Pervasives_Native.tuple2
  | Bind of (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3
  | If of (term,term,term) FStar_Pervasives_Native.tuple3
  | Match of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2
  | TryWith of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Ascribed of (term,term,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3
  | Record of
  (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                         FStar_Pervasives_Native.tuple2
                                         Prims.list)
  FStar_Pervasives_Native.tuple2
  | Project of (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  | Product of (binder Prims.list,term) FStar_Pervasives_Native.tuple2
  | Sum of (binder Prims.list,term) FStar_Pervasives_Native.tuple2
  | QForall of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3
  | QExists of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3
  | Refine of (binder,term) FStar_Pervasives_Native.tuple2
  | NamedTyp of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
  | Paren of term
  | Requires of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Ensures of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Labeled of (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3
  | Assign of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
  | Discrim of FStar_Ident.lid
  | Attributes of term Prims.list[@@deriving show]
and term = {
  tm: term';
  range: FStar_Range.range;
  level: level;}[@@deriving show]
and binder' =
  | Variable of FStar_Ident.ident
  | TVariable of FStar_Ident.ident
  | Annotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
  | TAnnotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
  | NoName of term[@@deriving show]
and binder =
  {
  b: binder';
  brange: FStar_Range.range;
  blevel: level;
  aqual: aqual;}[@@deriving show]
and pattern' =
  | PatWild
  | PatConst of FStar_Const.sconst
  | PatApp of (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2
  | PatVar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | PatName of FStar_Ident.lid
  | PatTvar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | PatList of pattern Prims.list
  | PatTuple of (pattern Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | PatRecord of (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2
  Prims.list
  | PatAscribed of (pattern,term) FStar_Pervasives_Native.tuple2
  | PatOr of pattern Prims.list
  | PatOp of FStar_Ident.ident[@@deriving show]
and pattern = {
  pat: pattern';
  prange: FStar_Range.range;}[@@deriving show]
let uu___is_Wild: term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____524 -> false
let uu___is_Const: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____529 -> false
let __proj__Const__item___0: term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_Op: term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____547 -> false
let __proj__Op__item___0:
  term' -> (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Op _0 -> _0
let uu___is_Tvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____577 -> false
let __proj__Tvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0
let uu___is_Uvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____589 -> false
let __proj__Uvar__item___0: term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0
let uu___is_Var: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____601 -> false
let __proj__Var__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Name: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____613 -> false
let __proj__Name__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Projector: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____629 -> false
let __proj__Projector__item___0:
  term' -> (FStar_Ident.lid,FStar_Ident.ident) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Projector _0 -> _0
let uu___is_Construct: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____663 -> false
let __proj__Construct__item___0:
  term' ->
    (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Abs: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____711 -> false
let __proj__Abs__item___0:
  term' -> (pattern Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____747 -> false
let __proj__App__item___0:
  term' -> (term,term,imp) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____789 -> false
let __proj__Let__item___0:
  term' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
      term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_LetOpen: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____841 -> false
let __proj__LetOpen__item___0:
  term' -> (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LetOpen _0 -> _0
let uu___is_Seq: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____869 -> false
let __proj__Seq__item___0:
  term' -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Seq _0 -> _0
let uu___is_Bind: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____899 -> false
let __proj__Bind__item___0:
  term' -> (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Bind _0 -> _0
let uu___is_If: term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____935 -> false
let __proj__If__item___0:
  term' -> (term,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | If _0 -> _0
let uu___is_Match: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____979 -> false
let __proj__Match__item___0:
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_TryWith: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1047 -> false
let __proj__TryWith__item___0:
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TryWith _0 -> _0
let uu___is_Ascribed: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1109 -> false
let __proj__Ascribed__item___0:
  term' ->
    (term,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Ascribed _0 -> _0
let uu___is_Record: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1157 -> false
let __proj__Record__item___0:
  term' ->
    (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                           FStar_Pervasives_Native.tuple2
                                           Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Record _0 -> _0
let uu___is_Project: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1209 -> false
let __proj__Project__item___0:
  term' -> (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Project _0 -> _0
let uu___is_Product: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1239 -> false
let __proj__Product__item___0:
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Product _0 -> _0
let uu___is_Sum: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1275 -> false
let __proj__Sum__item___0:
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Sum _0 -> _0
let uu___is_QForall: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1317 -> false
let __proj__QForall__item___0:
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QForall _0 -> _0
let uu___is_QExists: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1377 -> false
let __proj__QExists__item___0:
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QExists _0 -> _0
let uu___is_Refine: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1429 -> false
let __proj__Refine__item___0:
  term' -> (binder,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Refine _0 -> _0
let uu___is_NamedTyp: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1457 -> false
let __proj__NamedTyp__item___0:
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0
let uu___is_Paren: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1481 -> false
let __proj__Paren__item___0: term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0
let uu___is_Requires: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1499 -> false
let __proj__Requires__item___0:
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Requires _0 -> _0
let uu___is_Ensures: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1535 -> false
let __proj__Ensures__item___0:
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Ensures _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1571 -> false
let __proj__Labeled__item___0:
  term' -> (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_Assign: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1605 -> false
let __proj__Assign__item___0:
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assign _0 -> _0
let uu___is_Discrim: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1629 -> false
let __proj__Discrim__item___0: term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0
let uu___is_Attributes: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1643 -> false
let __proj__Attributes__item___0: term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0
let __proj__Mkterm__item__tm: term -> term' =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__tm
let __proj__Mkterm__item__range: term -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__range
let __proj__Mkterm__item__level: term -> level =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; range = __fname__range; level = __fname__level;_}
        -> __fname__level
let uu___is_Variable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1679 -> false
let __proj__Variable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0
let uu___is_TVariable: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1691 -> false
let __proj__TVariable__item___0: binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0
let uu___is_Annotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1707 -> false
let __proj__Annotated__item___0:
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Annotated _0 -> _0
let uu___is_TAnnotated: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1735 -> false
let __proj__TAnnotated__item___0:
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0
let uu___is_NoName: binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1759 -> false
let __proj__NoName__item___0: binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0
let __proj__Mkbinder__item__b: binder -> binder' =
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__b
let __proj__Mkbinder__item__brange: binder -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__brange
let __proj__Mkbinder__item__blevel: binder -> level =
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__blevel
let __proj__Mkbinder__item__aqual: binder -> aqual =
  fun projectee  ->
    match projectee with
    | { b = __fname__b; brange = __fname__brange; blevel = __fname__blevel;
        aqual = __fname__aqual;_} -> __fname__aqual
let uu___is_PatWild: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1798 -> false
let uu___is_PatConst: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1803 -> false
let __proj__PatConst__item___0: pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0
let uu___is_PatApp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1821 -> false
let __proj__PatApp__item___0:
  pattern' -> (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatApp _0 -> _0
let uu___is_PatVar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1857 -> false
let __proj__PatVar__item___0:
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatVar _0 -> _0
let uu___is_PatName: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1887 -> false
let __proj__PatName__item___0: pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0
let uu___is_PatTvar: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____1905 -> false
let __proj__PatTvar__item___0:
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTvar _0 -> _0
let uu___is_PatList: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____1937 -> false
let __proj__PatList__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0
let uu___is_PatTuple: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____1961 -> false
let __proj__PatTuple__item___0:
  pattern' -> (pattern Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTuple _0 -> _0
let uu___is_PatRecord: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____1997 -> false
let __proj__PatRecord__item___0:
  pattern' ->
    (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PatRecord _0 -> _0
let uu___is_PatAscribed: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2031 -> false
let __proj__PatAscribed__item___0:
  pattern' -> (pattern,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0
let uu___is_PatOr: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2057 -> false
let __proj__PatOr__item___0: pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0
let uu___is_PatOp: pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2075 -> false
let __proj__PatOp__item___0: pattern' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | PatOp _0 -> _0
let __proj__Mkpattern__item__pat: pattern -> pattern' =
  fun projectee  ->
    match projectee with
    | { pat = __fname__pat; prange = __fname__prange;_} -> __fname__pat
let __proj__Mkpattern__item__prange: pattern -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pat = __fname__pat; prange = __fname__prange;_} -> __fname__prange
type branch =
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type knd = term[@@deriving show]
type typ = term[@@deriving show]
type expr = term[@@deriving show]
type fsdoc =
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2[@@deriving show]
type tycon =
  | TyconAbstract of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3
  | TyconAbbrev of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  term) FStar_Pervasives_Native.tuple4
  | TyconRecord of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple4
  | TyconVariant of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                           FStar_Pervasives_Native.option,
    Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_TyconAbstract: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____2211 -> false
let __proj__TyconAbstract__item___0:
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0
let uu___is_TyconAbbrev: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____2265 -> false
let __proj__TyconAbbrev__item___0:
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      term) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0
let uu___is_TyconRecord: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____2335 -> false
let __proj__TyconRecord__item___0:
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0
let uu___is_TyconVariant: tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____2439 -> false
let __proj__TyconVariant__item___0:
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                               FStar_Pervasives_Native.option,
        Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
      FStar_Pervasives_Native.tuple4
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
  | Logic[@@deriving show]
let uu___is_Private: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____2528 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____2532 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____2536 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____2540 -> false
let uu___is_Assumption: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____2544 -> false
let uu___is_DefaultEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____2548 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____2552 -> false
let uu___is_Effect_qual: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____2556 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____2560 -> false
let uu___is_Inline: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____2564 -> false
let uu___is_Visible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____2568 -> false
let uu___is_Unfold_for_unification_and_vcgen: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____2572 -> false
let uu___is_Inline_for_extraction: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____2576 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____2580 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____2584 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____2588 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____2592 -> false
let uu___is_Opaque: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____2596 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____2600 -> false
type qualifiers = qualifier Prims.list[@@deriving show]
type attributes_ = term Prims.list[@@deriving show]
type decoration =
  | Qualifier of qualifier
  | DeclAttributes of term Prims.list
  | Doc of fsdoc[@@deriving show]
let uu___is_Qualifier: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____2623 -> false
let __proj__Qualifier__item___0: decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0
let uu___is_DeclAttributes: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____2637 -> false
let __proj__DeclAttributes__item___0: decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0
let uu___is_Doc: decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____2655 -> false
let __proj__Doc__item___0: decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0
type lift_op =
  | NonReifiableLift of term
  | ReifiableLift of (term,term) FStar_Pervasives_Native.tuple2
  | LiftForFree of term[@@deriving show]
let uu___is_NonReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____2683 -> false
let __proj__NonReifiableLift__item___0: lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0
let uu___is_ReifiableLift: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____2699 -> false
let __proj__ReifiableLift__item___0:
  lift_op -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0
let uu___is_LiftForFree: lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____2723 -> false
let __proj__LiftForFree__item___0: lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid;
  mdest: FStar_Ident.lid;
  lift_op: lift_op;}[@@deriving show]
let __proj__Mklift__item__msource: lift -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__msource
let __proj__Mklift__item__mdest: lift -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__mdest
let __proj__Mklift__item__lift_op: lift -> lift_op =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mdest = __fname__mdest;
        lift_op = __fname__lift_op;_} -> __fname__lift_op
type pragma =
  | SetOptions of Prims.string
  | ResetOptions of Prims.string FStar_Pervasives_Native.option
  | LightOff[@@deriving show]
let uu___is_SetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____2775 -> false
let __proj__SetOptions__item___0: pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____2789 -> false
let __proj__ResetOptions__item___0:
  pragma -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let uu___is_LightOff: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____2806 -> false
type decl' =
  | TopLevelModule of FStar_Ident.lid
  | Open of FStar_Ident.lid
  | Include of FStar_Ident.lid
  | ModuleAbbrev of (FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2
  | TopLevelLet of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Main of term
  | Tycon of
  (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Val of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
  | Exception of (FStar_Ident.ident,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | NewEffect of effect_decl
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
  | Assume of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2
[@@deriving show]
and decl =
  {
  d: decl';
  drange: FStar_Range.range;
  doc: fsdoc FStar_Pervasives_Native.option;
  quals: qualifiers;
  attrs: attributes_;}[@@deriving show]
and effect_decl =
  | DefineEffect of
  (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
  FStar_Pervasives_Native.tuple4
  | RedefineEffect of (FStar_Ident.ident,binder Prims.list,term)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_TopLevelModule: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____2957 -> false
let __proj__TopLevelModule__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0
let uu___is_Open: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____2969 -> false
let __proj__Open__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0
let uu___is_Include: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____2981 -> false
let __proj__Include__item___0: decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0
let uu___is_ModuleAbbrev: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____2997 -> false
let __proj__ModuleAbbrev__item___0:
  decl' -> (FStar_Ident.ident,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0
let uu___is_TopLevelLet: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____3031 -> false
let __proj__TopLevelLet__item___0:
  decl' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0
let uu___is_Main: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____3073 -> false
let __proj__Main__item___0: decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0
let uu___is_Tycon: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____3097 -> false
let __proj__Tycon__item___0:
  decl' ->
    (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tycon _0 -> _0
let uu___is_Val: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____3149 -> false
let __proj__Val__item___0:
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Val _0 -> _0
let uu___is_Exception: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____3179 -> false
let __proj__Exception__item___0:
  decl' ->
    (FStar_Ident.ident,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Exception _0 -> _0
let uu___is_NewEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____3209 -> false
let __proj__NewEffect__item___0: decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0
let uu___is_SubEffect: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____3221 -> false
let __proj__SubEffect__item___0: decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0
let uu___is_Pragma: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____3233 -> false
let __proj__Pragma__item___0: decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0
let uu___is_Fsdoc: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____3245 -> false
let __proj__Fsdoc__item___0: decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0
let uu___is_Assume: decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____3261 -> false
let __proj__Assume__item___0:
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assume _0 -> _0
let __proj__Mkdecl__item__d: decl -> decl' =
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__d
let __proj__Mkdecl__item__drange: decl -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__drange
let __proj__Mkdecl__item__doc: decl -> fsdoc FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__doc
let __proj__Mkdecl__item__quals: decl -> qualifiers =
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__quals
let __proj__Mkdecl__item__attrs: decl -> attributes_ =
  fun projectee  ->
    match projectee with
    | { d = __fname__d; drange = __fname__drange; doc = __fname__doc;
        quals = __fname__quals; attrs = __fname__attrs;_} -> __fname__attrs
let uu___is_DefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____3351 -> false
let __proj__DefineEffect__item___0:
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0
let uu___is_RedefineEffect: effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____3407 -> false
let __proj__RedefineEffect__item___0:
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid,decl Prims.list)
  FStar_Pervasives_Native.tuple2
  | Interface of (FStar_Ident.lid,decl Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Module: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3471 -> false
let __proj__Module__item___0:
  modul -> (FStar_Ident.lid,decl Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Interface: modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____3509 -> false
let __proj__Interface__item___0:
  modul ->
    (FStar_Ident.lid,decl Prims.list,Prims.bool)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Interface _0 -> _0
type file = modul[@@deriving show]
type inputFragment = (file,decl Prims.list) FStar_Util.either[@@deriving
                                                               show]
let decl_drange: decl -> FStar_Range.range = fun decl  -> decl.drange
let check_id: FStar_Ident.ident -> Prims.unit =
  fun id  ->
    let first_char =
      FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1") in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____3555 =
         let uu____3556 =
           let uu____3561 =
             FStar_Util.format1
               "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
               id.FStar_Ident.idText in
           (uu____3561, (id.FStar_Ident.idRange)) in
         FStar_Errors.Error uu____3556 in
       FStar_Exn.raise uu____3555)
let at_most_one:
  'Auu____3566 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____3566 Prims.list ->
          'Auu____3566 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____3586 ->
            let uu____3589 =
              let uu____3590 =
                let uu____3595 =
                  FStar_Util.format1
                    "At most one %s is allowed on declarations" s in
                (uu____3595, r) in
              FStar_Errors.Error uu____3590 in
            FStar_Exn.raise uu____3589
let mk_decl: decl' -> FStar_Range.range -> decoration Prims.list -> decl =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____3614 =
            FStar_List.choose
              (fun uu___103_3619  ->
                 match uu___103_3619 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____3623 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "fsdoc" r uu____3614 in
        let attributes_ =
          let uu____3629 =
            FStar_List.choose
              (fun uu___104_3638  ->
                 match uu___104_3638 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____3648 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu____3629 in
        let attributes_1 = FStar_Util.dflt [] attributes_ in
        let qualifiers =
          FStar_List.choose
            (fun uu___105_3663  ->
               match uu___105_3663 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____3667 -> FStar_Pervasives_Native.None) decorations in
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
                (s,FStar_Pervasives_Native.Some (FStar_Const.Signed ,width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.strcat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____3724 -> Op ((FStar_Ident.mk_ident ("-", rminus)), [t]) in
          mk_term t1 r l
let mk_pattern: pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r }
let un_curry_abs: pattern Prims.list -> term -> term' =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____3751 -> Abs (ps, body)
let mk_function:
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id () in FStar_Ident.gen r1 in
        let uu____3785 =
          let uu____3786 =
            let uu____3793 =
              let uu____3794 =
                let uu____3795 =
                  let uu____3810 =
                    let uu____3811 =
                      let uu____3812 = FStar_Ident.lid_of_ids [x] in
                      Var uu____3812 in
                    mk_term uu____3811 r1 Expr in
                  (uu____3810, branches) in
                Match uu____3795 in
              mk_term uu____3794 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____3793) in
          Abs uu____3786 in
        mk_term uu____3785 r2 Expr
let un_function:
  pattern ->
    term ->
      (pattern,term) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____3845,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____3864 -> FStar_Pervasives_Native.None
let lid_with_range:
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let uu____3879 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____3879 r
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
let mkApp:
  term ->
    (term,imp) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> term
  =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____4032 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____4046 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____4056  ->
                        match uu____4056 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
let mkRefSet: FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let uu____4073 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu____4073 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr in
          let addr_of1 =
            mk_term (Var (FStar_Ident.set_lid_range addr_of_lid r)) r Expr in
          let singleton1 =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr in
          let union1 =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp addr_of1 [(e, Nothing)] r in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
let mkExplicitApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____4139 ->
            (match t.tm with
             | Name s ->
                 let uu____4143 =
                   let uu____4144 =
                     let uu____4155 =
                       FStar_List.map (fun a  -> (a, Nothing)) args in
                     (s, uu____4155) in
                   Construct uu____4144 in
                 mk_term uu____4143 r Un
             | uu____4174 ->
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
let mkWildAdmitMagic:
  'Auu____4190 .
    FStar_Range.range ->
      (pattern,'Auu____4190 FStar_Pervasives_Native.option,term)
        FStar_Pervasives_Native.tuple3
  =
  fun r  ->
    let uu____4203 = mkAdmitMagic r in
    ((mk_pattern PatWild r), FStar_Pervasives_Native.None, uu____4203)
let focusBranches:
  'Auu____4209 .
    (Prims.bool,(pattern,'Auu____4209 FStar_Pervasives_Native.option,
                  term) FStar_Pervasives_Native.tuple3)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (pattern,'Auu____4209 FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun branches  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches in
      if should_filter
      then
        (FStar_Errors.warn r "Focusing on only some cases";
         (let focussed =
            let uu____4299 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu____4299
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu____4386 =
            let uu____4397 = mkWildAdmitMagic r in [uu____4397] in
          FStar_List.append focussed uu____4386))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings:
  'Auu____4486 .
    (Prims.bool,('Auu____4486,term) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        ('Auu____4486,term) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs in
      if should_filter
      then
        (FStar_Errors.warn r
           "Focusing on only some cases in this (mutually) recursive definition";
         FStar_List.map
           (fun uu____4556  ->
              match uu____4556 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____4584 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu____4584))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let mkFsTypApp: term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____4631 = FStar_List.map (fun a  -> (a, FsTypApp)) args in
        mkApp t uu____4631 r
let mkTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____4655 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____4655 r
let mkDTuple: term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____4679 = FStar_List.map (fun x  -> (x, Nothing)) args in
      mkApp (mk_term (Name cons1) r Expr) uu____4679 r
let mkRefinedBinder:
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> aqual -> binder
  =
  fun id  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id, t)) m Type_level implicit in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
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
        term FStar_Pervasives_Native.option ->
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
                | FStar_Pervasives_Native.None  -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____4744) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____4749 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____4753 =
                                 let uu____4754 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____4754 in
                               mk_term uu____4753 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu____4775 =
                                 let uu____4776 =
                                   let uu____4777 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____4777 in
                                 mk_term uu____4776 phi.range Formula in
                               ((mk_pattern PatWild phi.range),
                                 FStar_Pervasives_Native.None, uu____4775) in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level) in
              mk_pattern (PatAscribed (pat, t1)) range
let rec extract_named_refinement:
  term ->
    (FStar_Ident.ident,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____4853; blevel = uu____4854;
           aqual = uu____4855;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____4868 -> FStar_Pervasives_Native.None
let rec as_mlist:
  ((FStar_Ident.lid,decl) FStar_Pervasives_Native.tuple2,decl Prims.list)
    FStar_Pervasives_Native.tuple2 -> decl Prims.list -> modul
  =
  fun cur  ->
    fun ds  ->
      let uu____4907 = cur in
      match uu____4907 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Unexpected module declaration", (d.drange)))
                | uu____4936 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let as_frag:
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____4956 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu____4956 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____4993 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____4993 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in FStar_Util.Inl m1
             | uu____5004 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___106_5015  ->
                       match uu___106_5015 with
                       | { d = TopLevelModule uu____5016; drange = r;
                           doc = uu____5018; quals = uu____5019;
                           attrs = uu____5020;_} ->
                           FStar_Exn.raise
                             (FStar_Errors.Error
                                ("Unexpected module declaration", r))
                       | uu____5023 -> ()) ds2;
                  FStar_Util.Inr ds2))
let compile_op:
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___107_5038 =
          match uu___107_5038 with
          | 38 -> "Amp"
          | 64 -> "At"
          | 43 -> "Plus"
          | 45 when arity = (Prims.parse_int "1") -> "Minus"
          | 45 -> "Subtraction"
          | 126 -> "Tilde"
          | 47 -> "Slash"
          | 92 -> "Backslash"
          | 60 -> "Less"
          | 61 -> "Equals"
          | 62 -> "Greater"
          | 95 -> "Underscore"
          | 124 -> "Bar"
          | 33 -> "Bang"
          | 94 -> "Hat"
          | 37 -> "Percent"
          | 42 -> "Star"
          | 63 -> "Question"
          | 58 -> "Colon"
          | 36 -> "Dollar"
          | 46 -> "Dot"
          | c ->
              FStar_Exn.raise
                (FStar_Errors.Error
                   ((Prims.strcat "Unexpected operator symbol: '"
                       (Prims.strcat (FStar_Util.string_of_char c) "'")), r)) in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | uu____5040 ->
            let uu____5041 =
              let uu____5042 =
                let uu____5045 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu____5045 in
              FStar_String.concat "_" uu____5042 in
            Prims.strcat "op_" uu____5041
let compile_op': Prims.string -> FStar_Range.range -> Prims.string =
  fun s  -> fun r  -> compile_op (- (Prims.parse_int "1")) s r
let string_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____5066  ->
    match uu____5066 with
    | (comment,keywords) ->
        let uu____5091 =
          let uu____5092 =
            FStar_List.map
              (fun uu____5102  ->
                 match uu____5102 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords in
          FStar_String.concat "," uu____5092 in
        Prims.strcat comment uu____5091
let string_of_let_qualifier: let_qualifier -> Prims.string =
  fun uu___108_5111  ->
    match uu___108_5111 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
let to_string_l:
  'Auu____5116 .
    Prims.string ->
      ('Auu____5116 -> Prims.string) ->
        'Auu____5116 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____5138 = FStar_List.map f l in
        FStar_String.concat sep uu____5138
let imp_to_string: imp -> Prims.string =
  fun uu___109_5143  ->
    match uu___109_5143 with | Hash  -> "#" | uu____5144 -> ""
let rec term_to_string: term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____5155) ->
        let uu____5160 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____5160
    | Ensures (t,uu____5162) ->
        let uu____5167 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____5167
    | Labeled (t,l,uu____5170) ->
        let uu____5171 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____5171
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____5179 =
          let uu____5180 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs in
          FStar_String.concat ", " uu____5180 in
        FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____5179
    | Tvar id -> id.FStar_Ident.idText
    | Uvar id -> id.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____5203 =
          to_string_l " "
            (fun uu____5212  ->
               match uu____5212 with
               | (a,imp) ->
                   let uu____5219 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____5219)
            args in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____5203
    | Abs (pats,t) ->
        let uu____5226 = to_string_l " " pat_to_string pats in
        let uu____5227 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____5226 uu____5227
    | App (t1,t2,imp) ->
        let uu____5231 = FStar_All.pipe_right t1 term_to_string in
        let uu____5232 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____5231 (imp_to_string imp)
          uu____5232
    | Let (Rec ,lbs,body) ->
        let uu____5247 =
          to_string_l " and "
            (fun uu____5257  ->
               match uu____5257 with
               | (p,b) ->
                   let uu____5264 = FStar_All.pipe_right p pat_to_string in
                   let uu____5265 = FStar_All.pipe_right b term_to_string in
                   FStar_Util.format2 "%s=%s" uu____5264 uu____5265) lbs in
        let uu____5266 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format2 "let rec %s in %s" uu____5247 uu____5266
    | Let (q,(pat,tm)::[],body) ->
        let uu____5285 = FStar_All.pipe_right pat pat_to_string in
        let uu____5286 = FStar_All.pipe_right tm term_to_string in
        let uu____5287 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____5285 uu____5286 uu____5287
    | Seq (t1,t2) ->
        let uu____5290 = FStar_All.pipe_right t1 term_to_string in
        let uu____5291 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____5290 uu____5291
    | If (t1,t2,t3) ->
        let uu____5295 = FStar_All.pipe_right t1 term_to_string in
        let uu____5296 = FStar_All.pipe_right t2 term_to_string in
        let uu____5297 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____5295 uu____5296
          uu____5297
    | Match (t,branches) ->
        let uu____5320 = FStar_All.pipe_right t term_to_string in
        let uu____5321 =
          to_string_l " | "
            (fun uu____5337  ->
               match uu____5337 with
               | (p,w,e) ->
                   let uu____5353 = FStar_All.pipe_right p pat_to_string in
                   let uu____5354 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____5356 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____5356 in
                   let uu____5357 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____5353 uu____5354
                     uu____5357) branches in
        FStar_Util.format2 "match %s with %s" uu____5320 uu____5321
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____5362 = FStar_All.pipe_right t1 term_to_string in
        let uu____5363 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____5362 uu____5363
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____5369 = FStar_All.pipe_right t1 term_to_string in
        let uu____5370 = FStar_All.pipe_right t2 term_to_string in
        let uu____5371 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____5369 uu____5370 uu____5371
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____5388 = FStar_All.pipe_right e term_to_string in
        let uu____5389 =
          to_string_l " "
            (fun uu____5398  ->
               match uu____5398 with
               | (l,e1) ->
                   let uu____5405 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5405)
            fields in
        FStar_Util.format2 "{%s with %s}" uu____5388 uu____5389
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____5421 =
          to_string_l " "
            (fun uu____5430  ->
               match uu____5430 with
               | (l,e) ->
                   let uu____5437 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5437)
            fields in
        FStar_Util.format1 "{%s}" uu____5421
    | Project (e,l) ->
        let uu____5440 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format2 "%s.%s" uu____5440 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____5460 = FStar_All.pipe_right b binder_to_string in
        let uu____5461 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____5460 uu____5461
    | Product (b::[],t) when x.level = Kind ->
        let uu____5466 = FStar_All.pipe_right b binder_to_string in
        let uu____5467 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____5466 uu____5467
    | Sum (binders,t) ->
        let uu____5474 =
          let uu____5475 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____5475 (FStar_String.concat " * ") in
        let uu____5484 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s * %s" uu____5474 uu____5484
    | QForall (bs,pats,t) ->
        let uu____5500 = to_string_l " " binder_to_string bs in
        let uu____5501 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____5504 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____5500 uu____5501
          uu____5504
    | QExists (bs,pats,t) ->
        let uu____5520 = to_string_l " " binder_to_string bs in
        let uu____5521 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____5524 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____5520 uu____5521
          uu____5524
    | Refine (b,t) ->
        let uu____5527 = FStar_All.pipe_right b binder_to_string in
        let uu____5528 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____5527 uu____5528
    | NamedTyp (x1,t) ->
        let uu____5531 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____5531
    | Paren t ->
        let uu____5533 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____5533
    | Product (bs,t) ->
        let uu____5540 =
          let uu____5541 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____5541 (FStar_String.concat ",") in
        let uu____5550 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____5540
          uu____5550
    | t -> "_"
and binder_to_string: binder -> Prims.string =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____5558 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5558
      | Annotated (i,t) ->
          let uu____5561 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5561
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____5563 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____5563 s
and aqual_to_string: aqual -> Prims.string =
  fun uu___110_5564  ->
    match uu___110_5564 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____5565 -> ""
and pat_to_string: pattern -> Prims.string =
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____5574 = FStar_All.pipe_right p pat_to_string in
        let uu____5575 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____5574 uu____5575
    | PatTvar (i,aq) ->
        let uu____5582 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____5582 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____5589 = aqual_to_string aq in
        FStar_Util.format2 "%s%s" uu____5589 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____5594 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____5594
    | PatTuple (l,false ) ->
        let uu____5600 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____5600
    | PatTuple (l,true ) ->
        let uu____5606 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____5606
    | PatRecord l ->
        let uu____5614 =
          to_string_l "; "
            (fun uu____5623  ->
               match uu____5623 with
               | (f,e) ->
                   let uu____5630 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____5630) l in
        FStar_Util.format1 "{%s}" uu____5614
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op)
    | PatAscribed (p,t) ->
        let uu____5637 = FStar_All.pipe_right p pat_to_string in
        let uu____5638 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____5637 uu____5638
let rec head_id_of_pat: pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____5648) ->
        let uu____5653 = FStar_Ident.lid_of_ids [i] in [uu____5653]
    | PatApp (p1,uu____5655) -> head_id_of_pat p1
    | PatAscribed (p1,uu____5661) -> head_id_of_pat p1
    | uu____5662 -> []
let lids_of_let:
  'Auu____5665 .
    (pattern,'Auu____5665) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lid Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____5699  ->
            match uu____5699 with | (p,uu____5707) -> head_id_of_pat p))
let id_of_tycon: tycon -> Prims.string =
  fun uu___111_5710  ->
    match uu___111_5710 with
    | TyconAbstract (i,uu____5712,uu____5713) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____5723,uu____5724,uu____5725) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____5735,uu____5736,uu____5737) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____5767,uu____5768,uu____5769) ->
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
    | TopLevelLet (uu____5814,pats) ->
        let uu____5828 =
          let uu____5829 =
            let uu____5832 = lids_of_let pats in
            FStar_All.pipe_right uu____5832
              (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
          FStar_All.pipe_right uu____5829 (FStar_String.concat ", ") in
        Prims.strcat "let " uu____5828
    | Main uu____5843 -> "main ..."
    | Assume (i,uu____5845) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____5846,tys) ->
        let uu____5864 =
          let uu____5865 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____5887  ->
                    match uu____5887 with | (x,uu____5895) -> id_of_tycon x)) in
          FStar_All.pipe_right uu____5865 (FStar_String.concat ", ") in
        Prims.strcat "type " uu____5864
    | Val (i,uu____5903) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____5905) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____5911,uu____5912,uu____5913)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____5923,uu____5924)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | SubEffect uu____5929 -> "sub_effect"
    | Pragma uu____5930 -> "pragma"
    | Fsdoc uu____5931 -> "fsdoc"
let modul_to_string: modul -> Prims.string =
  fun m  ->
    match m with
    | Module (uu____5935,decls) ->
        let uu____5941 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____5941 (FStar_String.concat "\n")
    | Interface (uu____5950,decls,uu____5952) ->
        let uu____5957 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____5957 (FStar_String.concat "\n")
let error:
  'Auu____5970 . Prims.string -> term -> FStar_Range.range -> 'Auu____5970 =
  fun msg  ->
    fun tm  ->
      fun r  ->
        let tm1 = FStar_All.pipe_right tm term_to_string in
        let tm2 =
          if (FStar_String.length tm1) >= (Prims.parse_int "80")
          then
            let uu____5985 =
              FStar_Util.substring tm1 (Prims.parse_int "0")
                (Prims.parse_int "77") in
            Prims.strcat uu____5985 "..."
          else tm1 in
        FStar_Exn.raise
          (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm2)), r))