open Prims
type doc =
  | Doc of Prims.string[@@deriving show]
let uu___is_Doc: doc -> Prims.bool = fun projectee  -> true
let __proj__Doc__item___0: doc -> Prims.string =
  fun projectee  -> match projectee with | Doc _0 -> _0
let empty: doc = Doc ""
let hardline: doc = Doc "\n"
let text: Prims.string -> doc = fun s  -> Doc s
let num: Prims.int -> doc = fun i  -> Doc (Prims.string_of_int i)
let break_: Prims.int -> doc = fun i  -> Doc ""
let break0: doc = break_ (Prims.parse_int "0")
let break1: doc = text " "
let enclose: doc -> doc -> doc -> doc =
  fun uu____27  ->
    fun uu____28  ->
      fun uu____29  ->
        match (uu____27, uu____28, uu____29) with
        | (Doc l,Doc r,Doc x) -> Doc (Prims.strcat l (Prims.strcat x r))
let brackets: doc -> doc =
  fun uu____35  ->
    match uu____35 with | Doc d -> enclose (text "[") (text "]") (Doc d)
let cbrackets: doc -> doc =
  fun uu____39  ->
    match uu____39 with | Doc d -> enclose (text "{") (text "}") (Doc d)
let parens: doc -> doc =
  fun uu____43  ->
    match uu____43 with | Doc d -> enclose (text "(") (text ")") (Doc d)
let cat: doc -> doc -> doc =
  fun uu____49  ->
    fun uu____50  ->
      match (uu____49, uu____50) with
      | (Doc d1,Doc d2) -> Doc (Prims.strcat d1 d2)
let reduce: doc Prims.list -> doc =
  fun docs  -> FStar_List.fold_left cat empty docs
let group: doc -> doc = fun uu____62  -> match uu____62 with | Doc d -> Doc d
let groups: doc Prims.list -> doc =
  fun docs  -> let uu____71 = reduce docs in group uu____71
let combine: doc -> doc Prims.list -> doc =
  fun uu____78  ->
    fun docs  ->
      match uu____78 with
      | Doc sep ->
          let select uu____88 =
            match uu____88 with
            | Doc d ->
                if d = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d in
          let docs1 = FStar_List.choose select docs in
          Doc (FStar_String.concat sep docs1)
let cat1: doc -> doc -> doc = fun d1  -> fun d2  -> reduce [d1; break1; d2]
let reduce1: doc Prims.list -> doc = fun docs  -> combine break1 docs
let nest: Prims.int -> doc -> doc =
  fun i  -> fun uu____116  -> match uu____116 with | Doc d -> Doc d
let align: doc Prims.list -> doc =
  fun docs  ->
    let uu____125 = combine hardline docs in
    match uu____125 with | Doc doc1 -> Doc doc1
let hbox: doc -> doc = fun d  -> d
let pretty: Prims.int -> doc -> Prims.string =
  fun sz  -> fun uu____135  -> match uu____135 with | Doc doc1 -> doc1