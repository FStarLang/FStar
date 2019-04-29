open Prims
type doc =
  | Doc of Prims.string 
let (uu___is_Doc : doc -> Prims.bool) = fun projectee -> true
let (__proj__Doc__item___0 : doc -> Prims.string) =
  fun projectee -> match projectee with | Doc _0 -> _0
let (empty : doc) = Doc ""
let (hardline : doc) = Doc "\n"
let (text : Prims.string -> doc) = fun s -> Doc s
let (num : Prims.int -> doc) = fun i -> Doc (Prims.string_of_int i)
let (break_ : Prims.int -> doc) = fun i -> Doc ""
let (break0 : doc) = break_ (Prims.parse_int "0")
let (break1 : doc) = text " "
let (enclose : doc -> doc -> doc -> doc) =
  fun uu____70 ->
    fun uu____71 ->
      fun uu____72 ->
        match (uu____70, uu____71, uu____72) with
        | (Doc l, Doc r, Doc x) -> Doc (Prims.op_Hat l (Prims.op_Hat x r))
let (brackets : doc -> doc) =
  fun uu____84 ->
    match uu____84 with | Doc d -> enclose (text "[") (text "]") (Doc d)
let (cbrackets : doc -> doc) =
  fun uu____94 ->
    match uu____94 with | Doc d -> enclose (text "{") (text "}") (Doc d)
let (parens : doc -> doc) =
  fun uu____104 ->
    match uu____104 with | Doc d -> enclose (text "(") (text ")") (Doc d)
let (cat : doc -> doc -> doc) =
  fun uu____118 ->
    fun uu____119 ->
      match (uu____118, uu____119) with
      | (Doc d1, Doc d2) -> Doc (Prims.op_Hat d1 d2)
let (reduce : doc Prims.list -> doc) =
  fun docs -> FStar_List.fold_left cat empty docs
let (group : doc -> doc) =
  fun uu____139 -> match uu____139 with | Doc d -> Doc d
let (groups : doc Prims.list -> doc) =
  fun docs -> let uu____152 = reduce docs in group uu____152
let (combine : doc -> doc Prims.list -> doc) =
  fun uu____164 ->
    fun docs ->
      match uu____164 with
      | Doc sep ->
          let select uu____178 =
            match uu____178 with
            | Doc d ->
                if d = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d in
          let docs1 = FStar_List.choose select docs in
          Doc (FStar_String.concat sep docs1)
let (cat1 : doc -> doc -> doc) = fun d1 -> fun d2 -> reduce [d1; break1; d2]
let (reduce1 : doc Prims.list -> doc) = fun docs -> combine break1 docs
let (nest : Prims.int -> doc -> doc) =
  fun i -> fun uu____231 -> match uu____231 with | Doc d -> Doc d
let (align : doc Prims.list -> doc) =
  fun docs ->
    let uu____245 = combine hardline docs in
    match uu____245 with | Doc doc -> Doc doc
let (hbox : doc -> doc) = fun d -> d
let (pretty : Prims.int -> doc -> Prims.string) =
  fun sz -> fun uu____266 -> match uu____266 with | Doc doc -> doc