open Prims
type ident = {
  idText: Prims.string ;
  idRange: FStar_Compiler_Range.range }[@@deriving yojson,show,yojson,show]
let (__proj__Mkident__item__idText : ident -> Prims.string) =
  fun projectee -> match projectee with | { idText; idRange;_} -> idText
let (__proj__Mkident__item__idRange : ident -> FStar_Compiler_Range.range) =
  fun projectee -> match projectee with | { idText; idRange;_} -> idRange
type path = Prims.string Prims.list[@@deriving yojson,show]
type ipath = ident Prims.list[@@deriving yojson,show]
type lident =
  {
  ns: ipath ;
  ident: ident ;
  nsstr: Prims.string ;
  str: Prims.string }[@@deriving yojson,show,yojson,show]
let (__proj__Mklident__item__ns : lident -> ipath) =
  fun projectee ->
    match projectee with | { ns; ident = ident1; nsstr; str;_} -> ns
let (__proj__Mklident__item__ident : lident -> ident) =
  fun projectee ->
    match projectee with | { ns; ident = ident1; nsstr; str;_} -> ident1
let (__proj__Mklident__item__nsstr : lident -> Prims.string) =
  fun projectee ->
    match projectee with | { ns; ident = ident1; nsstr; str;_} -> nsstr
let (__proj__Mklident__item__str : lident -> Prims.string) =
  fun projectee ->
    match projectee with | { ns; ident = ident1; nsstr; str;_} -> str
let (mk_ident : (Prims.string * FStar_Compiler_Range.range) -> ident) =
  fun uu___ ->
    match uu___ with | (text, range) -> { idText = text; idRange = range }
let (set_id_range : FStar_Compiler_Range.range -> ident -> ident) =
  fun r -> fun i -> { idText = (i.idText); idRange = r }
let (reserved_prefix : Prims.string) = "uu___"
let (gen' : Prims.string -> FStar_Compiler_Range.range -> ident) =
  fun s ->
    fun r ->
      let i = FStar_GenSym.next_id () in
      mk_ident ((Prims.op_Hat s (Prims.string_of_int i)), r)
let (gen : FStar_Compiler_Range.range -> ident) =
  fun r -> gen' reserved_prefix r
let (ident_of_lid : lident -> ident) = fun l -> l.ident
let (range_of_id : ident -> FStar_Compiler_Range.range) =
  fun id -> id.idRange
let (id_of_text : Prims.string -> ident) =
  fun str -> mk_ident (str, FStar_Compiler_Range.dummyRange)
let (string_of_id : ident -> Prims.string) = fun id -> id.idText
let (text_of_path : path -> Prims.string) =
  fun path1 -> FStar_Compiler_Util.concat_l "." path1
let (path_of_text : Prims.string -> path) =
  fun text -> FStar_String.split [46] text
let (path_of_ns : ipath -> path) =
  fun ns -> FStar_Compiler_List.map string_of_id ns
let (path_of_lid : lident -> path) =
  fun lid ->
    FStar_Compiler_List.map string_of_id
      (FStar_Compiler_List.op_At lid.ns [lid.ident])
let (ns_of_lid : lident -> ipath) = fun lid -> lid.ns
let (ids_of_lid : lident -> ipath) =
  fun lid -> FStar_Compiler_List.op_At lid.ns [lid.ident]
let (lid_of_ns_and_id : ipath -> ident -> lident) =
  fun ns ->
    fun id ->
      let nsstr =
        let uu___ = FStar_Compiler_List.map string_of_id ns in
        FStar_Compiler_Effect.op_Bar_Greater uu___ text_of_path in
      {
        ns;
        ident = id;
        nsstr;
        str =
          (if nsstr = ""
           then id.idText
           else Prims.op_Hat nsstr (Prims.op_Hat "." id.idText))
      }
let (lid_of_ids : ipath -> lident) =
  fun ids ->
    let uu___ = FStar_Compiler_Util.prefix ids in
    match uu___ with | (ns, id) -> lid_of_ns_and_id ns id
let (lid_of_str : Prims.string -> lident) =
  fun str ->
    let uu___ =
      FStar_Compiler_List.map id_of_text (FStar_Compiler_Util.split str ".") in
    lid_of_ids uu___
let (lid_of_path : path -> FStar_Compiler_Range.range -> lident) =
  fun path1 ->
    fun pos ->
      let ids = FStar_Compiler_List.map (fun s -> mk_ident (s, pos)) path1 in
      lid_of_ids ids
let (text_of_lid : lident -> Prims.string) = fun lid -> lid.str
let (lid_equals : lident -> lident -> Prims.bool) =
  fun l1 -> fun l2 -> l1.str = l2.str
let (ident_equals : ident -> ident -> Prims.bool) =
  fun id1 -> fun id2 -> id1.idText = id2.idText
type lid = lident[@@deriving yojson,show]
let (range_of_lid : lident -> FStar_Compiler_Range.range) =
  fun lid1 -> range_of_id lid1.ident
let (set_lid_range : lident -> FStar_Compiler_Range.range -> lident) =
  fun l ->
    fun r ->
      {
        ns = (l.ns);
        ident =
          (let uu___ = l.ident in { idText = (uu___.idText); idRange = r });
        nsstr = (l.nsstr);
        str = (l.str)
      }
let (lid_add_suffix : lident -> Prims.string -> lident) =
  fun l ->
    fun s ->
      let path1 = path_of_lid l in
      let uu___ = range_of_lid l in
      lid_of_path (FStar_Compiler_List.op_At path1 [s]) uu___
let (ml_path_of_lid : lident -> Prims.string) =
  fun lid1 ->
    let uu___ =
      let uu___1 = path_of_ns lid1.ns in
      let uu___2 = let uu___3 = string_of_id lid1.ident in [uu___3] in
      FStar_Compiler_List.op_At uu___1 uu___2 in
    FStar_Compiler_Effect.op_Less_Bar (FStar_String.concat "_") uu___
let (string_of_lid : lident -> Prims.string) = fun lid1 -> lid1.str
let (qual_id : lident -> ident -> lident) =
  fun lid1 ->
    fun id ->
      let uu___ =
        lid_of_ids (FStar_Compiler_List.op_At lid1.ns [lid1.ident; id]) in
      let uu___1 = range_of_id id in set_lid_range uu___ uu___1
let (nsstr : lident -> Prims.string) = fun l -> l.nsstr