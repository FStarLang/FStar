open Prims
type ident = {
  idText: Prims.string ;
  idRange: FStar_Range.range }[@@deriving yojson,show]
let (__proj__Mkident__item__idText : ident -> Prims.string) =
  fun projectee  -> match projectee with | { idText; idRange;_} -> idText 
let (__proj__Mkident__item__idRange : ident -> FStar_Range.range) =
  fun projectee  -> match projectee with | { idText; idRange;_} -> idRange 
type path = Prims.string Prims.list
type lident =
  {
  ns: ident Prims.list ;
  ident: ident ;
  nsstr: Prims.string ;
  str: Prims.string }[@@deriving yojson,show]
let (__proj__Mklident__item__ns : lident -> ident Prims.list) =
  fun projectee  -> match projectee with | { ns; ident; nsstr; str;_} -> ns 
let (__proj__Mklident__item__ident : lident -> ident) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str;_} -> ident
  
let (__proj__Mklident__item__nsstr : lident -> Prims.string) =
  fun projectee  ->
    match projectee with | { ns; ident; nsstr; str;_} -> nsstr
  
let (__proj__Mklident__item__str : lident -> Prims.string) =
  fun projectee  -> match projectee with | { ns; ident; nsstr; str;_} -> str 
type lid = lident[@@deriving yojson,show]
let (mk_ident : (Prims.string * FStar_Range.range) -> ident) =
  fun uu____132  ->
    match uu____132 with | (text,range) -> { idText = text; idRange = range }
  
let (reserved_prefix : Prims.string) = "uu___" 
let (_gen : FStar_Range.range -> ident) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun r  ->
    (let uu____158 =
       let uu____160 = FStar_ST.op_Bang x  in
       uu____160 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals x uu____158);
    (let uu____249 =
       let uu____255 =
         let uu____257 =
           let uu____259 = FStar_ST.op_Bang x  in
           Prims.string_of_int uu____259  in
         Prims.op_Hat reserved_prefix uu____257  in
       (uu____255, r)  in
     mk_ident uu____249)
  
let (gen : FStar_Range.range -> ident) = fun r  -> _gen r 
let (range_of_id : ident -> FStar_Range.range) = fun id1  -> id1.idRange 
let (id_of_text : Prims.string -> ident) =
  fun str  -> mk_ident (str, FStar_Range.dummyRange) 
let (text_of_id : ident -> Prims.string) = fun id1  -> id1.idText 
let (text_of_path : path -> Prims.string) =
  fun path  -> FStar_Util.concat_l "." path 
let (path_of_text : Prims.string -> path) =
  fun text  -> FStar_String.split [46] text 
let (path_of_ns : ident Prims.list -> path) =
  fun ns  -> FStar_List.map text_of_id ns 
let (path_of_lid : lident -> path) =
  fun lid  ->
    FStar_List.map text_of_id (FStar_List.append lid.ns [lid.ident])
  
let (ids_of_lid : lident -> ident Prims.list) =
  fun lid  -> FStar_List.append lid.ns [lid.ident] 
let (lid_of_ns_and_id : ident Prims.list -> ident -> lident) =
  fun ns  ->
    fun id1  ->
      let nsstr =
        let uu____395 = FStar_List.map text_of_id ns  in
        FStar_All.pipe_right uu____395 text_of_path  in
      {
        ns;
        ident = id1;
        nsstr;
        str =
          (if nsstr = ""
           then id1.idText
           else Prims.op_Hat nsstr (Prims.op_Hat "." id1.idText))
      }
  
let (lid_of_ids : ident Prims.list -> lident) =
  fun ids  ->
    let uu____415 = FStar_Util.prefix ids  in
    match uu____415 with | (ns,id1) -> lid_of_ns_and_id ns id1
  
let (lid_of_str : Prims.string -> lident) =
  fun str  ->
    let uu____436 = FStar_List.map id_of_text (FStar_Util.split str ".")  in
    lid_of_ids uu____436
  
let (lid_of_path : path -> FStar_Range.range -> lident) =
  fun path  ->
    fun pos  ->
      let ids = FStar_List.map (fun s  -> mk_ident (s, pos)) path  in
      lid_of_ids ids
  
let (text_of_lid : lident -> Prims.string) = fun lid  -> lid.str 
let (lid_equals : lident -> lident -> Prims.bool) =
  fun l1  -> fun l2  -> l1.str = l2.str 
let (ident_equals : ident -> ident -> Prims.bool) =
  fun id1  -> fun id2  -> id1.idText = id2.idText 
let (range_of_lid : lident -> FStar_Range.range) =
  fun lid  -> range_of_id lid.ident 
let (set_lid_range : lident -> FStar_Range.range -> lident) =
  fun l  ->
    fun r  ->
      let uu___21_510 = l  in
      {
        ns = (uu___21_510.ns);
        ident =
          (let uu___22_512 = l.ident  in
           { idText = (uu___22_512.idText); idRange = r });
        nsstr = (uu___21_510.nsstr);
        str = (uu___21_510.str)
      }
  
let (lid_add_suffix : lident -> Prims.string -> lident) =
  fun l  ->
    fun s  ->
      let path = path_of_lid l  in
      let uu____527 = range_of_lid l  in
      lid_of_path (FStar_List.append path [s]) uu____527
  
let (ml_path_of_lid : lident -> Prims.string) =
  fun lid  ->
    let uu____538 =
      let uu____542 = path_of_ns lid.ns  in
      let uu____546 = let uu____550 = text_of_id lid.ident  in [uu____550]
         in
      FStar_List.append uu____542 uu____546  in
    FStar_All.pipe_left (FStar_String.concat "_") uu____538
  
let (string_of_ident : ident -> Prims.string) = fun id1  -> id1.idText 
let (string_of_lid : lident -> Prims.string) =
  fun lid  -> let uu____574 = path_of_lid lid  in text_of_path uu____574 