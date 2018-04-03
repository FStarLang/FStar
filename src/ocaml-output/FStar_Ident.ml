open Prims
type ident = {
  idText: Prims.string ;
  idRange: FStar_Range.range }[@@deriving show]
let (__proj__Mkident__item__idText : ident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { idText = __fname__idText; idRange = __fname__idRange;_} ->
        __fname__idText
  
let (__proj__Mkident__item__idRange : ident -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { idText = __fname__idText; idRange = __fname__idRange;_} ->
        __fname__idRange
  
type path = Prims.string Prims.list[@@deriving show]
type lident =
  {
  ns: ident Prims.list ;
  ident: ident ;
  nsstr: Prims.string ;
  str: Prims.string }[@@deriving show]
let (__proj__Mklident__item__ns : lident -> ident Prims.list) =
  fun projectee  ->
    match projectee with
    | { ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr;
        str = __fname__str;_} -> __fname__ns
  
let (__proj__Mklident__item__ident : lident -> ident) =
  fun projectee  ->
    match projectee with
    | { ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr;
        str = __fname__str;_} -> __fname__ident
  
let (__proj__Mklident__item__nsstr : lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr;
        str = __fname__str;_} -> __fname__nsstr
  
let (__proj__Mklident__item__str : lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr;
        str = __fname__str;_} -> __fname__str
  
type lid = lident[@@deriving show]
let (mk_ident :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 -> ident) =
  fun uu____85  ->
    match uu____85 with | (text,range) -> { idText = text; idRange = range }
  
let (reserved_prefix : Prims.string) = "uu___" 
let (_gen : FStar_Range.range -> ident) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun r  ->
    (let uu____99 =
       let uu____100 = FStar_ST.op_Bang x  in
       uu____100 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals x uu____99);
    (let uu____183 =
       let uu____188 =
         let uu____189 =
           let uu____190 = FStar_ST.op_Bang x  in
           Prims.string_of_int uu____190  in
         Prims.strcat reserved_prefix uu____189  in
       (uu____188, r)  in
     mk_ident uu____183)
  
let (gen : FStar_Range.range -> ident) = fun r  -> _gen r 
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
        let uu____276 = FStar_List.map text_of_id ns  in
        FStar_All.pipe_right uu____276 text_of_path  in
      {
        ns;
        ident = id1;
        nsstr;
        str =
          (if nsstr = ""
           then id1.idText
           else Prims.strcat nsstr (Prims.strcat "." id1.idText))
      }
  
let (lid_of_ids : ident Prims.list -> lident) =
  fun ids  ->
    let uu____289 = FStar_Util.prefix ids  in
    match uu____289 with | (ns,id1) -> lid_of_ns_and_id ns id1
  
let (lid_of_str : Prims.string -> lident) =
  fun str  ->
    let uu____305 = FStar_List.map id_of_text (FStar_Util.split str ".")  in
    lid_of_ids uu____305
  
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
  fun lid  -> (lid.ident).idRange 
let (set_lid_range : lident -> FStar_Range.range -> lident) =
  fun l  ->
    fun r  ->
      let uu___25_343 = l  in
      {
        ns = (uu___25_343.ns);
        ident =
          (let uu___26_345 = l.ident  in
           { idText = (uu___26_345.idText); idRange = r });
        nsstr = (uu___25_343.nsstr);
        str = (uu___25_343.str)
      }
  
let (lid_add_suffix : lident -> Prims.string -> lident) =
  fun l  ->
    fun s  ->
      let path = path_of_lid l  in
      let uu____353 = range_of_lid l  in
      lid_of_path (FStar_List.append path [s]) uu____353
  
let (ml_path_of_lid : lident -> Prims.string) =
  fun lid  ->
    let uu____357 =
      let uu____360 = path_of_ns lid.ns  in
      let uu____363 = let uu____366 = text_of_id lid.ident  in [uu____366]
         in
      FStar_List.append uu____360 uu____363  in
    FStar_All.pipe_left (FStar_String.concat "_") uu____357
  
let (string_of_ident : ident -> Prims.string) = fun id1  -> id1.idText 
let (string_of_lid : lident -> Prims.string) =
  fun lid  -> let uu____375 = path_of_lid lid  in text_of_path uu____375 