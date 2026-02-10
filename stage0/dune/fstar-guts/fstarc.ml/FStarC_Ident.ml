open Prims
type ident = {
  idText: Prims.string ;
  idRange: FStarC_Range_Type.range }[@@deriving yojson,show]
let __proj__Mkident__item__idText (projectee : ident) : Prims.string=
  match projectee with | { idText; idRange;_} -> idText
let __proj__Mkident__item__idRange (projectee : ident) :
  FStarC_Range_Type.range=
  match projectee with | { idText; idRange;_} -> idRange
type path = Prims.string Prims.list[@@deriving yojson,show]
type ipath = ident Prims.list[@@deriving yojson,show]
type lident =
  {
  ns: ipath ;
  ident: ident ;
  nsstr: Prims.string ;
  str: Prims.string }[@@deriving yojson,show]
let __proj__Mklident__item__ns (projectee : lident) : ipath=
  match projectee with | { ns; ident = ident1; nsstr; str;_} -> ns
let __proj__Mklident__item__ident (projectee : lident) : ident=
  match projectee with | { ns; ident = ident1; nsstr; str;_} -> ident1
let __proj__Mklident__item__nsstr (projectee : lident) : Prims.string=
  match projectee with | { ns; ident = ident1; nsstr; str;_} -> nsstr
let __proj__Mklident__item__str (projectee : lident) : Prims.string=
  match projectee with | { ns; ident = ident1; nsstr; str;_} -> str
let mk_ident (uu___ : (Prims.string * FStarC_Range_Type.range)) : ident=
  match uu___ with | (text, range) -> { idText = text; idRange = range }
let set_id_range (r : FStarC_Range_Type.range) (i : ident) : ident=
  { idText = (i.idText); idRange = r }
let reserved_prefix : Prims.string= "uu___"
let gen' (s : Prims.string) (r : FStarC_Range_Type.range) : ident=
  let i = FStarC_GenSym.next_id () in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      Prims.strcat s uu___2 in
    (uu___1, r) in
  mk_ident uu___
let gen (r : FStarC_Range_Type.range) : ident= gen' reserved_prefix r
let ident_of_lid (l : lident) : ident= l.ident
let range_of_id (id : ident) : FStarC_Range_Type.range= id.idRange
let id_of_text (str : Prims.string) : ident=
  mk_ident (str, FStarC_Range_Type.dummyRange)
let string_of_id (id : ident) : Prims.string= id.idText
let text_of_path (path1 : path) : Prims.string=
  FStarC_Util.concat_l "." path1
let path_of_text (text : Prims.string) : path= FStarC_String.split [46] text
let path_of_ns (ns : ipath) : path= FStarC_List.map string_of_id ns
let path_of_lid (lid : lident) : path=
  FStarC_List.map string_of_id (FStarC_List.op_At lid.ns [lid.ident])
let ns_of_lid (lid : lident) : ipath= lid.ns
let ids_of_lid (lid : lident) : ipath= FStarC_List.op_At lid.ns [lid.ident]
let lid_of_ns_and_id (ns : ipath) (id : ident) : lident=
  let nsstr =
    let uu___ = FStarC_List.map string_of_id ns in text_of_path uu___ in
  {
    ns;
    ident = id;
    nsstr;
    str =
      (if nsstr = ""
       then id.idText
       else Prims.strcat nsstr (Prims.strcat "." id.idText))
  }
let id_as_lid (id : ident) : lident= lid_of_ns_and_id [] id
let lid_of_ids (ids : ipath) : lident=
  let uu___ = FStarC_Util.prefix ids in
  match uu___ with | (ns, id) -> lid_of_ns_and_id ns id
let lid_of_str (str : Prims.string) : lident=
  let uu___ = FStarC_List.map id_of_text (FStarC_Util.split str ".") in
  lid_of_ids uu___
let lid_of_path (path1 : path) (pos : FStarC_Range_Type.range) : lident=
  let ids = FStarC_List.map (fun s -> mk_ident (s, pos)) path1 in
  lid_of_ids ids
let text_of_lid (lid : lident) : Prims.string= lid.str
let lid_equals (l1 : lident) (l2 : lident) : Prims.bool= l1.str = l2.str
let ident_equals (id1 : ident) (id2 : ident) : Prims.bool=
  id1.idText = id2.idText
type lid = lident[@@deriving yojson,show]
let range_of_lid (lid1 : lid) : FStarC_Range_Type.range=
  range_of_id lid1.ident
let set_lid_range (l : lident) (r : FStarC_Range_Type.range) : lident=
  {
    ns = (l.ns);
    ident = (let uu___ = l.ident in { idText = (uu___.idText); idRange = r });
    nsstr = (l.nsstr);
    str = (l.str)
  }
let lid_add_suffix (l : lident) (s : Prims.string) : lident=
  let path1 = path_of_lid l in
  let uu___ = range_of_lid l in
  lid_of_path (FStarC_List.op_At path1 [s]) uu___
let ml_path_of_lid (lid1 : lident) : Prims.string=
  let uu___ =
    let uu___1 = path_of_ns lid1.ns in
    let uu___2 = let uu___3 = string_of_id lid1.ident in [uu___3] in
    FStarC_List.op_At uu___1 uu___2 in
  FStarC_String.concat "_" uu___
let string_of_lid (lid1 : lident) : Prims.string= lid1.str
let qual_id (lid1 : lident) (id : ident) : lident=
  let uu___ = lid_of_ids (FStarC_List.op_At lid1.ns [lid1.ident; id]) in
  let uu___1 = range_of_id id in set_lid_range uu___ uu___1
let nsstr (l : lid) : Prims.string= l.nsstr
let showable_ident : ident FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_id }
let showable_lident : lident FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_lid }
let pretty_ident : ident FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_ident
let pretty_lident : lident FStarC_Class_PP.pretty=
  FStarC_Class_PP.pretty_from_showable showable_lident
let hasrange_ident : ident FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos = range_of_id;
    FStarC_Class_HasRange.setPos =
      (fun rng id -> { idText = (id.idText); idRange = rng })
  }
let hasrange_lident : lident FStarC_Class_HasRange.hasRange=
  {
    FStarC_Class_HasRange.pos =
      (fun lid1 -> FStarC_Class_HasRange.pos hasrange_ident lid1.ident);
    FStarC_Class_HasRange.setPos =
      (fun rng id ->
         let uu___ = FStarC_Class_HasRange.setPos hasrange_ident rng id.ident in
         { ns = (id.ns); ident = uu___; nsstr = (id.nsstr); str = (id.str) })
  }
let deq_ident : ident FStarC_Class_Deq.deq=
  { FStarC_Class_Deq.op_Equals_Question = ident_equals }
let deq_lident : lident FStarC_Class_Deq.deq=
  { FStarC_Class_Deq.op_Equals_Question = lid_equals }
let ord_ident : ident FStarC_Class_Ord.ord=
  {
    FStarC_Class_Ord.super = deq_ident;
    FStarC_Class_Ord.cmp =
      (fun x y ->
         let uu___ = string_of_id x in
         let uu___1 = string_of_id y in
         FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_string uu___ uu___1)
  }
let ord_lident : lident FStarC_Class_Ord.ord=
  {
    FStarC_Class_Ord.super = deq_lident;
    FStarC_Class_Ord.cmp =
      (fun x y ->
         let uu___ = string_of_lid x in
         let uu___1 = string_of_lid y in
         FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_string uu___ uu___1)
  }
