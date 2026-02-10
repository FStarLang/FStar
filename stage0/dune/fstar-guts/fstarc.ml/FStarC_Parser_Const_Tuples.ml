open Prims
let tuple_table : (Prims.int * Prims.string * Prims.string) Prims.list=
  [((Prims.of_int (2)), "FStar.Pervasives.Native.tuple2",
     "FStar.Pervasives.Native.Mktuple2");
  ((Prims.of_int (3)), "FStar.Pervasives.Native.tuple3",
    "FStar.Pervasives.Native.Mktuple3");
  ((Prims.of_int (4)), "FStar.Pervasives.Native.tuple4",
    "FStar.Pervasives.Native.Mktuple4");
  ((Prims.of_int (5)), "FStar.Pervasives.Native.tuple5",
    "FStar.Pervasives.Native.Mktuple5");
  ((Prims.of_int (6)), "FStar.Pervasives.Native.tuple6",
    "FStar.Pervasives.Native.Mktuple6");
  ((Prims.of_int (7)), "FStar.Pervasives.Native.tuple7",
    "FStar.Pervasives.Native.Mktuple7");
  ((Prims.of_int (8)), "FStar.Pervasives.Native.tuple8",
    "FStar.Pervasives.Native.Mktuple8");
  ((Prims.of_int (9)), "FStar.Pervasives.Native.tuple9",
    "FStar.Pervasives.Native.Mktuple9");
  ((Prims.of_int (10)), "FStar.Pervasives.Native.tuple10",
    "FStar.Pervasives.Native.Mktuple10");
  ((Prims.of_int (11)), "FStar.Pervasives.Native.tuple11",
    "FStar.Pervasives.Native.Mktuple11");
  ((Prims.of_int (12)), "FStar.Pervasives.Native.tuple12",
    "FStar.Pervasives.Native.Mktuple12");
  ((Prims.of_int (13)), "FStar.Pervasives.Native.tuple13",
    "FStar.Pervasives.Native.Mktuple13");
  ((Prims.of_int (14)), "FStar.Pervasives.Native.tuple14",
    "FStar.Pervasives.Native.Mktuple14")]
let lookup_tuple (n : Prims.int) : (Prims.int * Prims.string * Prims.string)=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (n', uu___2, uu___3) -> n = n')
      tuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
        Prims.strcat "Tuple too large: " uu___2 in
      failwith uu___1
let mk_tuple_lid (n : Prims.int) (r : FStarC_Range_Type.range) :
  FStarC_Ident.lid=
  let uu___ = lookup_tuple n in
  match uu___ with
  | (uu___1, s, uu___2) ->
      let l = FStarC_Ident.lid_of_str s in FStarC_Ident.set_lid_range l r
let mk_tuple_data_lid (n : Prims.int) (r : FStarC_Range_Type.range) :
  FStarC_Ident.lid=
  let uu___ = lookup_tuple n in
  match uu___ with
  | (uu___1, uu___2, s) ->
      let l = FStarC_Ident.lid_of_str s in FStarC_Ident.set_lid_range l r
let get_tuple_datacon_arity (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (uu___2, uu___3, s') -> s = s')
      tuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some (n, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some n
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let get_tuple_tycon_arity (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (uu___2, s', uu___3) -> s = s')
      tuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some (n, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some n
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let is_tuple_constructor_string (s : Prims.string) : Prims.bool=
  FStarC_List.existsb
    (fun uu___ -> match uu___ with | (uu___1, s', uu___2) -> s = s')
    tuple_table
let is_tuple_datacon_string (s : Prims.string) : Prims.bool=
  FStarC_List.existsb
    (fun uu___ -> match uu___ with | (n, uu___1, s') -> s = s') tuple_table
let is_tuple_constructor_lid (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_Ident.string_of_lid lid in
  is_tuple_constructor_string uu___
let is_tuple_datacon_lid (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_Ident.string_of_lid lid in is_tuple_datacon_string uu___
let is_tuple_data_lid (f : FStarC_Ident.lident) (n : Prims.int) : Prims.bool=
  let uu___ = mk_tuple_data_lid n FStarC_Range_Type.dummyRange in
  FStarC_Ident.lid_equals f uu___
let dtuple_table : (Prims.int * Prims.string * Prims.string) Prims.list=
  [((Prims.of_int (2)), "Prims.dtuple2", "Prims.Mkdtuple2");
  ((Prims.of_int (3)), "FStar.Pervasives.dtuple3",
    "FStar.Pervasives.Mkdtuple3");
  ((Prims.of_int (4)), "FStar.Pervasives.dtuple4",
    "FStar.Pervasives.Mkdtuple4");
  ((Prims.of_int (5)), "FStar.Pervasives.dtuple5",
    "FStar.Pervasives.Mkdtuple5")]
let lookup_dtuple (n : Prims.int) :
  (Prims.int * Prims.string * Prims.string)=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (n', uu___2, uu___3) -> n = n')
      dtuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
        Prims.strcat "DTuple too large: " uu___2 in
      failwith uu___1
let mk_dtuple_lid (n : Prims.int) (r : FStarC_Range_Type.range) :
  FStarC_Ident.lid=
  let uu___ = lookup_dtuple n in
  match uu___ with
  | (uu___1, s, uu___2) ->
      let l = FStarC_Ident.lid_of_str s in FStarC_Ident.set_lid_range l r
let mk_dtuple_data_lid (n : Prims.int) (r : FStarC_Range_Type.range) :
  FStarC_Ident.lid=
  let uu___ = lookup_dtuple n in
  match uu___ with
  | (uu___1, uu___2, s) ->
      let l = FStarC_Ident.lid_of_str s in FStarC_Ident.set_lid_range l r
let get_dtuple_datacon_arity (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (uu___2, uu___3, s') -> s = s')
      dtuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some (n, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some n
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let get_dtuple_tycon_arity (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (uu___2, s', uu___3) -> s = s')
      dtuple_table in
  match uu___ with
  | FStar_Pervasives_Native.Some (n, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some n
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let is_dtuple_constructor_string (s : Prims.string) : Prims.bool=
  FStarC_List.existsb
    (fun uu___ -> match uu___ with | (uu___1, s', uu___2) -> s = s')
    dtuple_table
let is_dtuple_datacon_string (s : Prims.string) : Prims.bool=
  FStarC_List.existsb
    (fun uu___ -> match uu___ with | (uu___1, uu___2, s') -> s = s')
    dtuple_table
let is_dtuple_constructor_lid (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_Ident.string_of_lid lid in
  is_dtuple_constructor_string uu___
let is_dtuple_data_lid (f : FStarC_Ident.lident) (n : Prims.int) :
  Prims.bool=
  let uu___ = mk_dtuple_data_lid n FStarC_Range_Type.dummyRange in
  FStarC_Ident.lid_equals f uu___
let is_dtuple_datacon_lid (f : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_Ident.string_of_lid f in is_dtuple_datacon_string uu___
let lid_tuple2 : FStarC_Ident.lident=
  mk_tuple_lid (Prims.of_int (2)) FStarC_Range_Type.dummyRange
let lid_tuple3 : FStarC_Ident.lident=
  mk_tuple_lid (Prims.of_int (3)) FStarC_Range_Type.dummyRange
let lid_tuple4 : FStarC_Ident.lident=
  mk_tuple_lid (Prims.of_int (4)) FStarC_Range_Type.dummyRange
let lid_tuple5 : FStarC_Ident.lident=
  mk_tuple_lid (Prims.of_int (5)) FStarC_Range_Type.dummyRange
let lid_Mktuple2 : FStarC_Ident.lident=
  mk_tuple_data_lid (Prims.of_int (2)) FStarC_Range_Type.dummyRange
let lid_Mktuple3 : FStarC_Ident.lident=
  mk_tuple_data_lid (Prims.of_int (3)) FStarC_Range_Type.dummyRange
let lid_Mktuple4 : FStarC_Ident.lident=
  mk_tuple_data_lid (Prims.of_int (4)) FStarC_Range_Type.dummyRange
let lid_Mktuple5 : FStarC_Ident.lident=
  mk_tuple_data_lid (Prims.of_int (5)) FStarC_Range_Type.dummyRange
let lid_dtuple2 : FStarC_Ident.lident=
  mk_dtuple_lid (Prims.of_int (2)) FStarC_Range_Type.dummyRange
