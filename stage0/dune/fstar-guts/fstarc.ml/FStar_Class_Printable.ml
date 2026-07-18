open Prims
type 'a printable = {
  to_string: 'a -> Prims.string }
let __proj__Mkprintable__item__to_string (projectee : 'a printable) :
  'a -> Prims.string= match projectee with | { to_string;_} -> to_string
let to_string (projectee : 'a printable) : 'a -> Prims.string=
  __proj__Mkprintable__item__to_string projectee
let printable_unit : unit printable= { to_string = (fun uu___ -> "()") }
let printable_bool : Prims.bool printable=
  { to_string = Prims.string_of_bool }
let printable_nat : Prims.nat printable= { to_string = Prims.string_of_int }
let printable_int : Prims.int printable= { to_string = Prims.string_of_int }
let printable_ref (p : unit) (d : 'a printable) : 'a printable=
  { to_string = (d.to_string) }
let printable_list (x : 'a printable) : 'a Prims.list printable=
  {
    to_string =
      (fun l ->
         Prims.strcat "["
           (Prims.strcat
              (FStar_String.concat "; "
                 (FStar_List_Tot_Base.map (to_string x) l)) "]"))
  }
let printable_string : Prims.string printable=
  { to_string = (fun x -> Prims.strcat "\"" (Prims.strcat x "\"")) }
let printable_option (uu___ : 'a printable) :
  'a FStar_Pervasives_Native.option printable=
  {
    to_string =
      (fun uu___1 ->
         match uu___1 with
         | FStar_Pervasives_Native.None -> "None"
         | FStar_Pervasives_Native.Some x ->
             Prims.strcat "(Some " (Prims.strcat (to_string uu___ x) ")"))
  }
let printable_either (uu___ : 'a printable) (uu___1 : 'b printable) :
  ('a, 'b) FStar_Pervasives.either printable=
  {
    to_string =
      (fun uu___2 ->
         match uu___2 with
         | FStar_Pervasives.Inl x ->
             Prims.strcat "(Inl " (Prims.strcat (to_string uu___ x) ")")
         | FStar_Pervasives.Inr x ->
             Prims.strcat "(Inr " (Prims.strcat (to_string uu___1 x) ")"))
  }
let printable_char : FStar_Char.char printable=
  { to_string = FStar_String.string_of_char }
let printable_byte : FStar_UInt8.t printable=
  { to_string = FStar_UInt8.to_string }
let printable_int8 : FStar_Int8.t printable=
  { to_string = FStar_Int8.to_string }
let printable_uint8 : FStar_UInt8.t printable=
  { to_string = FStar_UInt8.to_string }
let printable_int16 : FStar_Int16.t printable=
  { to_string = FStar_Int16.to_string }
let printable_uint16 : FStar_UInt16.t printable=
  { to_string = FStar_UInt16.to_string }
let printable_int32 : FStar_Int32.t printable=
  { to_string = FStar_Int32.to_string }
let printable_uint32 : FStar_UInt32.t printable=
  { to_string = FStar_UInt32.to_string }
let printable_int64 : FStar_Int64.t printable=
  { to_string = FStar_Int64.to_string }
let printable_uint64 : FStar_UInt64.t printable=
  { to_string = FStar_UInt64.to_string }
let printable_tuple2 (uu___ : 'a printable) (uu___1 : 'b printable) :
  ('a * 'b) printable=
  {
    to_string =
      (fun uu___2 ->
         match uu___2 with
         | (x, y) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ x)
                  (Prims.strcat ", " (Prims.strcat (to_string uu___1 y) ")"))))
  }
let printable_tuple3 (uu___ : 't0 printable) (uu___1 : 't1 printable)
  (uu___2 : 't2 printable) : ('t0 * 't1 * 't2) printable=
  {
    to_string =
      (fun uu___3 ->
         match uu___3 with
         | (v0, v1, v2) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ v0)
                  (Prims.strcat ", "
                     (Prims.strcat (to_string uu___1 v1)
                        (Prims.strcat ", "
                           (Prims.strcat (to_string uu___2 v2) ")"))))))
  }
let printable_tuple4 (uu___ : 't0 printable) (uu___1 : 't1 printable)
  (uu___2 : 't2 printable) (uu___3 : 't3 printable) :
  ('t0 * 't1 * 't2 * 't3) printable=
  {
    to_string =
      (fun uu___4 ->
         match uu___4 with
         | (v0, v1, v2, v3) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ v0)
                  (Prims.strcat ", "
                     (Prims.strcat (to_string uu___1 v1)
                        (Prims.strcat ", "
                           (Prims.strcat (to_string uu___2 v2)
                              (Prims.strcat ", "
                                 (Prims.strcat (to_string uu___3 v3) ")"))))))))
  }
let printable_tuple5 (uu___ : 't0 printable) (uu___1 : 't1 printable)
  (uu___2 : 't2 printable) (uu___3 : 't3 printable) (uu___4 : 't4 printable)
  : ('t0 * 't1 * 't2 * 't3 * 't4) printable=
  {
    to_string =
      (fun uu___5 ->
         match uu___5 with
         | (v0, v1, v2, v3, v4) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ v0)
                  (Prims.strcat ", "
                     (Prims.strcat (to_string uu___1 v1)
                        (Prims.strcat ", "
                           (Prims.strcat (to_string uu___2 v2)
                              (Prims.strcat ", "
                                 (Prims.strcat (to_string uu___3 v3)
                                    (Prims.strcat ", "
                                       (Prims.strcat (to_string uu___4 v4)
                                          ")"))))))))))
  }
let printable_tuple6 (uu___ : 't0 printable) (uu___1 : 't1 printable)
  (uu___2 : 't2 printable) (uu___3 : 't3 printable) (uu___4 : 't4 printable)
  (uu___5 : 't5 printable) : ('t0 * 't1 * 't2 * 't3 * 't4 * 't5) printable=
  {
    to_string =
      (fun uu___6 ->
         match uu___6 with
         | (v0, v1, v2, v3, v4, v5) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ v0)
                  (Prims.strcat ", "
                     (Prims.strcat (to_string uu___1 v1)
                        (Prims.strcat ", "
                           (Prims.strcat (to_string uu___2 v2)
                              (Prims.strcat ", "
                                 (Prims.strcat (to_string uu___3 v3)
                                    (Prims.strcat ", "
                                       (Prims.strcat (to_string uu___4 v4)
                                          (Prims.strcat ", "
                                             (Prims.strcat
                                                (to_string uu___5 v5) ")"))))))))))))
  }
let printable_tuple7 (uu___ : 't0 printable) (uu___1 : 't1 printable)
  (uu___2 : 't2 printable) (uu___3 : 't3 printable) (uu___4 : 't4 printable)
  (uu___5 : 't5 printable) (uu___6 : 't6 printable) :
  ('t0 * 't1 * 't2 * 't3 * 't4 * 't5 * 't6) printable=
  {
    to_string =
      (fun uu___7 ->
         match uu___7 with
         | (v0, v1, v2, v3, v4, v5, v6) ->
             Prims.strcat "("
               (Prims.strcat (to_string uu___ v0)
                  (Prims.strcat ", "
                     (Prims.strcat (to_string uu___1 v1)
                        (Prims.strcat ", "
                           (Prims.strcat (to_string uu___2 v2)
                              (Prims.strcat ", "
                                 (Prims.strcat (to_string uu___3 v3)
                                    (Prims.strcat ", "
                                       (Prims.strcat (to_string uu___4 v4)
                                          (Prims.strcat ", "
                                             (Prims.strcat
                                                (to_string uu___5 v5)
                                                (Prims.strcat ", "
                                                   (Prims.strcat
                                                      (to_string uu___6 v6)
                                                      ")"))))))))))))))
  }
let printable_seq (x : 'b printable) : 'b FStar_Seq_Base.seq printable=
  {
    to_string =
      (fun s ->
         let strings_of_b = FStar_Seq_Properties.map_seq (to_string x) s in
         Prims.strcat "<"
           (Prims.strcat
              (FStar_String.concat "; "
                 (FStar_Seq_Base.seq_to_list strings_of_b)) ">"))
  }
