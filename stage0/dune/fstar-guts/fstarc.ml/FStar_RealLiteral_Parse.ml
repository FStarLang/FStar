open Prims
let digit_of_char (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  match c with
  | 48 -> FStar_Pervasives_Native.Some Prims.int_zero
  | 49 -> FStar_Pervasives_Native.Some Prims.int_one
  | 50 -> FStar_Pervasives_Native.Some (Prims.of_int 2)
  | 51 -> FStar_Pervasives_Native.Some (Prims.of_int 3)
  | 52 -> FStar_Pervasives_Native.Some (Prims.of_int 4)
  | 53 -> FStar_Pervasives_Native.Some (Prims.of_int 5)
  | 54 -> FStar_Pervasives_Native.Some (Prims.of_int 6)
  | 55 -> FStar_Pervasives_Native.Some (Prims.of_int 7)
  | 56 -> FStar_Pervasives_Native.Some (Prims.of_int 8)
  | 57 -> FStar_Pervasives_Native.Some (Prims.of_int 9)
  | uu___ -> FStar_Pervasives_Native.None
let rec split_at_dot (cs : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | 46::cs1 -> FStar_Pervasives_Native.Some ([], cs1)
  | c::cs1 ->
      (match split_at_dot cs1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (i, f) ->
           FStar_Pervasives_Native.Some ((c :: i), f))
let rec digits_of_chars (cs : FStar_Char.char Prims.list) :
  Prims.int Prims.list FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some []
  | c::cs1 ->
      (match ((digit_of_char c), (digits_of_chars cs1)) with
       | (FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.Some ds) ->
           FStar_Pervasives_Native.Some (d :: ds)
       | uu___ -> FStar_Pervasives_Native.None)
let rec int_of_digits_acc (acc : Prims.int) (ds : Prims.int Prims.list) :
  Prims.int=
  match ds with
  | [] -> acc
  | d::ds' -> int_of_digits_acc ((acc * (Prims.of_int 10)) + d) ds'
let of_string (s : Prims.string) :
  FStar_RealLiteral.real_literal FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  let uu___ = match cs with | 45::cs1 -> (true, cs1) | uu___1 -> (false, cs) in
  match uu___ with
  | (neg, cs1) ->
      let uu___1 =
        match split_at_dot cs1 with
        | FStar_Pervasives_Native.Some (i, f) -> (i, f)
        | FStar_Pervasives_Native.None -> (cs1, []) in
      (match uu___1 with
       | (ipart, fpart) ->
           (match (ipart, (digits_of_chars ipart), (digits_of_chars fpart))
            with
            | (uu___2::uu___3, FStar_Pervasives_Native.Some ipart1,
               FStar_Pervasives_Native.Some fpart1) ->
                let m =
                  int_of_digits_acc Prims.int_zero
                    (FStar_List_Tot_Base.op_At ipart1 fpart1) in
                FStar_Pervasives_Native.Some
                  (FStar_RealLiteral.mk (if neg then - m else m)
                     (- (FStar_List_Tot_Base.length fpart1)))
            | uu___2 -> FStar_Pervasives_Native.None))
