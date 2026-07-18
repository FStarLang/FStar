module Definitions

type a_type = 
  | AType1: a1:int -> a2:nat -> a_type
  | AType2 of string
  | AType3 { a_type_C_field1: int
           ; a_type_C_field2: b_type }
and b_type =
  | BType1
  | BType2 of a_type
  | BType3 { b_type_F_field1: int
           ; a_type_F_field2: a_type }

type a_record = { a_record_field1: a_type; a_record_field2: int }

let fn_example x y = x + y
