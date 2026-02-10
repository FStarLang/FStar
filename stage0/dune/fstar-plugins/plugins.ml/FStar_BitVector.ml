open Fstarcompiler
open Prims
type 'n bv_t = Prims.bool FStar_Seq_Base.seq
let zero_vec (n : Prims.pos) : Obj.t bv_t= FStar_Seq_Base.create n false
let elem_vec (n : Prims.pos) (i : Prims.nat) : Obj.t bv_t=
  FStar_Seq_Base.upd (FStar_Seq_Base.create n false) i true
let ones_vec (n : Prims.pos) : Obj.t bv_t= FStar_Seq_Base.create n true
let rec logand_vec (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) :
  Obj.t bv_t=
  if n = Prims.int_one
  then
    FStar_Seq_Base.create Prims.int_one
      ((FStar_Seq_Base.index a Prims.int_zero) &&
         (FStar_Seq_Base.index b Prims.int_zero))
  else
    FStar_Seq_Base.append
      (FStar_Seq_Base.create Prims.int_one
         ((FStar_Seq_Base.index a Prims.int_zero) &&
            (FStar_Seq_Base.index b Prims.int_zero)))
      (logand_vec (n - Prims.int_one)
         (FStar_Seq_Base.slice a Prims.int_one n)
         (FStar_Seq_Base.slice b Prims.int_one n))
let rec logxor_vec (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) :
  Obj.t bv_t=
  if n = Prims.int_one
  then
    FStar_Seq_Base.create Prims.int_one
      ((FStar_Seq_Base.index a Prims.int_zero) <>
         (FStar_Seq_Base.index b Prims.int_zero))
  else
    FStar_Seq_Base.append
      (FStar_Seq_Base.create Prims.int_one
         ((FStar_Seq_Base.index a Prims.int_zero) <>
            (FStar_Seq_Base.index b Prims.int_zero)))
      (logxor_vec (n - Prims.int_one)
         (FStar_Seq_Base.slice a Prims.int_one n)
         (FStar_Seq_Base.slice b Prims.int_one n))
let rec logor_vec (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) :
  Obj.t bv_t=
  if n = Prims.int_one
  then
    FStar_Seq_Base.create Prims.int_one
      ((FStar_Seq_Base.index a Prims.int_zero) ||
         (FStar_Seq_Base.index b Prims.int_zero))
  else
    FStar_Seq_Base.append
      (FStar_Seq_Base.create Prims.int_one
         ((FStar_Seq_Base.index a Prims.int_zero) ||
            (FStar_Seq_Base.index b Prims.int_zero)))
      (logor_vec (n - Prims.int_one) (FStar_Seq_Base.slice a Prims.int_one n)
         (FStar_Seq_Base.slice b Prims.int_one n))
let rec lognot_vec (n : Prims.pos) (a : Obj.t bv_t) : Obj.t bv_t=
  if n = Prims.int_one
  then
    FStar_Seq_Base.create Prims.int_one
      (Prims.op_Negation (FStar_Seq_Base.index a Prims.int_zero))
  else
    FStar_Seq_Base.append
      (FStar_Seq_Base.create Prims.int_one
         (Prims.op_Negation (FStar_Seq_Base.index a Prims.int_zero)))
      (lognot_vec (n - Prims.int_one)
         (FStar_Seq_Base.slice a Prims.int_one n))
type ('n, 'a, 'b) is_subset_vec = unit
type ('n, 'a, 'b) is_superset_vec = unit
let shift_left_vec (n : Prims.pos) (a : Obj.t bv_t) (s : Prims.nat) :
  Obj.t bv_t=
  if s >= n
  then zero_vec n
  else
    if s = Prims.int_zero
    then a
    else FStar_Seq_Base.append (FStar_Seq_Base.slice a s n) (zero_vec s)
let shift_right_vec (n : Prims.pos) (a : Obj.t bv_t) (s : Prims.nat) :
  Obj.t bv_t=
  if s >= n
  then zero_vec n
  else
    if s = Prims.int_zero
    then a
    else
      FStar_Seq_Base.append (zero_vec s)
        (FStar_Seq_Base.slice a Prims.int_zero (n - s))
let shift_arithmetic_right_vec (n : Prims.pos) (a : Obj.t bv_t)
  (s : Prims.nat) : Obj.t bv_t=
  if FStar_Seq_Base.index a Prims.int_zero
  then
    (if s >= n
     then ones_vec n
     else
       if s = Prims.int_zero
       then a
       else
         FStar_Seq_Base.append (ones_vec s)
           (FStar_Seq_Base.slice a Prims.int_zero (n - s)))
  else shift_right_vec n a s
