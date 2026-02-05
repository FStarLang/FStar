open Fstarcompiler
open Prims
type 'n bv_t = 'n FStar_BitVector.bv_t
let bv_uext (n : Prims.pos) (i : Prims.pos) (a : Obj.t bv_t) :
  Prims.bool FStar_Seq_Base.seq=
  FStar_Seq_Base.append (FStar_Seq_Base.create i false) a
let int2bv : Prims.pos -> Obj.t FStar_UInt.uint_t -> Obj.t bv_t=
  FStar_UInt.to_vec
let bv2int : Prims.pos -> Obj.t bv_t -> Obj.t FStar_UInt.uint_t=
  FStar_UInt.from_vec
let int2bv_nat (n : Prims.pos) (num : Prims.nat) : Obj.t bv_t=
  FStar_UInt.to_vec n ((mod) num (Prims.pow2 n))
let list2bv (n : Prims.pos) (l : Prims.bool Prims.list) : Obj.t bv_t=
  FStar_Seq_Base.seq_of_list l
let bv2list (n : Prims.pos) (s : Obj.t bv_t) : Prims.bool Prims.list=
  FStar_Seq_Base.seq_to_list s
let bvand : Prims.pos -> Obj.t bv_t -> Obj.t bv_t -> Obj.t bv_t=
  FStar_BitVector.logand_vec
let bvxor : Prims.pos -> Obj.t bv_t -> Obj.t bv_t -> Obj.t bv_t=
  FStar_BitVector.logxor_vec
let bvor : Prims.pos -> Obj.t bv_t -> Obj.t bv_t -> Obj.t bv_t=
  FStar_BitVector.logor_vec
let bvnot : Prims.pos -> Obj.t bv_t -> Obj.t bv_t= FStar_BitVector.lognot_vec
let bvshl' (n : Prims.pos) (a : Obj.t bv_t) (s : Obj.t bv_t) : Obj.t bv_t=
  FStar_BitVector.shift_left_vec n a (bv2int n s)
let bvshl (n : Prims.pos) (a : Obj.t bv_t) (s : Prims.nat) : Obj.t bv_t=
  bvshl' n a (int2bv_nat n s)
let bvshr' (n : Prims.pos) (a : Obj.t bv_t) (s : Obj.t bv_t) : Obj.t bv_t=
  FStar_BitVector.shift_right_vec n a (bv2int n s)
let bvshr (n : Prims.pos) (a : Obj.t bv_t) (s : Prims.nat) : Obj.t bv_t=
  bvshr' n a (int2bv_nat n s)
let bv_zero (n : Prims.pos) : Obj.t bv_t= int2bv n Prims.int_zero
let bvult (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) : Prims.bool=
  (bv2int n a) < (bv2int n b)
let bvadd (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) : Obj.t bv_t=
  int2bv n (FStar_UInt.add_mod n (bv2int n a) (bv2int n b))
let bvsub (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) : Obj.t bv_t=
  int2bv n (FStar_UInt.sub_mod n (bv2int n a) (bv2int n b))
let bvdiv (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t FStar_UInt.uint_t) :
  Obj.t bv_t= int2bv n (FStar_UInt.udiv n (bv2int n a) b)
let bvdiv_unsafe (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) :
  Obj.t bv_t=
  if (bv2int n b) <> Prims.int_zero
  then bvdiv n a (bv2int n b)
  else int2bv n Prims.int_zero
let bvmod (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t FStar_UInt.uint_t) :
  Obj.t bv_t= int2bv n (FStar_UInt.mod1 n (bv2int n a) b)
let bvmod_unsafe (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) :
  Obj.t bv_t=
  if (bv2int n b) <> Prims.int_zero
  then bvmod n a (bv2int n b)
  else int2bv n Prims.int_zero
let bvmul (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t FStar_UInt.uint_t) :
  Obj.t bv_t= int2bv n (FStar_UInt.mul_mod n (bv2int n a) b)
let bvmul' (n : Prims.pos) (a : Obj.t bv_t) (b : Obj.t bv_t) : Obj.t bv_t=
  int2bv n (FStar_UInt.mul_mod n (bv2int n a) (bv2int n b))
