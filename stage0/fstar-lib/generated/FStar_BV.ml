open Prims
type 'n bv_t = unit FStar_BitVector.bv_t
let (bv_uext :
  Prims.pos -> Prims.pos -> unit bv_t -> Prims.bool FStar_Seq_Base.seq) =
  fun n ->
    fun i -> fun a -> FStar_Seq_Base.append (FStar_Seq_Base.create i false) a
let (int2bv : Prims.pos -> unit FStar_UInt.uint_t -> unit bv_t) =
  FStar_UInt.to_vec
let (bv2int : Prims.pos -> unit bv_t -> unit FStar_UInt.uint_t) =
  FStar_UInt.from_vec
let (int2bv_nat : Prims.pos -> Prims.nat -> unit bv_t) =
  fun n -> fun num -> FStar_UInt.to_vec n (num mod (Prims.pow2 n))
let (list2bv : Prims.pos -> Prims.bool Prims.list -> unit bv_t) =
  fun n -> fun l -> FStar_Seq_Base.seq_of_list l
let (bv2list : Prims.pos -> unit bv_t -> Prims.bool Prims.list) =
  fun n -> fun s -> FStar_Seq_Base.seq_to_list s
let (bvand : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  FStar_BitVector.logand_vec
let (bvxor : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  FStar_BitVector.logxor_vec
let (bvor : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  FStar_BitVector.logor_vec
let (bvnot : Prims.pos -> unit bv_t -> unit bv_t) =
  FStar_BitVector.lognot_vec
let (bvshl' : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n -> fun a -> fun s -> FStar_BitVector.shift_left_vec n a (bv2int n s)
let (bvshl : Prims.pos -> unit bv_t -> Prims.nat -> unit bv_t) =
  fun n -> fun a -> fun s -> bvshl' n a (int2bv_nat n s)
let (bvshr' : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n -> fun a -> fun s -> FStar_BitVector.shift_right_vec n a (bv2int n s)
let (bvshr : Prims.pos -> unit bv_t -> Prims.nat -> unit bv_t) =
  fun n -> fun a -> fun s -> bvshr' n a (int2bv_nat n s)
let (bv_zero : Prims.pos -> unit bv_t) = fun n -> int2bv n Prims.int_zero
let (bvult : Prims.pos -> unit bv_t -> unit bv_t -> Prims.bool) =
  fun n -> fun a -> fun b -> (bv2int n a) < (bv2int n b)
let (bvadd : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n ->
    fun a ->
      fun b -> int2bv n (FStar_UInt.add_mod n (bv2int n a) (bv2int n b))
let (bvsub : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n ->
    fun a ->
      fun b -> int2bv n (FStar_UInt.sub_mod n (bv2int n a) (bv2int n b))
let (bvdiv : Prims.pos -> unit bv_t -> unit FStar_UInt.uint_t -> unit bv_t) =
  fun n -> fun a -> fun b -> int2bv n (FStar_UInt.udiv n (bv2int n a) b)
let (bvdiv_unsafe : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n ->
    fun a ->
      fun b ->
        if (bv2int n b) <> Prims.int_zero
        then bvdiv n a (bv2int n b)
        else int2bv n Prims.int_zero
let (bvmod : Prims.pos -> unit bv_t -> unit FStar_UInt.uint_t -> unit bv_t) =
  fun n -> fun a -> fun b -> int2bv n (FStar_UInt.mod1 n (bv2int n a) b)
let (bvmod_unsafe : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n ->
    fun a ->
      fun b ->
        if (bv2int n b) <> Prims.int_zero
        then bvmod n a (bv2int n b)
        else int2bv n Prims.int_zero
let (bvmul : Prims.pos -> unit bv_t -> unit FStar_UInt.uint_t -> unit bv_t) =
  fun n -> fun a -> fun b -> int2bv n (FStar_UInt.mul_mod n (bv2int n a) b)
let (bvmul' : Prims.pos -> unit bv_t -> unit bv_t -> unit bv_t) =
  fun n ->
    fun a ->
      fun b -> int2bv n (FStar_UInt.mul_mod n (bv2int n a) (bv2int n b))