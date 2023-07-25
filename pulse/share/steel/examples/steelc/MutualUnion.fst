module MutualUnion
open Steel.ST.Util
open Steel.ST.C.Types

module U32 = FStar.UInt32
module U16 = FStar.UInt16

(* The following correctly extracts to:
<<

typedef union {
  uint32_t as_u32;
  uint16_t *as_u16;
}
MutualUnion_test_union_OK;

>>
*)
type test_union_OK = union_t "MutualUnion.test_union_OK" (
       field_description_cons "as_u32" (scalar U32.t) (
       field_description_cons "as_u16" (scalar (ptr_gen U16.t)) (
       field_description_nil))
     )

(* The following extracts to something like:
<<

typedef struct MutualUnion_test_struct_s MutualUnion_test_struct;

typedef union {
  uint32_t as_u32;
  MutualUnion_test_struct *as_ptr;
}
MutualUnion_test_union1_OK;

typedef struct MutualUnion_test_struct_s
{
  bool tag;
  MutualUnion_test_union1_OK payload;
}
MutualUnion_test_struct;

>>
*)
noeq
type test_union1_OK = union_t "MutualUnion.test_union1_OK" (
       field_description_cons "as_u32" (scalar U32.t) (
       field_description_cons "as_ptr" (scalar (ptr_gen test_struct)) (
       field_description_nil))
     )
and test_struct = {
  tag: bool;
  payload: test_union1_OK;
}

#push-options "--__no_positivity"

(* The following extracts to something like:
<<

typedef union MutualUnion_test_union2_OK_u MutualUnion_test_union2_OK;

typedef struct MutualUnion_test_struct2_before_s {
  bool tag;
  MutualUnion_test_union2_OK *payload;
} MutualUnion_test_struct2_before;

typedef struct MutualUnion_test_struct2_after_s MutualUnion_test_struct2_after;

typedef union MutualUnion_test_union2_OK_u {
  MutualUnion_test_struct2_before as_struct;
  MutualUnion_test_struct2_after *as_ptr;
}
MutualUnion_test_union2_OK;

typedef struct MutualUnion_test_struct2_after_s
{
  bool tag;
  MutualUnion_test_union2_OK payload;
}
MutualUnion_test_struct2_after;

>>
*)
noeq
type test_struct2_before = {
  tag: bool;
  payload: ptr_gen test_union2_OK;
}
and test_union2_OK = union_t "MutualUnion.test_union2_OK" (
       field_description_cons "as_struct" (scalar test_struct2_before (* TODO TR: solve positivity issue here, independently of extraction *)) (
       field_description_cons "as_ptr" (scalar (ptr_gen test_struct2_after)) (
       field_description_nil))
     )
and test_struct2_after = {
  tag: bool;
  payload: test_union2_OK;
}

#pop-options

let test_fun () = 0s
