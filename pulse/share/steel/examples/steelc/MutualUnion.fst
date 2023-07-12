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

(* The following SHOULD extract to something like:
<<

typedef struct MutualUnion_test_struct_s MutualUnion_test_struct;

typedef union {
  uint32_t as_u32;
  MutualUnion_test_struct *as_ptr;
}
MutualUnion_test_union_FAIL;

typedef struct MutualUnion_test_struct_s
{
  bool tag;
  MutualUnion_test_union_FAIL payload;
}
MutualUnion_test_struct;

>>
But right now, KaRaMel generates the struct before the union, so the generated C code fails to compile.
*)
noeq
type test_union_FAIL = union_t "MutualUnion.test_union_FAIL" (
       field_description_cons "as_u32" (scalar U32.t) (
       field_description_cons "as_ptr" (scalar (ptr_gen test_struct)) (
       field_description_nil))
     )
and test_struct = {
  tag: bool;
  payload: test_union_FAIL;
}

let test_fun () = 0s
