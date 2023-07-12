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

#push-options "--__no_positivity"

(* The following SHOULD extract to something like:
<<

typedef union MutualUnion_test_union2_FAIL_u MutualUnion_test_union2_FAIL;

typedef struct MutualUnion_test_struct2_before_s {
  bool tag;
  MutualUnion_test_union2_FAIL *payload;
} MutualUnion_test_struct2_before;

typedef struct MutualUnion_test_struct2_after_s MutualUnion_test_struct2_after;

typedef union MutualUnion_test_union2_FAIL_u {
  MutualUnion_test_struct2_before as_struct;
  MutualUnion_test_struct2_after *as_ptr;
}
MutualUnion_test_union2_FAIL;

typedef struct MutualUnion_test_struct2_after_s
{
  bool tag;
  MutualUnion_test_union2_FAIL payload;
}
MutualUnion_test_struct2_after;

>>
But right now, KaRaMel generates struct2_after before the union, and
does not generate any forward declaration for union2, so the generated
C code fails to compile.
*)
noeq
type test_struct2_before = {
  tag: bool;
  payload: ptr_gen test_union2_FAIL;
}
and test_union2_FAIL = union_t "MutualUnion.test_union2_FAIL" (
       field_description_cons "as_struct" (scalar test_struct2_before (* TODO TR: solve positivity issue here, independently of extraction *)) (
       field_description_cons "as_ptr" (scalar (ptr_gen test_struct2_after)) (
       field_description_nil))
     )
and test_struct2_after = {
  tag: bool;
  payload: test_union2_FAIL;
}

#pop-options

let test_fun () = 0s
