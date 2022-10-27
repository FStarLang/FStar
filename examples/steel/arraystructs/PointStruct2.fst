module PointStruct2
open Steel.C.Types

module U32 = FStar.UInt32

noextract
inline_for_extraction
let point_fields =
  field_description_cons "x" (scalar U32.t) (
  field_description_cons "y" (scalar U32.t) (
  field_description_nil))

let _ = define_struct "PointStruct.point" point_fields

inline_for_extraction noextract
let point = struct "PointStruct.point" point_fields

#push-options "--query_stats --fuel 0"

let swap_struct (p: ref point) (v: Ghost.erased (typeof point))
: Steel (Ghost.erased (typeof point))
    (p `pts_to` v)
    (fun v' -> p `pts_to` v')
    (requires fun _ ->
      exists (vx vy: U32.t) . struct_get_field v "x" == mk_scalar vx /\ struct_get_field v "y" == mk_scalar vy
    )
    (ensures fun _ v' _ ->
      struct_get_field v' "x" == struct_get_field v "y" /\
      struct_get_field v' "y" == struct_get_field v "x"
    )
= let px = struct_field p "x" in
  let py = struct_field p "y" in
  let x = read px in
  let y = read py in
  write px y;
  write py x;
  unstruct_field p "x" px;
  unstruct_field p "y" py;
  return _
