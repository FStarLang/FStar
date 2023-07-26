module PointStructDirectDef
open Steel.ST.Util
open Steel.ST.C.Types

module U32 = FStar.UInt32
// module C = C // for _zero_for_deref

let swap (#v1 #v2: Ghost.erased U32.t) (r1 r2: ref (scalar U32.t)) : STT unit
  ((r1 `pts_to` mk_scalar (Ghost.reveal v1)) `star` (r2 `pts_to` mk_scalar (Ghost.reveal v2)))
  (fun _ -> (r1 `pts_to` mk_scalar (Ghost.reveal v2)) `star` (r2 `pts_to` mk_scalar (Ghost.reveal v1)))
= let x1 = read r1 in
  let x2 = read r2 in
  write r1 x2;
  write r2 x1;
  return () // necessary to enable smt_fallback

noextract
inline_for_extraction
[@@ norm_field_attr]
let point_fields =
  field_description_cons "x" (scalar U32.t) (
  field_description_cons "y" (scalar U32.t) (
  field_description_nil))

let point_t = struct_t "dummy" point_fields

noextract
let point : typedef point_t = struct0 _ _ _

#push-options "--query_stats --fuel 0 --print_implicits"

let swap_struct (p: ref point) (v: Ghost.erased (typeof point))
: ST (Ghost.erased (typeof point))
    (p `pts_to` v)
    (fun v' -> p `pts_to` v')
    (requires
      exists (vx vy: U32.t) . struct_get_field v "x" == mk_scalar vx /\ struct_get_field v "y" == mk_scalar vy
    )
    (ensures fun v' ->
      struct_get_field v' "x" == struct_get_field v "y" /\
      struct_get_field v' "y" == struct_get_field v "x"
    )
= let px = struct_field p "x" () in
  let py = struct_field p "y" () in
  let x = read px in
  let y = read py in
  write px y;
  write py x;
  let _ = unstruct_field p "x" px in
  let _ = unstruct_field p "y" py in
  drop (has_struct_field _ _ px);
  drop (has_struct_field _ _ _);
  return _

#pop-options

let copy_struct (p: ref point) (v: Ghost.erased (typeof point))
  (q: ref point) (w: Ghost.erased (typeof point))
: ST unit
    ((p `pts_to` v) `star` (q `pts_to` w))
    (fun v' -> (p `pts_to` w) `star` (q `pts_to` w))
    (requires
      (exists (vx vy: U32.t) . struct_get_field v "x" == mk_scalar vx /\ struct_get_field v "y" == mk_scalar vy) /\
      (exists (vx vy: U32.t) . struct_get_field w "x" == mk_scalar vx /\ struct_get_field w "y" == mk_scalar vy)
    )
    (ensures fun _ -> True)
= vpattern_rewrite (pts_to q) (Ghost.hide (mk_fraction point w full_perm));
  copy q p;
  vpattern_rewrite (pts_to q) w
