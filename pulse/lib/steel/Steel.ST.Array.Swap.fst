module Steel.ST.Array.Swap
open Steel.ST.GenElim
open Steel.ST.Array // for pts_to

module Gen = Steel.ST.GenArraySwap

[@@__reduce__]
let array_pts_to (#t: Type) (a: array t) : Tot (Gen.array_pts_to_t t) =
  fun s -> pts_to a full_perm (Ghost.reveal s)

inline_for_extraction
let array_index
  (#t: Type)
  (a: array t)
: Tot (Gen.array_index_t (array_pts_to a))
= fun s n i ->
    index a i

inline_for_extraction
let array_upd
  (#t: Type)
  (a: array t)
: Tot (Gen.array_upd_t (array_pts_to a))
= fun s n i x ->
    upd a i x;
    return _

let swap
  a n l
= pts_to_length a _;
  Gen.array_swap_gen (array_index a) (array_upd a) _ n l
