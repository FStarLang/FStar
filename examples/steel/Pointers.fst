module Pointers

open Steel.Effect
open Steel.Effect.Atomic
module U32 = FStar.UInt32

open Steel.Pointer

let test_malloc_free () : SteelT unit emp (fun _ -> emp) =
  let x = malloc false in
  if is_null x _
  then begin
    assert_null x _;
    return ()
  end else begin
    assert_not_null x _;
    free x _
  end

let test_split () : SteelT unit emp (fun _ -> emp) =
  let x = calloc false (mk_size_t 3ul) in
  if is_null x _
  then begin
    noop ();
    assert_null x _
  end else begin
    assert_not_null x _;
    let x2 = add x _ (mk_size_t 2ul) in
    let _ = move x x2 _ in
    let _ = split x2 _ in
    let _ = move x2 x (GPair?.fst _) in // annotation is advised, but surprisingly not necessary despite split giving two possible ranges for x2
    let x1 = add x _ (mk_size_t 1ul) in
    let _ = move x x1 _ in
    let _ = split x1 _ in
    let _ = move x1 x (GPair?.fst _) in  // same here
    let _ = merge_left x1 x2 _ _ in
    let _ = merge_left x x1 _ _ in
    free x _
  end
