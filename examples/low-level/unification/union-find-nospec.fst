(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst
  --*)
module UnionFind
open FStar.Heap


type elem = ref content
and content =
| Link: elem -> content
| Root: nat -> content


val find: x:elem ->
  ST elem
    (requires (fun _ -> True))
    (ensures (fun h_0 y h_1 ->
      is_Root (Heap.sel h_1 y) /\
      (forall z. is_Link (Heap.sel h_0 z) ==> is_Link (Heap.sel h_1 z)) /\
      (forall z. is_Root (Heap.sel h_0 z) ==> is_Root (Heap.sel h_1 z))))
let rec find x =
  match !x with
  | Link r ->
      let r' = find r in
      x := Link r';
      r'
  | Root _ ->
      x


val link: x:elem -> y:elem ->
  ST elem
    (requires (fun h -> is_Root (Heap.sel h x) /\ is_Root (Heap.sel h y)))
    (ensures (fun _ _ _ -> True))
let link x y =
  if x = y then
    x
  else match !x, !y with
  | Root rx, Root ry ->
      if rx < ry then begin
        x := Link y; y
      end else if rx > ry then begin
        y := Link x; x
      end else begin
        y := Link x;
        x := Root (rx + 1);
        x
      end


val union: elem -> elem -> St elem
let union x y =
  let rx = find x in
  let ry = find y in
  let t = !ry in
  link rx ry


val equiv: elem -> elem -> St bool
let equiv x y =
  find x = find y
