(*--build-config
    options:--admit_fsi FStar.Set --verify_module M;
    other-files:set.fsi heap.fst st.fst all.fst
--*)
module M

// Substituting `pos` for a non-refined type makes `f` below typecheck
// type num = | N of int
type num = | N of pos

val f: num -> num
let f n =
  match n with
  | N d -> let rec g x = N d in g 1
