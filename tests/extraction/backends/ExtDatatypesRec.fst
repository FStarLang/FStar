module ExtDatatypesRec

/// Recursive inductives. **Known C limitation, XFAIL_C.**
///
/// Low* has no heap-allocated inductives, so a constructor field whose type
/// is the type being defined cannot be laid out. Karamel does not diagnose
/// this: it emits a struct containing itself by value, and the *C compiler*
/// is the one that complains ("field 'tl' has incomplete type"). Emitting
/// uncompilable C with no warning is severity 4 and, more importantly, means
/// the user gets a confusing error in generated code rather than a message
/// about their F* source.
///
/// The Rust backend does not fail either -- it simply never finishes. Two
/// recursive datatypes in one module are enough to make krml spin at 100% CPU
/// indefinitely (FINDINGS.md #9), which is why every krml invocation in this
/// directory runs under a timeout. Only OCaml handles this module.

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let three : U32.t = 3ul
let seven : U32.t = 7ul

type mylist (a:Type) =
  | Nil : mylist a
  | Cons : hd:a -> tl:mylist a -> mylist a

let rec length (#a:Type) (l:mylist a) : U32.t =
  match l with
  | Nil -> 0ul
  | Cons _ tl -> U32.add_mod 1ul (length tl)

let rec sum (l:mylist U32.t) : U32.t =
  match l with
  | Nil -> 0ul
  | Cons h tl -> U32.add_mod h (sum tl)

/// Tail-recursive, with an accumulator: the shape a backend might turn into
/// a loop.
let rec sum_acc (l:mylist U32.t) (acc:U32.t) : U32.t =
  match l with
  | Nil -> acc
  | Cons h tl -> sum_acc tl (U32.add_mod acc h)

type tree =
  | Leaf : U32.t -> tree
  | Node : tree -> tree -> tree

/// Two recursive calls in one branch, so the traversal order matters.
let rec tree_sum (t:tree) : U32.t =
  match t with
  | Leaf v -> v
  | Node l r -> U32.add_mod (tree_sum l) (tree_sum r)

let main () : I32.t =
  let l = Cons one (Cons two (Cons three Nil)) in
  let t = Node (Node (Leaf one) (Leaf two)) (Leaf seven) in
     chk 1l (U32.eq (length l) 3ul)
 &&& chk 2l (U32.eq (sum l) 6ul)
 &&& chk 3l (U32.eq (length #U32.t Nil) 0ul)
 &&& chk 4l (U32.eq (sum Nil) 0ul)
 &&& chk 5l (U32.eq (sum_acc l 0ul) 6ul)
 &&& chk 6l (U32.eq (tree_sum t) 10ul)
 &&& chk 7l (U32.eq (tree_sum (Leaf seven)) 7ul)
 &&& chk 8l (match l with | Cons h _ -> U32.eq h 1ul | Nil -> false)
     (* a nested pattern, two levels deep *)
 &&& chk 9l (match l with | Cons _ (Cons h _) -> U32.eq h 2ul | _ -> false)
