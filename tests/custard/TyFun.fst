module TyFun

/// Section 56.  A type-level *function* -- a [let] returning a type whose
/// kind takes a *value* binder -- applied to a value.  Every type here is
/// computed by matching on a list of descriptors, which is the shape Kuiper's
/// shared-memory descriptors have.
///
/// The bug this pins reduced such an application exactly once: [carrier
/// [R 4ul]] became [U32.t & carrier []] and the [carrier []] inside it stayed
/// stuck, so the second component came out [any].  Nothing here may be [any]
/// -- the suite runs this with [--custard_warn_any --warn_error @367] -- and
/// the values are checked at run time, since a type that is merely *declared*
/// correctly is not yet one whose fields land where the body expects them.

module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

type req = | R : sz:U32.t -> req

(* The recursive case: one level per list element. *)
let rec carrier (ds : list req) : Type0 =
  match ds with
  | []      -> I32.t
  | _ :: ds -> U32.t & carrier ds

(* The base case, which reduces with no unfolding of a nested application. *)
let base (c : carrier []) : I32.t = c

(* One level.  The [any] appeared at the second component. *)
let one (c : carrier [R 4ul]) : U32.t = let (a, _) = c in a

(* Three levels, so that a fix which merely unfolds *twice* still fails. *)
let three (c : carrier [R 4ul; R 8ul; R 12ul]) : U32.t =
  let (_, (_, (c3, _))) = c in c3

(* A *non-recursive* two-level chain through a second name.  There is no
   [let rec] anywhere here, so this is not about fixpoints: [outer] must
   reduce, and so must the [inner] its result names.  The recursion in
   {!ty_of_typ} is what reaches the second name. *)
let inner (ds : list req) : Type0 =
  match ds with
  | []     -> I32.t
  | _ :: _ -> U32.t

let outer (ds : list req) : Type0 =
  match ds with
  | []       -> I32.t
  | _ :: ds' -> U32.t & inner ds'

let chain (c : outer [R 1ul; R 2ul]) : U32.t = let (_, b) = c in b

let main () : ML I32.t =
  let b : carrier [] = 3l in
  let o : carrier [R 4ul] = (7ul, 5l) in
  let t : carrier [R 4ul; R 8ul; R 12ul] = (1ul, (2ul, (9ul, 4l))) in
  let ch : outer [R 1ul; R 2ul] = (6ul, 8ul) in
  if I32.eq (base b) 3l
     && U32.eq (one o) 7ul
     && U32.eq (three t) 9ul
     && U32.eq (chain ch) 8ul
  then 0l else 1l
