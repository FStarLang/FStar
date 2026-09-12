(* Section 106.  The same built-in representation rule as section 93, one
   level down.  [option (array uint32)] and [option (array bool)] differ only
   in the element type of an array that is not at the head of either, and the
   guard that kept [array] from normalizing away read the head alone -- so
   both reduced to [option array'], both produced the same key, and one
   [fst] specialization was emitted for two incompatible tuple types.

   [fst_both] is the shape: one definition projecting out of both tuples, so
   that a single shared specialization is a C error rather than a coincidence
   of naming.  [opt_arr] pins the two option types apart, and [plain_both] is
   the control that compiled before -- a parameterized record in the same
   position, carrying no rule and rightly sharing nothing. *)
module NestArr
module A = Pulse.Lib.Array
module U32 = FStar.UInt32

let fst_both (x : U32.t & option (A.array U32.t))
             (y : U32.t & option (A.array bool)) : U32.t =
  U32.add_mod (fst x) (fst y)

let opt_arr (o : option (A.array U32.t)) : bool =
  match o with
  | None -> true
  | Some a -> A.is_null a

let opt_arr_b (o : option (A.array bool)) : bool =
  match o with
  | None -> true
  | Some a -> A.is_null a

(* The control: a parameterized record in the same position, carrying no
   rule.  It compiled before and must go on compiling -- the guard has not
   widened to types whose element is already visible in the reduced form. *)
noeq type box (a:Type0) = { v : a }

let plain_both (x : U32.t & option (box U32.t))
               (y : U32.t & option (box bool)) : U32.t =
  U32.add_mod (fst x) (fst y)

let main () : FStar.All.ML FStar.Int32.t =
  let a : option (A.array U32.t) = None in
  let b : option (A.array bool) = None in
  let n = fst_both (1ul, a) (2ul, b) in
  let m = plain_both (1ul, None) (2ul, None) in
  if opt_arr a && opt_arr_b b && U32.eq n 3ul && U32.eq m 3ul then 0l else 1l
