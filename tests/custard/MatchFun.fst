module MatchFun
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* An application whose head is a [match] whose arms are lambdas.  None of the
   backends has closures, so the arms have to meet their argument where beta
   can fire, and the only place that can happen is inside the arms; the
   commuting conversion in [Simplify.reduce] is what puts it there.

   The arguments are passed in the other order than the binders take them,
   which is what keeps the shape: applied to [n m], F* eta-contracts [apply]
   and the application moves to the call site, where the head is no longer a
   [match].

   The C backend is the assertion -- it is the one that cannot emit an arm as
   a value -- and the run pins that the conversion did not change which arm is
   taken. *)

type ab = | A | B

let apply (c:ab) (n:U32.t) (m:U32.t) : U32.t =
  (match c with
   | A -> (fun (x:U32.t) (y:U32.t) -> U32.add_mod x y)
   | B -> (fun (x:U32.t) (y:U32.t) -> U32.sub_mod x y)) m n

let main () : I32.t =
  if U32.eq (apply A 1ul 2ul) 3ul && U32.eq (apply B 1ul 5ul) 4ul then 0l else 1l
