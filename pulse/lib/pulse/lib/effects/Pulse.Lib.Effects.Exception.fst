module Pulse.Lib.Effects.Exception

(* Pure exception-tree transformations and their policy-preservation proofs.

   No definition here executes a Pulse action. The handlers traverse the
   available tree structure, leave Step actions delayed, and transform their
   continuations. Actual heap effects occur only when the resulting Core tree
   is interpreted. A Throw discards code, never its ownership obligations.

   catch has its own traversal because its refined input proves that a local
   Throw's frame is emp. handle's callback is instead universally quantified
   over frames; it cannot directly accept an ordinary exception-only callback.
   Both traversals remove one layer and forward the remaining operations. *)

open Pulse.Lib.Core
// E is the underlying representation; exception prog is only its refinement.
module E = Pulse.Lib.Effects.Core

// Reuse Core.lift and discharge its local frame policy with the generic
// no-requests lemma. The thunk remains unevaluated.
let lift #other #exn #a #ops #exceptional #p #q action =
  E.lift_all_requests action (frame_policy ops exceptional);
  E.lift action

// Follow normal leaves and resumable Other continuations, preserving the local
// policy. At Throw, construct the abort node at the new result/postcondition
// without composing into its uninhabited continuation. Besides matching abortive
// sequencing, this avoids specializing unreachable continuation code in Custard.
let rec bind #other #exn #a #b #ops #exceptional #p #q #s c next =
  match c with
  | E.Return x -> next x
  | E.Step action k -> E.Step action (fun x -> bind (k x) next)
  | E.Perform #_ #_ #_ #_ #r op arg k ->
      match op with
      | Throw ->
          // Do not compose code into an impossible continuation.
          E.Perform #_ #(extend ops exceptional) #b #s #r Throw arg
            (fun impossible -> match impossible with)
      | Other op ->
          E.Perform #_ #(extend ops exceptional) #b #s #r (Other op) arg
            (fun y -> bind (k y) next)

// Construct a request with frame emp and eliminate the impossible reply.
// The final equality transport hides the constructor's administrative ** emp;
// no impossible postcondition is asserted or admitted.
let throw #other #exn #a #ops #exceptional #q e =
  let request =
    E.Perform #(tag other) #(extend ops exceptional) #a #q #emp Throw e
      (fun impossible -> match impossible with)
  in
  star_comm (exceptional e) emp;
  emp_unit (exceptional e);
  E.reindex_pre (exceptional e) () request

// For a raw tree, pass the exact private frame r to the exceptional clause.
// Return invokes the normal clause; Step and Other keep their continuations
// under this handler. The clause result is already in the outer environment.
let rec handle #other #exn #a #b #ops #exceptional #p #q #s c on_return on_throw =
  match c with
  | E.Return x -> on_return x
  | E.Step action k ->
      E.Step action (fun x -> handle (k x) on_return on_throw)
  | E.Perform #_ #_ #_ #_ #r op arg k ->
      match op with
      | Throw -> on_throw #r arg
      | Other op ->
          E.Perform #other #ops #b #s #r op arg
            (fun y -> handle (k y) on_return on_throw)

// Use the input refinement at Throw to identify its private frame with emp.
// Reindexing the exception clause then matches the original request precondition
// exactly. No continuation is resumed, and no nonempty frame is dropped.
let rec catch #other #exn #a #b #ops #exceptional #p #q #s c on_return on_throw =
  match c with
  | E.Return x -> on_return x
  | E.Step action k ->
      E.Step action (fun x -> catch (k x) on_return on_throw)
  | E.Perform #_ #_ #_ #_ #r op arg k ->
      match op with
      | Throw ->
          assert (r == emp);
          star_comm (exceptional arg) emp;
          emp_unit (exceptional arg);
          E.reindex_pre p () (on_throw arg)
      | Other op ->
          E.Perform #other #ops #b #s #r op arg
            (fun y -> catch (k y) on_return on_throw)

// Induct over catch's traversal. At Throw, relate the transported clause tree
// to on_throw arg so its policy proof applies; at Other, retain the current
// request's policy and prove the property for every forwarded continuation.
let rec catch_all_requests #other #exn #a #b #ops #exceptional #p #q #s
  c on_return on_throw policy =
  match c with
  | E.Return _ -> ()
  | E.Step action k ->
      FStar.Classical.forall_intro
        (fun x -> catch_all_requests (k x) on_return on_throw policy)
  | E.Perform #_ #_ #_ #_ #r op arg k ->
      match op with
      | Throw ->
          assert (r == emp);
          star_comm (exceptional arg) emp;
          emp_unit (exceptional arg);
          let handled = E.reindex_pre p () (on_throw arg) in
          assert (handled == on_throw arg);
          assert (catch c on_return on_throw == handled)
      | Other _ ->
          FStar.Classical.forall_intro
            (fun y -> catch_all_requests (k y) on_return on_throw policy)

// Every embedded tag is Other, which the local frame policy accepts regardless
// of the request frame. Establish that property before returning Core.weaken's
// relabelled tree as a member of the refined exception fragment.
let weaken #other #exn #a #ops #exceptional #p #q c =
  E.weaken_all_requests #other #(tag other) #ops #(extend ops exceptional)
    (fun op -> Other op) c (frame_policy ops exceptional);
  E.weaken #other #(tag other) #ops #(extend ops exceptional) (fun op -> Other op) c
