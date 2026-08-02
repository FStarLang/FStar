(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module OPLSS2021.DijkstraMonads

(* This module defines an abstraction for reasoning about stateful
   computations.

   The main computation type it defines is `repr a st pre post`, a state
   monad whose type records a pre- and a postcondition.

   Historically, F* itself was built on *weakest precondition
   transformers*: an effect carried a WP monad, and a computation type
   `STATE a wp` was indexed by a WP.  F* now specifies a computation
   directly by a precondition and a postcondition, so this module does
   the same: we

     1. define the specification monad --- pre- and postconditions;

     2. index a basic state monad by a specification;

     3. show that the indexed monad has a `return`, a `bind`, and a
        notion of subsumption, which is all it takes to program with it
        in direct style, using `let!`.
*)

(*** Step 1: Specifications ***)

/// A precondition constrains the initial state.
let pre_t (st:Type0) = st -> prop

/// A postcondition relates the initial state, the result, and the
/// final state.
let post_t (st:Type0) (a:Type) = st -> a -> st -> prop

/// The specification of `return x`: the state is unchanged and the
/// result is `x`.
unfold
let return_post (#a:Type) (#st:Type0) (x:a)
  : post_t st a
  = fun s0 y s1 -> y == x /\ s1 == s0

/// Sequential composition of two specifications.  Read the
/// precondition as: `c` must be runnable, and whatever it may return,
/// the continuation must be runnable on that result.
unfold
let bind_pre (#a:Type) (#st:Type0)
             (pre_c:pre_t st) (post_c:post_t st a) (pre_f:a -> pre_t st)
  : pre_t st
  = fun s0 -> pre_c s0 /\ (forall x s1. post_c s0 x s1 ==> pre_f x s1)

/// The postcondition of a sequential composition: there is an
/// intermediate result and state that `c` may produce, and from which
/// the continuation produces the final one.
unfold
let bind_post (#a #b:Type) (#st:Type0)
              (post_c:post_t st a) (post_f:a -> post_t st b)
  : post_t st b
  = fun s0 y s2 -> exists x s1. post_c s0 x s1 /\ post_f x s1 y s2

(*** Step 2: Define the computational monad
             indexed by the specification
 ***)

/// A stateful computation is a function from an initial state
/// satisfying the precondition to a result and a final state
/// satisfying the postcondition.  Note that this is just a refinement
/// type: no effect is involved.
let repr (a:Type) (st:Type0) (pre:pre_t st) (post:post_t st a) : Type =
  s0:st{pre s0} -> r:(a & st){post s0 (fst r) (snd r)}

/// `repr` is an indexed monad.

/// Returning a value `x`
///
/// "The specification of return is the return of the specification"
let return (a:Type) (x:a) (st:Type0)
  : repr a st (fun _ -> True) (return_post x)
  = fun s0 -> (x, s0)

/// Sequentially composing computations
///
/// "The specification of a bind is the bind of the specification"
let bind (a:Type) (b:Type) (st:Type0)
         (pre_c:pre_t st) (post_c:post_t st a)
         (pre_f:a -> pre_t st) (post_f:a -> post_t st b)
         (c : repr a st pre_c post_c)
         (f : (x:a -> repr b st (pre_f x) (post_f x)))
  : repr b st (bind_pre pre_c post_c pre_f) (bind_post post_c post_f)
  = fun s0 -> let (y, s1) = c s0 in
           f y s1

/// You can also define a notion of subsumption of our computation type:
/// a computation may always be given a weaker precondition and a
/// stronger postcondition.
let stronger
  (#a:Type) (#st:Type0)
  (pre1:pre_t st) (post1:post_t st a)
  (pre2:pre_t st) (post2:post_t st a)
  : prop
  = (forall s0. pre2 s0 ==> pre1 s0) /\
    (forall s0 x s1. pre2 s0 /\ post1 s0 x s1 ==> post2 s0 x s1)

let subcomp
  (a:Type)
  (st:Type0)
  (pre1:pre_t st) (post1:post_t st a)
  (pre2:pre_t st) (post2:post_t st a)
  (f : repr a st pre1 post1)
  : Pure (repr a st pre2 post2)
         (requires stronger pre1 post1 pre2 post2)
         (ensures fun _ -> True)
  = fun s0 -> f s0

(*** Step 3: Programming with it ***)

/// F* used to package such an indexed monad up as an *effect*, so that
/// the type checker would infer the indices of every `bind`.  That is
/// no longer needed for specifications --- every F* effect is already
/// specified by a pre- and a postcondition --- so we simply program
/// with `bind` directly.  The `let!` notation makes that pleasant.

let ( let! ) (#a #b:Type) (#st:Type0)
             (#pre_c:pre_t st) (#post_c:post_t st a)
             (#pre_f:a -> pre_t st) (#post_f:a -> post_t st b)
             (c : repr a st pre_c post_c)
             (f : (x:a -> repr b st (pre_f x) (post_f x)))
  : repr b st (bind_pre pre_c post_c pre_f) (bind_post post_c post_f)
  = bind a b st pre_c post_c pre_f post_f c f

/// Reading the state
let get (#st:Type0) ()
  : repr st st (fun _ -> True) (fun s0 x s1 -> x == s0 /\ s1 == s0)
  = fun s0 -> (s0, s0)

/// Writing the state
let put (#st:Type0) (s:st)
  : repr unit st (fun _ -> True) (fun _ _ s1 -> s1 == s)
  = fun _ -> ((), s)

/// And finally: here is a proof of `double`.  The composed
/// specification is inferred by `let!`; `subcomp` weakens it to the one
/// we want to advertise.
let double ()
  : repr unit int (fun _ -> True) (fun s0 _ s1 -> s1 == s0 + s0)
  = subcomp _ _ _ _ _ _ (let! x = get () in
                         put (x + x))
