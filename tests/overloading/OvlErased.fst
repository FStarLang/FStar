module OvlErased
open FStar.Ghost
open OvlInt
open OvlBool
open OvlGhostA
open OvlGhostB
open OvlGhostCoercion
open OvlGhostCoercionB

(* [erased t] is the one head whose type argument overload resolution has to
   look at. [hide] and [reveal] relate an [erased t] to a [t] and to nothing
   else, so an [erased t] reaches exactly what a [t] reaches -- treating
   [erased] as a head compatible with everything instead keeps candidates the
   elaborator can never reach. See #4471. *)

(* 1. The report. [FStar.UInt64] is opened over [Prims], so [>=] is
   [FStar.UInt64.op_Greater_Equals] by scope order. Its formals are
   [FStar.UInt64.t], which no coercion can produce from an [erased nat]:
   [reveal] gives a [nat] and stops there. The answer is
   [Prims.op_Greater_Equals]. *)
open FStar.UInt64
let ge_erased (x y : erased nat) = x >= y

(* 2. [reveal] on an argument. [OvlBool.f] takes a [bool] and [OvlInt.f] an
   [int], and only the latter is what an [erased int] reveals to. *)
let arg_revealed (x : erased int) : GTot int = f x

(* 3. [hide] on an argument, the same thing in the other direction:
   [OvlGhostB.h] is the scope-order answer and takes a [bool], while an [int]
   hides into the [erased int] that [OvlGhostA.h] takes. *)
let arg_hidden (x : int) : int = h x

(* 4. And on the result: [OvlBool.mk] returns an [OvlBool.t], [OvlInt.mk] an
   [OvlInt.t], and the expected type is the latter under [erased]. *)
let result_hidden (x : int) : erased OvlInt.t = mk x

(* 5. Stripping [erased] must not hide a [@@coercion] that names [erased] as
   one of its ends. [OvlGhostCoercionB.k] is the scope-order answer and takes
   a [bool]; only [OvlGhostCoercion.k] can receive an [erased int], and only
   because [erased_to_ghint] says so. *)
let arg_user_coerced (x : erased int) : GTot int = k x
