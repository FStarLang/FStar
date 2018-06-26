module UnifyRefs

unfold let pow2_32 = 0x100000000
unfold let pow2_64 = 0x10000000000000000

let natN (n:nat) = x:nat{x < n}
let nat32 = natN pow2_32
let nat64 = natN pow2_64

(* These tests SHOULD NOT REALLY FAIL!
 *
 * We're just *admitting* them for now, until we fix #606. Related: #1345.
 *
 * Keeping them in here, and thus CI, is a good way to not forget and to
 * not inadvertedly change the situation. If you find some test starts
 * passing, (and therefore failing due to the @fail) that's good, just
 * remove the @fail.
 *
 * Do try to not add back any @fail's, please.
 *)

[@fail]
let nat32_to_nat64'0 (n:nat32) : nat64 = n

[@fail]
let nat32_to_nat64'1 (n:natN pow2_32) : nat64 = n

[@fail]
let nat32_to_nat64'2 (n:nat32) : natN pow2_64 = n

[@fail]
let nat32_to_nat64'3 (n:natN pow2_32) : natN pow2_64 = n

[@fail]
let nat64_to_nat32'0 (n:nat64 {n < pow2_32}) : nat32 = n

[@fail]
let nat64_to_nat32'1 (n:nat64 {n < pow2_32}) : natN pow2_32 = n

[@fail]
let nat64_to_nat32'2 (n:natN pow2_64 {n < pow2_32}) : nat32 = n

[@fail]
let nat64_to_nat32'3 (n:natN pow2_64 {n < pow2_32}) : natN pow2_32 = n

(* Unfolding manually causes the unifier to do more work, and succeed *)

let nat32_to_nat64'4 (n:nat{n < pow2_32}) : natN pow2_64 = n

let nat32_to_nat64'5 (n:nat32) : (x:nat{x < pow2_64}) = n

let nat64_to_nat32'4 (n:(x:nat{x < pow2_64}) {n < pow2_32}) : nat32 = n

let nat64_to_nat32'5 (n:nat64 {n < pow2_32}) : (n:nat{n < pow2_32}) = n
