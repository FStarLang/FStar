module Phase2CoreKindByEval

(* Relating two applications of a [unifier_hint_injective] head, here
   [parser (k1 n) (vlarray ..)] and [parser (k2 ..) t5], Core relates their
   arguments ([k1 n == k2 ..], provable by evaluation) rather than their
   unfoldings, whose guard would equate two refinement types, as Rel does
   (everparse qd tests T5). *)

noeq type kind = { lo: nat; hi: option nat }
let rec log2' (n:nat) : Tot nat (decreases n) = if n < 2 then 0 else 1 + log2' (n / 2)
let k1 (n:nat) : kind = { lo = log2' n + 1; hi = Some (log2' n + n) }
let k2 (a b:nat) : kind = { lo = a; hi = Some b }
assume val kind_prop (#a:Type) (k:kind) (f: int -> a) : prop
[@unifier_hint_injective]
let parser (k:kind) (t:Type) = f:(int -> t){kind_prop k f}
let vlarray (t:Type) (min max:nat) = l:list t{min <= List.Tot.length l /\ List.Tot.length l <= max}
assume val mk (n:nat) : parser (k1 n) (vlarray bool 0 n)

type t5 = l:list bool{0 <= List.Tot.length l /\ List.Tot.length l <= 255}
let k_p = k2 8 262
val p : parser k_p t5
let p = mk 255
