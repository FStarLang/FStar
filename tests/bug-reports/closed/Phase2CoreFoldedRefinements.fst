module Phase2CoreFoldedRefinements

(* Both [sum_cases ts (cce k)] and [t k] unfold to refinements whose base
   types, [sum_type ts] (a stuck [match] on [ts]) and [t'], never come to
   match: the guard is [sum_cases ts (cce k) == t k], provable from the SMT
   pattern of [lem] (everparse LowParseExample8.Aux). *)

type kt = | Ka | Kb
noeq type t' = | Ta of int | Tb of bool
let key (x:t') : kt = match x with Ta _ -> Ka | Tb _ -> Kb
let t (k:kt) : Type = x:t'{key x == k}
noeq type sum = | Sum : (data:Type) -> (tag: data -> kt) -> sum
let sum_type (s:sum) : Type = match s with Sum d _ -> d
let sum_tag (s:sum) : sum_type s -> kt = match s with Sum _ tg -> tg
let rwt (#a:Type) (#b:Type) (tag: b -> a) (x:a) = y:b{tag y == x}
let sum_cases (s:sum) (k:kt) : Type = rwt #kt #(sum_type s) (sum_tag s) k
let mk_sum (d:Type) (tg: d -> kt) = Sum d tg
let ts : sum = mk_sum t' key
let cce (k:kt) : kt = match k with Ka -> Ka | Kb -> Kb
let parser (t:Type) = int -> option (t & nat)
assume val p (s:sum) (k:kt) : parser (sum_cases s k)
let lem (k:kt) : Lemma (t k == sum_cases ts (cce k)) [SMTPat (t k)] =
  match k with
  | Ka -> assert_norm (t Ka == sum_cases ts (cce Ka))
  | Kb -> assert_norm (t Kb == sum_cases ts (cce Kb))
let parse_t (k:kt) : parser (t k) = p ts (cce k)
