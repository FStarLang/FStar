module IfaceErasableFold

(* The erasability check (warning 318) on definitions that have an interface
   val used to normalize the body of [layer] to HNF, unrolling the recursive
   fold below and blowing up exponentially in memory. It must only look at
   definitions of types. *)
let step a z0 z1 z2 z3 = a + z0 + z1 + z2 + z3
let zeta i = 0

let rec fold_range (#acc_t: Type0) (start: nat) (end_: nat)
  (inv: acc_t -> (i:nat{start <= i /\ i <= end_}) -> prop)
  (init: acc_t {start <= end_ ==> inv init start})
  (f: (acc:acc_t -> i:nat{start <= i /\ i < end_ /\ inv acc i} -> acc':acc_t{inv acc' (i + 1)}))
  : Tot (r: acc_t{start > end_ ==> r == init}) (decreases end_ - start)
  = if start < end_ then fold_range (start + 1) end_ (fun a (i:nat{start + 1 <= i /\ i <= end_}) -> inv a i) (f init start) (fun a i -> f a i) else init

let layer zeta_i re =
  let (re, zeta_i) =
    fold_range 0 16 (fun _ _ -> True) (re, zeta_i)
      (fun (re, zeta_i) round ->
        let zeta_i = (zeta_i + 1) % 64 in
        let re = if Seq.length re > round then
                   Seq.upd re round (Seq.index re round + 1)
                 else re in
        (re, zeta_i + 3))
  in (zeta_i, re)
