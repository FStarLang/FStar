module X64.Vale.Regs_i
// This interface should not refer to Semantics_s

open X64.Machine_s

module F = FStar.FunctionalExtensionality

type t = F.restricted_t reg (fun _ -> nat64)

val equal : regs1:t -> regs2:t -> Type0

val lemma_equal_intro : regs1:t -> regs2:t -> Lemma
  (requires forall r. regs1 r == regs2 r)
  (ensures equal regs1 regs2)
  [SMTPat (equal regs1 regs2)]

val lemma_equal_elim : regs1:t -> regs2:t -> Lemma
  (requires equal regs1 regs2)
  (ensures regs1 == regs2)
  [SMTPat (equal regs1 regs2)]

