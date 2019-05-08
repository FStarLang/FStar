(*
   Copyright 2008-2018 Microsoft Research

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

