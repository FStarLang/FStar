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

(*
 * An alternative formulation of LowStar modifies transitivity lemma that is goal directed
 * The intended usage is for the clients to remove LowStar.Monotonic.Buffer.modifies_trans
 *   from the context using --using_facts_from
 *   and include this module
 *
 * Over time we hope to remove modifies_trans and make the following default
 *
 * See also #1592 for more discussions
 * And examples/bug-reports/Bug1592.fst for an example usage
 *)

module LowStar.Modifies.Linear

open LowStar.Monotonic.Buffer

module HS = FStar.HyperStack

let modifies_trans_linear (s l:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies s h1 h2 /\ modifies l h2 h3 /\ loc_includes l s))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies s h1 h2); SMTPat (modifies l h1 h3)]
  = ()
