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
module Ex12c.Format

open FStar.String
open FStar.Bytes            //This shadows length, index etc. from FStar.Seq, for no good reason?
open FStar.Seq              //It's really important for FStar.Seq.index to have precedence for proper use of the lemmas in FStar.Seq
open FStar.Classical

type message = bytes
type msg (l:nat) = lbytes l

(* ----- a lemma on array append *)
// BEGIN: FormatAppendEx
val append_inj_lemma: b1:message -> b2:message {UInt.fits (Bytes.length b1 + Bytes.length b2) 32}
                   -> c1:message -> c2:message {UInt.fits (Bytes.length c1 + Bytes.length c2) 32}
                   -> Lemma (requires (Bytes.length b1==Bytes.length c1 
		                      /\ (Bytes.append b1 b2) = (Bytes.append c1 c2)))
                           (ensures (Bytes.equal b1 c1 /\ Bytes.equal b2 c2))
                           [SMTPat (Bytes.append b1 b2); SMTPat (Bytes.append c1 c2)] 
			   (* given to the SMT solver *)
let append_inj_lemma b1 b2 c1 c2 =
  lemma_append_len_disj (reveal b1) (reveal b2) (reveal c1) (reveal c2);
  Classical.forall_intro 
    #_ 
    #(fun (x:(i:nat{i < Bytes.length b1})) -> Bytes.index b1 x == Bytes.index c1 x) 
    (lemma_append_inj_l (reveal b1) (reveal b2) (reveal c1) (reveal c2)); 
    //currently the 2nd implicit argument has to be provided explicitly
  admit()
// END: FormatAppendEx
