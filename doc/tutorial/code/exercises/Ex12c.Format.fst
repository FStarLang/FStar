module Ex12c.Format

open FStar.String
open Platform.Bytes         //This shadows length, index etc. from FStar.Seq, for no good reason?
open FStar.Seq              //It's really important for FStar.Seq.index to have precedence for proper use of the lemmas in FStar.Seq
open FStar.Classical

type message = bytes
type msg (l:nat) = lbytes l

(* ----- a lemma on array append *)
// BEGIN: FormatAppendEx
val append_inj_lemma: b1:message -> b2:message
                   -> c1:message -> c2:message
                   -> Lemma (requires (length b1==length c1 
		                      /\ b2t (Seq.eq (b1 @| b2) (c1 @| c2))))
                           (ensures (b2t (Seq.eq b1 c1) /\ b2t (Seq.eq b2 c2)))
                           [SMTPat (b1 @| b2); SMTPat (c1 @| c2)] 
			   (* given to the SMT solver *)
let append_inj_lemma b1 b2 c1 c2 =
  lemma_append_len_disj b1 b2 c1 c2;
  Classical.forall_intro 
    #_ 
    #(fun (x:(i:nat{i < length b1})) -> index b1 x == index c1 x) 
    (lemma_append_inj_l b1 b2 c1 c2); 
    //currently the 2nd implicit argument has to be provided explicitly
  admit()
// END: FormatAppendEx
