module FStar.Witnessed.Core
module P = FStar.Preorder

(* This is just to give definitions to the witnessed type for extraction.
   It is NOT a semantic model of the witnessed modality *)
   
let witnessed (state:Type u#a)
              (rel:P.preorder state)
              (p:s_predicate state)
  : Type0
  = unit
  
let witnessed_proof_irrelevant 
      (state:Type u#a)
      (rel:P.preorder state)
      (p:s_predicate state)
      (w0 w1:witnessed state rel p)
  : Lemma (w0 == w1)
  = ()
