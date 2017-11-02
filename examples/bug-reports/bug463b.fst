module Bug463b

open FStar.List.Tot

val move_refinement:
  #a:Type{hasEq a}
  -> #p:(a -> Type)
  -> l:(list a){forall z. mem z l ==> p z}
  -> Tot (list (x:a{p x}))

let rec move_refinement (#a:Type{hasEq a}) (#p:(a -> Type)) l = match l with
  | [] -> []
  | hd::tl -> hd::move_refinement #a #p tl

val eq1 : #a:Type{hasEq a}
  -> #p:(a -> Type)
  -> hd:a{p hd} -> tl:(list a){forall z. mem z tl ==> p z} ->
     Lemma (requires True)
            (ensures (length (move_refinement #a #p (hd::tl)) =
                      length (hd::move_refinement #a #p tl)))
let eq1 #a #p hd tl = ()

val eq2 :   #a:Type{hasEq a}
  -> #p:(a -> Type)
  -> hd:a{p hd} -> tl:(list a){forall z. mem z tl ==> p z} ->
     Lemma (requires True)
            (ensures (length (hd::move_refinement #a #p tl) =
                      1+length (move_refinement #a #p tl)))
let eq2 #a #p hd tl = ()

val lemma_move_refinement_length:
  #a:Type{hasEq a}
  -> #p:(a -> Type)
  -> l:(list a){forall z. mem z l ==> p z}
  -> Lemma (requires (True))
           (ensures ((length l) = (length (move_refinement #a #p l))))
let rec lemma_move_refinement_length (#a:Type{hasEq a}) (#p:(a -> Type)) l =
  match l with
  | [] -> admit()
  | hd::tl ->
     (* for some obscure reasons these assertions fail *)
     (* assert(length (hd::move_refinement #a #p tl) = *)
     (*      1+length (move_refinement #a #p tl)); *)
     (* assert(length (hd::move_refinement #a #p tl) = *)
     (*                  1+length (move_refinement #a #p tl)); *)
     (* but we can still call lemmas to make this work*)
     eq1 #a #p hd tl;
     eq2 #a #p hd tl;
     lemma_move_refinement_length #a #p tl
