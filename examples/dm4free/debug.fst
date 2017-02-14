module Debug

open FStar.DM4F.Memo

(* Trying to prove that the the result of the reification in the recursive case *)
(* results in the same thing as the reification of the body of the function *)
(* Does not verify *)

#set-options "--z3rlimit 100"

(* let bidule f x x' px (cont : codom -> Tot (partial_result x)) h0 = *)
(*   assume (x' << x) ; *)
(*   (\* let y0, h01 = reify ( *\) *)
(*   (\*   let p x' = %[ %[x'; 1 ; ()] ] << %[ %[x; 0 ; px] ] in *\) *)
(*   (\*   let h (x:dom{p x}) : Memo codom = memo_rec_extr f x in *\) *)
(*   (\*   memo_f_extr_p p h x') h0 in *\) *)
(*   (\* let y,h1 = reify (complete_memo_rec_extr f x (cont y0)) h01 in *\) *)
(*   let y,h1 = reify begin *)
(*     (\* (fun f x (px:partial_result x) -> *\) *)
(*     (\*   match px with *\) *)
(*     (\*   | Done _ y -> y *\) *)
(*     (\*   | Need x0 x' cont -> *\) *)
(*         let y = memo_f_extr_p (p x px) (bidule f x px) x' in *)
(*         assume (forall y. cont y << cont) ; *)
(*         complete_memo_rec_extr f x (cont y) *)
(*         (\* ) f x (Need x x' cont) *\) *)
(*     end h0 *)
(*   in *)
(*   let y',h1' = reify (complete_memo_rec_extr f x (Need x x' cont)) h0 in *)
(*   assert (y == y') ; *)
(*   assert (h1 == h1') *)
open FStar.Classical
open FStar.Squash

let rec complete_memo_rec_extr_computes :
  (f:(x:dom -> partial_result x)) ->
  (x:dom) ->
  (px:partial_result x) ->
  (h0:heap) ->
  Lemma (requires (fpartial_result x f px /\ valid_memo h0 (fixp f)))
    (ensures (let y, h1 = reify (complete_memo_rec_extr f x px) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))
    (decreases %[x ; 0 ; px])
= fun f x px h0 ->
  match px with
  | Done _ y -> ()
  | Need x0 x' cont ->
    let compute_lemma0 (h0:heap) (vm:squash(valid_memo h0 (fixp f))) (x':dom) (px':squash (p x px x'))
        : Lemma (p x px x' ==> (let y, h1 = reify (memo_rec_extr_temp f x px x') h0 in y == fixp f x' /\ valid_memo h1 (fixp f)))
    =
      give_proof vm ;
      give_proof px' ;
      memo_rec_extr_computes f x' h0 (* ; *)
      (* assert (reify (memo_rec_extr_temp f x px x') h0 = reify (memo_rec_extr f x') h0) ; *)
      (* let y, h1 = reify (memo_rec_extr_temp f x px x') h0 in *)
      (* assert (y == fixp f x') ; *)
      (* assert(valid_memo h1 (fixp f)) *)
    in
    let compute_lemma1 (h0:heap) (vm:squash(valid_memo h0 (fixp f)))
      : Lemma (forall x'. p x px x' ==> (let y, h1 = reify (memo_rec_extr_temp f x px x') h0 in y == fixp f x' /\ valid_memo h1 (fixp f)))
    = forall_impl_intro (compute_lemma0 h0 vm)
    in
    forall_impl_intro compute_lemma1 ;
    assert (computes #(p x px) (memo_rec_extr_temp f x px) (fixp f)) ;

    memo_f_extr_computes (p x px) (memo_rec_extr_temp f x px) (fixp f) ;
    let y, h1 = reify (memo_f_extr_p (p x px) (memo_rec_extr_temp f x px) x') h0 in
    assert (y == fixp f x') ;
    assert (valid_memo h1 (fixp f)) ;
    assume (forall y. cont y << cont) ;
    complete_memo_rec_extr_computes f x (cont y) h1 ;
    let y, h1 = reify (complete_memo_rec_extr f x (cont y)) h1 in
    assert (y == fixp f x) ;
    assert (valid_memo h1 (fixp f)) ;
    assert (x == x0) ;
    assert (px == Need x0 x' cont) ;
    let y', h1' = reify (complete_memo_rec_extr f x px) h0 in
    (* These should be assertions, not assumptions !!! *)
    assert (y == y') ;
    assert (h1 == h1')

and memo_rec_extr_computes :
  (f:(x:dom -> partial_result x)) ->
  (x:dom) ->
  (h0:heap) ->
  Lemma (requires (valid_memo h0 (fixp f)))
    (ensures (let y, h1 = reify (memo_rec_extr f x) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))
    (decreases %[x ; 1 ; ()])
= fun f x h0 ->
  fpartial_result_lemma f x (f x) Now ;
  complete_memo_rec_extr_computes f x (f x) h0



(* let memo_rec_extr_computes (f:x:dom -> Tot (partial_result x)) *)
(*   : Lemma ((memo_rec_extr f) `computes` (fixp f)) *)
(* = memo_rec_extr_lemma *)
