module Alex

let unbounded (f: nat -> int) = forall (m: nat). exists (n:nat). abs (f n) > m

assume
val f : (f:(nat -> int){unbounded f})

let g : (nat -> int) = fun x -> f (x+1)

#push-options "--fuel 0 --ifuel 0 --z3smtopt '(set-option :smt.qi.eager_threshold 2)'"
let find_above_for_g (m:nat) : Lemma(exists (i:nat). abs(g i) > m) = 
  assert (unbounded f); // apply forall to m
  eliminate exists (n:nat). abs(f n) > m
  returns exists (i:nat). abs(g i) > m with _. begin
    let m1 = abs(f n) in
    assert (m1 > m); //prover hint
    if n>=1 then assert (abs(g (n-1)) > m)
    else begin
      assert (n<=0); //arithmetics hint
      eliminate exists (n1:nat). abs (f n1) > m1
      returns exists (i:nat). abs(g i) > m with _. 
      begin
        assert (n1 > 0);
        assert (abs (g (n1-1)) > m)
      end 
    end 
  end 

#pop-options
