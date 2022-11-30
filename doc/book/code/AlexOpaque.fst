module AlexOpaque

//SNIPPET_START: opaque$
[@@"opaque_to_smt"]
let unbounded (f: ℕ → ℤ) = ∀ (m: ℕ). ∃ (n:ℕ). abs (f n) > m

let instantiate_unbounded (f:ℕ → ℤ { unbounded f }) (m:ℕ)
  : Lemma (∃ (n:ℕ). abs (f n) > m)
  = reveal_opaque (`%unbounded) (unbounded f)

assume
val f : (z:(ℕ → ℤ){unbounded z})

let g : (nat -> int) = fun x -> f (x+1)

#push-options "--query_stats --fuel 0 --ifuel 0"
let find_above_for_g (m:nat) : Lemma(exists (i:nat). abs(g i) > m) = 
  instantiate_unbounded f m;
  eliminate exists (n:nat). abs(f n) > m
  returns exists (i:nat). abs(g i) > m with _. begin
    let m1 = abs(f n) in
    if n>=1 then assert (abs(g (n-1)) > m)
    else begin
      instantiate_unbounded f m1;
      eliminate exists (n1:nat). abs (f n1) > m1
      returns exists (i:nat). abs(g i) > m with _. 
      begin
        assert (abs (g (n1-1)) > m)
      end 
    end 
  end 
//SNIPPET_END: opaque$


//SNIPPET_START: trigger$

let trigger (x:int) = True

let unbounded_alt (f: ℕ → ℤ) = ∀ (m: ℕ). {:pattern (trigger m)} (∃ (n:ℕ). abs (f n) > m)

assume
val ff : (z:(ℕ → ℤ){unbounded_alt z})

let gg : (nat -> int) = fun x -> ff (x+1)

#push-options "--query_stats --fuel 0 --ifuel 0"
let find_above_for_gg (m:nat) : Lemma(exists (i:nat). abs(gg i) > m) = 
  assert (unbounded_alt ff);
  assert (trigger m);
  eliminate exists (n:nat). abs(ff n) > m
  returns exists (i:nat). abs(gg i) > m with _. begin
    let m1 = abs(ff n) in
    if n>=1 then assert (abs(gg (n-1)) > m)
    else begin
      assert (trigger m1);
      eliminate exists (n1:nat). abs (ff n1) > m1
      returns exists (i:nat). abs(gg i) > m with _. 
      begin
        assert (abs (gg (n1-1)) > m)
      end 
    end 
  end 
//SNIPPET_END: trigger$

//SNIPPET_START: trigger_exists$
let find_above_for_g1 (m:nat) : Lemma(exists (i:nat). abs(g i) > m) = 
  instantiate_unbounded f m;
  eliminate exists (n:nat). abs(f n) > m
  returns exists (i:nat). abs(g i) > m with _. begin
    let m1 = abs(f n) in
    if n>=1 then assert (trigger (g (n-1)))
    else begin
      instantiate_unbounded f m1;
      eliminate exists (n1:nat). abs (f n1) > m1
      returns exists (i:nat). abs(g i) > m with _. 
      begin
        assert (trigger (g (n1-1)))
      end 
    end 
  end 
//SNIPPET_END: trigger_exists$

//SNIPPET_START: explicit_exists$
let find_above_for_g' (m:nat) : Lemma(exists (i:nat). abs(g i) > m) = 
  instantiate_unbounded f m;
  eliminate exists (n:nat). abs(f n) > m
  returns exists (i:nat). abs(g i) > m with _. begin
    let m1 = abs(f n) in
    if n>=1 then (
      introduce exists (i:nat). abs(g i) > m 
      with (n - 1)
      and ()
    )
    else begin
      instantiate_unbounded f m1;
      eliminate exists (n1:nat). abs (f n1) > m1
      returns exists (i:nat). abs(g i) > m with _. 
      begin 
        introduce exists (i:nat). abs (g i) > m
        with (n1 - 1)
        and ()
      end 
    end 
  end 
//SNIPPET_END: explicit_exists$
