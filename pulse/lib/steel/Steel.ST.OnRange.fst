module Steel.ST.OnRange
open Steel.ST.GenElim

let rec on_range
  (p: (nat -> vprop))
  (i j: nat)
: Tot vprop
  (decreases (if j <= i then 0 else j - i))
= if j < i
  then pure False
  else if j = i
  then emp
  else p i `star` on_range p (i + 1) j

let on_range_le
  p i j
= if i <= j
  then noop ()
  else begin
    rewrite (on_range p i j) (pure False);
    let _ = gen_elim () in
    rewrite emp (on_range p i j); // by contradiction
    noop ()
  end

let on_range_empty
  p i j
= rewrite emp (on_range p i j)

let on_range_singleton_intro
  p i j
= rewrite (p i `star` emp) (on_range p i j)

let on_range_singleton_elim
  p i j
= rewrite (on_range p i j) (p i `star` emp)

let rec on_range_split
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (on_range p i k)
    (fun _ -> on_range p i j `star` on_range p j k)
    (i <= j /\ j <= k)
    (fun _ -> True)
    (decreases (j - i))
= if i = j
  then begin
    rewrite emp (on_range p i j);
    rewrite (on_range p i k) (on_range p j k)
  end else begin
    rewrite (on_range p i k) (p i `star` on_range p (i + 1) k);
    on_range_split p (i + 1) j k;
    rewrite (p i `star` on_range p (i + 1) j) (on_range p i j)
  end

let rec on_range_join
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhostT unit opened
    (on_range p i j `star` on_range p j k)
    (fun _ -> on_range p i k)
    (decreases (if j >= i then j - i else 0))
= on_range_le p i j;
  on_range_le p j k;
  if i = j
  then begin
    rewrite (on_range p i j) emp;
    rewrite (on_range p j k) (on_range p i k)
  end else begin
    rewrite (on_range p i j) (p i `star` on_range p (i + 1) j);
    on_range_join p (i + 1) j k;
    rewrite (p i `star` on_range p (i + 1) k) (on_range p i k)
  end
