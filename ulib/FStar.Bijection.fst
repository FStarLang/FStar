module FStar.Bijection

open FStar.Functions { pigeon }

let bij_inv_nopat (#a #b : _) (d : a =~ b) (x:a) (y:b)
  : Lemma (d.right x == y <==> x == d.left y)
  = d.right_left y;
    d.left_right x

let bij_inv_fwd (#a #b : _) (d : a =~ b) (x:a)
  : Lemma (x == d.left (d.right x))
          [SMTPat (d.right x)]
  = bij_inv_nopat d x (d.right x)

let bij_inv_bk (#a #b : _) (d : a =~ b) (y:b)
  : Lemma (y == d.right (d.left y))
          [SMTPat (d.left y)]
  = bij_inv_nopat d (d.left y) y

let inv_lemma_pat (#a #b : _) (d : a =~ b) (x:a) (y:b)
  : Lemma ((x >> d) == y <==> x == (y << d))
          [SMTPat (d.right x); SMTPat (d.left y)]
  = d.right_left y;
    d.left_right x

let __bij_cardinal (n1 n2 : nat) (bij : fin n1 =~ fin n2)
  : Lemma (n1 == n2) =
  if n1 > n2 then pigeon n1 n2 bij.right;
  if n1 < n2 then pigeon n2 n1 bij.left;
  ()

let bij_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 =~ fin n2). True)
          (ensures n1 == n2)
  = Classical.forall_intro (__bij_cardinal n1 n2)
