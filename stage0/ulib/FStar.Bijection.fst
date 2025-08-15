module FStar.Bijection

let inv_lemma_pat (#a #b : _) (d : a =~ b) (x:a) (y:b)
  : Lemma ((x >> d) == y <==> x == (y << d))
          [SMTPat (d.right x); SMTPat (d.left y)]
  = d.right_left y;
    d.left_right x
