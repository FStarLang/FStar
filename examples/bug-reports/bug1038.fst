module Bug1038
open FStar.List

assume val pairs_with_sum (n: nat) : list (p:(nat * nat){fst p + snd p == n})

assume val pws_complete (m n: nat) : Lemma (List.memP #(p:(nat * nat){fst p + snd p == (m + n)}) (m, n) (pairs_with_sum (m + n)))

let tos_complete (s s1 s2: nat) : Lemma (True) =
    pws_complete s1 s2;
    assume (s1 + s2 == s);
    (* let s = s1 + s2 in -- replacing assume with let makes everything work *)
    // This works:
    (* assert (List.memP (s1, s2) (pairs_with_sum (s1 + s2))); *)
    // This also works:
    (* assert (List.memP #(p:(nat * nat){fst p + snd p == (s1 + s2)}) (s1, s2) (pairs_with_sum s)); *)
    // But this fails (on its own):
    assert (List.memP #(p:(nat * nat){fst p + snd p == s}) (s1, s2) (pairs_with_sum s));
    admit ()
