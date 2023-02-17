module Steel.ST.GenElim.Base

irreducible let gen_elim_reduce = ()

[@@noextract_to "Plugin"]
let gen_elim_pred
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type u#1)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (ij: (gen_elim_i & gen_elim_nondep_t))
: Tot prop
= let (i, j) = ij in
  p == compute_gen_elim_p i /\
  check_gen_elim_nondep_sem i j /\ 
  a == compute_gen_elim_nondep_a i j /\
  post == compute_gen_elim_nondep_post i j /\
  q == compute_gen_elim_nondep_q i j

let gen_elim_prop
  enable_nondep_opt p a q post
= exists ij . gen_elim_pred enable_nondep_opt p a q post ij

let gen_elim_prop_intro'
  i j enable_nondep_opt p a q post sq_p sq_j sq_a sq_q sq_post
= assert (gen_elim_pred enable_nondep_opt p a q post (i, j))

let gen_elim_prop_elim enable_nondep_opt p a q post =
  FStar.IndefiniteDescription.indefinite_description_ghost _ (gen_elim_pred enable_nondep_opt p a q post)
