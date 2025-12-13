module FlyDepsUncheckedDeps
let fdud = 0
let unsound_smt_lemma (a:Type) (l:list a)
: Lemma 
  (ensures FStar.List.Tot.length l > 0)
  [SMTPat (FStar.List.Tot.length l)]
= admit()