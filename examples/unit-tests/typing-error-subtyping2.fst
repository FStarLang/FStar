module Sub2

assume val mem : 'a -> list 'a -> Tot bool

val xxx : list 'a -> Tot (l:list 'a{forall (x : 'a). mem x l ==> False})
let xxx l = l

(* This one requires reduction below a quantifier
Subtyping check failed; expected type
[Before:l:(list 'a){(Forall #'a (fun x:'a => (l_imp (b2t (mem #'a x l)) False)))}]
[After:l:(list 'a){(forall x:'a. (b2t (mem #'a x l)) ==> False)}];
got type
[Before:((fun 'a:Type => (list 'a)) 'a)]
[After:(list 'a)]
(typing-error.fst(6,12-6,13))
*)
