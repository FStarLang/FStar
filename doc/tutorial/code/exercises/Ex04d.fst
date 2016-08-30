module Ex04d
//reverse

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

val snoc_cons: #t:eqtype -> l:list t -> h:t -> Lemma (reverse (snoc l h) = h::reverse l)
let rec snoc_cons #t l h = match l with
  | [] -> ()
  | hd::tl -> snoc_cons tl h 


val rev_involutive: #t:eqtype -> l:list t -> Lemma (reverse (reverse l) = l)
let rec rev_involutive #t l = match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; snoc_cons (reverse tl) hd

// BEGIN: RevInjective
val snoc_injective: #t:eqtype -> l1:list t -> h1:t -> l2:list t -> h2:t
                 -> Lemma (requires (snoc l1 h1 = snoc l2 h2))
                          (ensures (l1 = l2 && h1 = h2))
// END: RevInjective
