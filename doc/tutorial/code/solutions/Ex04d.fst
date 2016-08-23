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

(* Perhaps you did it like this: *)

// BEGIN: RevInjective1
val snoc_injective: #t:eqtype -> l1:list t -> h1:t -> l2:list t -> h2:t
                 -> Lemma (requires (snoc l1 h1 = snoc l2 h2))
                          (ensures (l1 = l2 && h1 = h2))
let rec snoc_injective #t l1 h1 l2 h2 = match l1, l2 with
  | _::tl1, _::tl2 -> snoc_injective tl1 h1 tl2 h2
  | _ -> ()

val rev_injective_1: #t:eqtype -> l1:list t -> l2:list t
                -> Lemma (requires (reverse l1 = reverse l2))
                         (ensures  (l1 = l2)) (decreases l1)
let rec rev_injective_1 #t l1 l2 =
  match l1,l2 with
  | h1::t1, h2::t2 ->
      // assert(reverse (h1::t1) = reverse (h2::t2));
      // assert(snoc (reverse t1) h1  = snoc (reverse t2) h2);
      snoc_injective (reverse t1) h1 (reverse t2) h2;
      // assert(reverse t1 = reverse t2 /\ h1 = h2);
      rev_injective_1 t1 t2
      // assert(t1 = t2 /\ h1::t1 = h2::t2)
  | _, _ -> ()
// END: RevInjective1

(* That's quite a tedious proof, isn't it. Here's a simpler proof. *)

// BEGIN: RevInjective2
val rev_injective_2: #t:eqtype -> l1:list t -> l2:list t 
                -> Lemma (requires (reverse l1 = reverse l2))
                         (ensures  (l1 = l2))
let rev_injective_2 #t l1 l2 = rev_involutive l1; rev_involutive l2
// END: RevInjective2

(* The `rev_injective_2` proof is based on the idea that every involutive
function is injective. We've already proven that `reverse` is
involutive. So, we invoke our lemma, once for `l1` and once for `l2`.
This gives to the SMT solver the information that `reverse (reverse
l1) = l1` and `reverse (reverse l2) = l2`, which suffices to complete
the proof. As usual, when structuring proofs, lemmas are your friends! *)
