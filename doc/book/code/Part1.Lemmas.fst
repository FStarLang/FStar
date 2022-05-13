module Part1.Lemmas
open FStar.Mul
open Part1.Inductives

let rec factorial (x:nat)
  : nat
  = if x = 0
    then 1
    else x * factorial (x - 1)

//SNIPPET_START: factorial_is_positive
let rec factorial_is_positive (x:nat)
  : u:unit{factorial x > 0}
  = if x = 0 then ()
    else factorial_is_positive (x - 1)
//SNIPPET_END: factorial_is_positive


//SNIPPET_START: factorial_is_positive_lemma
let rec factorial_is_pos (x:int)
  : Lemma (requires x >= 0)
          (ensures factorial x > 0)
  = if x = 0 then ()
    else factorial_is_pos (x - 1)
//SNIPPET_END: factorial_is_positive_lemma


//SNIPPET_START: factorial_is_greater_than_arg
let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
  = if x = 3 then ()
    else factorial_is_greater_than_arg (x - 1)
//SNIPPET_END: factorial_is_greater_than_arg

//SNIPPET_START: fibonacci_question
let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
//SNIPPET_END: fibonacci_question

//SNIPPET_START: fibonacci_answer
let rec fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
  = if n <= 3 then ()
    else (
      fibonacci_greater_than_arg (n - 1);
      fibonacci_greater_than_arg (n - 2)
    )
//SNIPPET_END: fibonacci_answer


//SNIPPET_START: fibonacci_answer_alt
let rec fib_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
  = if n = 2 then ()
    else (
      fib_greater_than_arg (n - 1)
    )
//SNIPPET_END: fibonacci_answer_alt

//SNIPPET_START: def append alt
let rec app #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: app tl l2
//SNIPPET_END: def append alt

//SNIPPET_START: sig app_length
val app_length (#a:Type) (l1 l2:list a)
  : Lemma (length (app l1 l2) = length l1 + length l2)
//SNIPPET_END: sig app_length

//SNIPPET_START: def app_length
let rec app_length #a l1 l2
  = match l1 with
    | [] -> ()
    | _ :: tl -> app_length tl l2
//SNIPPET_END: def app_length


//SNIPPET_START: reverse
let rec reverse #a (l:list a)
  : list a
  = match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]
//SNIPPET_END: reverse

//SNIPPET_START: reverse_involutive
(* snoc is "cons" backwards --- it adds an element to the end of a list *)
let snoc l h = append l [h]

let rec snoc_cons #a (l:list a) (h:a)
  : Lemma (reverse (snoc l h) == h :: reverse l)
  = match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h

let rec rev_involutive #a (l:list a)
  : Lemma (reverse (reverse l) == l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      // (1) [reverse (reverse tl) == tl]
      rev_involutive tl;
      // (2) [reverse (append (reverse tl) [hd]) == h :: reverse (reverse tl)]
      snoc_cons (reverse tl) hd
      // These two facts are enough for Z3 to prove the lemma:
      //   reverse (reverse (hd :: tl))
      //   =def= reverse (append (reverse tl) [hd])
      //   =(2)= hd :: reverse (reverse tl)
      //   =(1)= hd :: tl
      //   =def= l
//SNIPPET_END: reverse_involutive

// SNIPPET_START: sig rev_injective
val rev_injective (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
// SNIPPET_END: sig rev_injective

// SNIPPET_START: def rev_injective
let rec snoc_injective (#a:Type) (l1:list a) (h1:a) (l2:list a) (h2:a)
  : Lemma (requires snoc l1 h1 == snoc l2 h2)
          (ensures l1 == l2 /\ h1 == h2)
  = match l1, l2 with
    | _ :: tl1, _ :: tl2 -> snoc_injective tl1 h1 tl2 h2
    | _ -> ()


let rec rev_injective l1 l2 =
  match l1,l2 with
  | h1::t1, h2::t2 ->
      // assert(reverse (h1::t1) = reverse (h2::t2));
      // assert(snoc (reverse t1) h1  = snoc (reverse t2) h2);
      snoc_injective (reverse t1) h1 (reverse t2) h2;
      // assert(reverse t1 = reverse t2 /\ h1 = h2);
      rev_injective t1 t2
      // assert(t1 = t2 /\ h1::t1 = h2::t2)
  | _, _ -> ()
// SNIPPET_END: def rev_injective

(* That's quite a tedious proof, isn't it. Here's a simpler proof. *)

// SNIPPET_START: rev_injective_alt
let rev_injective_alt (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = rev_involutive l1; rev_involutive l2
// SNIPPET_END: rev_injective_alt

(* The `rev_injective_alt` proof is based on the idea that every
    involutive function is injective. We've already proven that
    `reverse` is involutive. So, we invoke our lemma, once for `l1`
    and once for `l2`.  This gives to the SMT solver the information
    that `reverse (reverse l1) = l1` and `reverse (reverse l2) = l2`,
    which suffices to complete the proof. As usual, when structuring
    proofs, lemmas are your friends! *)

// SNIPPET_START: map
let rec map #a #b (f: a -> b) (l:list a)
  : list b
  = match l with
    | [] -> []
    | hd::tl -> f hd :: map f tl
// SNIPPET_END: map

// SNIPPET_START: sig find
val find (#a:Type) (f: a -> bool) (l:list a)
  : o:option a{ Some? o ==> f (Some?.v o)}
// SNIPPET_END: sig find

// SNIPPET_START: find
let rec find f l =
  match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find f tl
// SNIPPET_END: find

// SNIPPET_START: find_alt
let rec find_alt f l =
  match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find_alt f tl

let rec find_alt_ok #a (f:a -> bool) (l:list a)
  : Lemma (match find_alt f l with
           | Some x -> f x
           | _ -> true)
  = match l with
    | [] -> ()
    | _ :: tl -> find_alt_ok f tl
// SNIPPET_END: find_alt

// SNIPPET_START: def fold_left
let rec fold_left #a #b (f: b -> a -> a) (l: list b) (acc:a)
  : a
  = match l with
    | [] -> acc
    | hd :: tl -> fold_left f tl (f hd acc)
// SNIPPET_END: def fold_left

// SNIPPET_START: sig fold_left_Cons_is_rev
val fold_left_Cons_is_rev (#a:Type) (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
// SNIPPET_END: sig fold_left_Cons_is_rev

// SNIPPET_START: fold_left_Cons_is_rev
let rec append_assoc #a (l1 l2 l3 : list a)
  : Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
  = match l1 with
    | [] -> ()
    | h1 :: t1 -> append_assoc t1 l2 l3

let rec fold_left_Cons_is_rev_stronger #a (l1 l2: list a)
  : Lemma (fold_left Cons l1 l2 == append (reverse l1) l2)
  = match l1 with
    | [] -> ()
    | h1 :: t1 ->
      // (1) [append (append (reverse t1) [h1]) l2
      //      == append (reverse t1) (append [h1] l2)]
      append_assoc (reverse t1) [h1] l2;
      // (2) [fold_left Cons t1 (h1 :: l2) = append (reverse t1) (h1 :: l2)]
      fold_left_Cons_is_rev_stronger t1 (h1 :: l2)
      // append (reverse l1) l2
      // =def= append (append (reverse t1) [h1]) l2
      // =(1)= append (reverse t1) (append [h1] l2)
      // =def= append (reverse t1) (h1 :: l2)
      // =(2)= fold_left Cons t1 (h1 :: l2)
      // =def= fold_left Cons l1 l2

let rec append_right_unit #a (l1:list a)
  : Lemma (append l1 [] == l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> append_right_unit tl

let fold_left_Cons_is_rev #a (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
  = fold_left_Cons_is_rev_stronger l [];
    append_right_unit (reverse l)
// SNIPPET_END: fold_left_Cons_is_rev


let rec rev_aux #a (l1 l2:list a)
  : Tot (list a) (decreases l2)
  = match l2 with
    | []     -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl

let rev #a (l:list a) : list a = rev_aux [] l

// SNIPPET_START: rev_is_ok
let rec rev_is_ok_aux #a (l1 l2:list a)
  : Lemma (ensures (rev_aux l1 l2 == append (reverse l2) l1))
          (decreases l2)
  = match l2 with
    | [] -> ()
    | hd :: tl  -> rev_is_ok_aux (hd :: l1) tl;
                 append_assoc (reverse tl) [hd] l1

let rev_is_ok #a (l:list a)
  : Lemma (rev l == reverse l)
  = rev_is_ok_aux [] l;
    append_right_unit (reverse l)
// SNIPPET_END: rev_is_ok

let rec fib_aux (a b n:nat)
  : Tot nat (decreases n)
  = match n with
    | 0 -> a
    | _ -> fib_aux b (a+b) (n-1)

let fib (n:nat) : nat = fib_aux 1 1 n

// SNIPPET_START: fib_is_ok
let rec fib_is_ok_aux (n: nat) (k: nat)
  : Lemma (fib_aux (fibonacci k)
                   (fibonacci (k + 1)) n == fibonacci (k + n))
  = if n = 0 then () else fib_is_ok_aux (n - 1) (k + 1)

let fib_is_ok (n:nat)
  : Lemma (fibonacci n == fib n)
  = fib_is_ok_aux n 0
// SNIPPET_END: fib_is_ok
