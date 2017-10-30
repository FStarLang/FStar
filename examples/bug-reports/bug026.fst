module Bug026

assume val factorial : n:nat -> Tot nat
assume val bar:n:int{n > 1} -> Tot (y:int{y=factorial n})

val evenb: nat -> Tot bool
let evenb i = (i % 2) = 0

val filter: ('a -> Tot bool) -> list 'a -> Tot (list 'a)
let rec filter f l = match l with
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

val test_filter1 : unit -> Lemma
      (ensures (filter evenb [1;2;3;4] = [2;4]))
let test_filter1 () = ()

val evenb2: pos -> Tot bool
let evenb2 i = (i % 2) = 0

val test_filter2 : unit -> Lemma
      (ensures (filter evenb2 [1;2;3;4] = [2;4]))
let test_filter2 () = ()

val evenb3: i:int{i>0} -> Tot bool
let evenb3 i = (i % 2) = 0

val test_filter3 : unit -> Lemma
      (ensures (b2t (filter evenb3 [1;2;3;4] = [2;4])))
let test_filter3 () = ()
