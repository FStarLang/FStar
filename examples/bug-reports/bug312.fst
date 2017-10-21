module Bug312

noeq type rel (a:Type) (b:Type) : Type =
  | R : l:a -> r:b -> rel a b

type double (t:Type) = rel t t
type eq (t:Type{hasEq t}) = p:(double t){R?.l p = R?.r p}

val rel_map2 : ('a -> 'b -> Tot 'c) -> (double 'a) -> (double 'b) -> Tot (double 'c)
let rel_map2 f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

type shared (secret:double int) = s:double (int*int)
                                    {fst(R?.l s) = fst(R?.r s)
                                  /\  (fst(R?.l s)) + (snd(R?.l s)) = R?.l secret
                                  /\  (fst(R?.r s)) + (snd(R?.r s)) = R?.r secret}

irreducible type injection (f:int -> Tot int) = (forall (x:int) (y:int). f x = f y ==> x = y)
irreducible type surjection (f:int -> Tot int) = (forall (y:int). (exists (x:int). f x = y))
irreducible type bijection (f:int -> Tot int) = injection f /\ surjection f

type bij = f:(int -> Tot int){bijection f}

unfold type inverses (f:int -> Tot int) (g:int -> Tot int) =
   (forall (y:int). f (g y) = y) /\
   (forall (x:int). g (f x) = x)

irreducible val lemma_inverses_bij: f:(int -> Tot int) -> g:(int -> Tot int) ->
  Lemma (requires (inverses f g))
        (ensures  (bijection f))
let lemma_inverses_bij f g = admit ()

(* sample two random values such that they are related by a bijection f *)
assume val sample : //#a:Type -> #b:Type
                    f:(int -> Tot int){bijection f}
                    -> Tot (r:(rel int int) {R?.r r = f (R?.l r)})


irreducible val triple_a : s:double int
               -> Tot (r:(h:double int & shared h) {(R?.l s) - (snd(R?.l(dsnd r))) =
                                                 (R?.r s) - (snd(R?.r(dsnd r)))})

#reset-options

let triple_a s = let sample_fun = (fun x ->  (x - (R?.l s)) + (R?.r s)) in
                 cut (inverses (fun x -> x) (fun x -> x));
                 lemma_inverses_bij (fun x -> x) (fun x -> x);
                 let as0 = sample (fun x -> x) in

                 let sample_fun'= (fun x ->  (x - (R?.r s)) + (R?.l s)) in
                 cut (inverses sample_fun sample_fun');
                 lemma_inverses_bij sample_fun sample_fun';
                 cut (bijection sample_fun);
                 let as1 = sample sample_fun in

                 let a = rel_map2 (fun x y -> x + y) as0 as1 in
                 (| a, rel_map2 Mktuple2 as0 as1 |)
