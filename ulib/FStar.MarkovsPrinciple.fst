module FStar.MarkovsPrinciple
assume
val markovs_principle: p: (nat -> Tot bool) ->
  Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n))

(* here is a stronger variant of Markov's principle
   (might be as strong as indefinite description?) *)
assume
val stronger_markovs_principle: p: (nat -> GTot bool) ->
  Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n))

