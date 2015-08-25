module FStar.Classical
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* My proposal would be to put this in Classic not in Tot *)
assume val excluded_middle : p:Type -> GTot (b:bool{b = true <==> p})

assume val forall_intro : #a:Type -> #p:(a -> Type) ->
  =f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)

assume val give_proof: #a:Type -> a -> Lemma (ensures a)
