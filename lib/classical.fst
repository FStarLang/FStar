module Classical

(* My proposal would be to put this in Classic not in Tot *)
assume val excluded_middle : p:Type -> Tot (b:bool{b = true <==> p})

assume val forall_intro : #a:Type -> #p:(a -> Type) ->
  =f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
