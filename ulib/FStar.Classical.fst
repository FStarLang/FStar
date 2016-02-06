module FStar.Classical
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* one variant of excluded middle is provable by SMT *)
val excluded_middle' : p:Type -> Lemma (requires (True))
                                       (ensures (p \/ ~p))
let excluded_middle' (p:Type) = ()

(* WARNING: this breaks parametricity; TODO: remove*)
assume val excluded_middle : p:Type -> GTot (b:bool{b = true <==> p})

(* TODO: remove *)
assume val forall_intro : #a:Type -> #p:(a -> Type) ->
  =f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)

(* TODO: remove *)
assume val give_proof: #a:Type -> a -> Lemma (ensures a)
