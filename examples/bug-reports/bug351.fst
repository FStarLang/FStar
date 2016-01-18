(*--build-config
  other-files: FStar.Constructive.fst
  --*)
module Bug351

// Failed attempts to reproduce #351
// seem like useful unit tests

val works : a:Type -> b:Type -> x:a -> Pure b (requires (a == b))
                                              (ensures (fun _ -> True))
let works (a:Type) (b:Type) x = x

val works_too : a:Type -> b:Type -> x:a -> f:(b -> Tot unit) ->
  Pure unit (requires (a == b)) (ensures (fun _ -> True))
let works_too (a:Type) (b:Type) x f = f x

val works_too' : a:(Type->Type) -> b:(Type->Type) -> t:Type -> x:a t ->
  f:(b t -> Tot unit) ->
  Pure unit (requires (a == b)) (ensures (fun _ -> True))
let works_too' (a:(Type->Type)) (b:(Type->Type)) (t:Type) (x:a t)
               (f:(b t -> Tot unit)) = f x

type arr (a:Type) = a -> Tot unit

val works_too'' : a:(Type->Type) -> b:(Type->Type) -> t:Type -> x:a t ->
  f:(arr (b t)) ->
  Pure unit (requires (a == b)) (ensures (fun _ -> True))
let works_too'' (a:(Type->Type)) (b:(Type->Type)) (t:Type) (x:a t)
                (f:(b t -> Tot unit)) = f x

open FStar.Constructive

opaque val p_and_not_p : p:Type -> cand p (cnot p) -> Tot cfalse
let p_and_not_p (p:Type) h =
  let Conj h1 h2 = h in h2 h1

val works_too''' : a:(Type->Type) -> b:(Type->Type) -> t:Type -> x:a t ->
  f:(cnot (b t)) ->
  Pure cfalse (requires (a == b)) (ensures (fun _ -> True))
let works_too''' (a:(Type->Type)) (b:(Type->Type)) (t:Type) (x:a t)
                 (f:(cnot (b t))) = f x

opaque val works_too'''' : _P:(Type->Type) ->
                 p:Type ->
                 h:_P p ->
                 a:(Type->Type) ->
                 h12:(cand ctrue (cnot (a p))) ->
                   Pure cfalse (requires (a == _P)) (ensures (fun _ -> True))
let works_too'''' (_P:(Type->Type)) (p:Type) (h:_P p) (a:(Type->Type)) h12 =
  let Conj h1 h2 = h12 in h2 h
