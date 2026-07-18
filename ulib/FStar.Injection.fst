module FStar.Injection

let inverse_f (#a #b : Type) (i : a @~> b) (y : image_of i) : GTot a =
  FStar.IndefiniteDescription.indefinite_description_ghost a
    (fun (x:a) -> i.f x == y)

let inverse_lem (#a #b : Type) (i : a @~> b) (y : image_of i)
  : Lemma (ensures i.f (inverse_f i y) == y)
          [SMTPat (inverse_f i y)]
  = ()

let __inj_cardinal (n1 n2 : nat)
  (i : fin n1 @~> fin n2)
  : Lemma (ensures n1 <= n2)
  = if n1 > n2 then
      Functions.pigeon n1 n2 i.f

let inj_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 @~> fin n2). True)
          (ensures n1 <= n2)
  = Classical.forall_intro (__inj_cardinal n1 n2)
