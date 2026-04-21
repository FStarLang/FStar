module Bug1966a

open FStar.Tactics.V2

let conversion a (x y : a) (h:(x == y)) : Tot (equals x y) = Refl

let q_as_lem (#a:Type) (#b:a -> prop) (p:squash (forall x. b x)) (x:a) 
  : Lemma (b x)
  = ()

let congruence_fun' #a (#b:a -> Type) (f g:(x:a -> b x)) (x:squash (forall x. f x == g x)) :
  Lemma (ensures (fun (x:a) -> f x) == (fun (x:a) -> g x)) = 
  assert ((fun (x:a) -> f x) == (fun (x:a) -> g x))
      by (l_to_r [quote (q_as_lem x)];
          trefl())

let congruence_fun #a (#b:a -> Type) (f g:(x:a -> b x)) :
  Lemma (requires (forall x. f x == g x))
        (ensures (fun (x:a) -> f x) == (fun (x:a) -> g x)) =  congruence_fun' f g ()

private
let __forall_inst #t (#pred : t -> prop) (h : (forall x. pred x)) (x : t) : squash (pred x) = ()

assume
val eta (#a:_) (#b:a -> Type) (f: (x:a -> b x)) (_:unit) : Lemma (f == (fun x -> f x))

let fun_ext' #a (#b:a -> Type) (f g: (x:a -> b x)) :
    Lemma (requires (forall x. f x == g x)) (ensures (f == g))
  = admit ()
