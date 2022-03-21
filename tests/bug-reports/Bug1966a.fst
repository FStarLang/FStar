module Bug1966a

open FStar.Tactics
open FStar.Squash

let conversion a (x y : a) (h:(x == y)) : Tot (equals x y) = Refl

let q_as_lem (#a:Type) (#b:a -> Type) (p:squash (forall x. b x)) (x:a) 
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
let __forall_inst #t (#pred : t -> Type0) (h : (forall x. pred x)) (x : t) : squash (pred x) = ()

assume
val eta (#a:_) (#b:a -> Type) (f: (x:a -> b x)) (_:unit) : Lemma (f == (fun x -> f x))

let fun_ext' #a (#b:a -> Type) (f g: (x:a -> b x)) :
    Lemma (requires (forall x. equals (f x) (g x))) (ensures (equals f g))
  by (
    let p = forall_intro_as "p" in
    let h = implies_intro() in
    let u = forall_intro() in
    let (h1, h2) = destruct_and h in    
    let h2' = instantiate h2 u in
    mapply h2'; clear h2'; clear h2; clear h;
    (* so far it was all boilerplate *)
    mapply (`conversion);
    l_to_r [quote (eta f)];
    l_to_r [quote (eta g)];    
    mapply (`join_squash);
    mapply (`congruence_fun);
    let x = forall_intro_as "X" in
    mapply (`return_squash);
    norm [delta];
    let h1' = instantiate h1 x in (* used to fail for no apparent reason *)
    ()
  ) = ()
