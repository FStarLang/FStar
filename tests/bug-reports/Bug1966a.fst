module Bug1966a

open FStar.Tactics
open FStar.Squash

let conversion a (x y : a) (h:(x == y)) : Tot (equals x y) = Refl

let congruence_fun #a (#b:a -> Type) (f g:(x:a -> b x)) :
  Lemma (requires (forall x. f x == g x))
        (ensures (fun (x:a) -> f x) == (fun (x:a) -> g x)) = admit()

private
let __forall_inst #t (#pred : t -> Type0) (h : (forall x. pred x)) (x : t) : squash (pred x) = ()

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
    grewrite (quote f) (quote (fun (x:a) -> f x)); (* eta *)
    grewrite (quote g) (quote (fun (x:a) -> g x)); (* eta *)
    mapply (`join_squash);
    mapply (`congruence_fun);
    let x = forall_intro_as "X" in
    mapply (`return_squash);
    norm [delta];
    let h1' = instantiate h1 x in (* fails for no apparent reason *)
    ()
  ) = ()
