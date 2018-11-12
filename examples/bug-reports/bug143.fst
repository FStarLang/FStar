module Bug143


type empty = | Empty : empty -> empty


val empty_is_empty : empty -> Tot (u:unit{False})
let rec empty_is_empty = function | Empty f -> empty_is_empty f


noeq type lam = | Lam : (lam -> Dv empty) -> lam


val f : lam -> Dv empty
let f l = match l with | Lam f -> f l


val delta : lam
let delta = Lam f


val omega : empty
let omega = f delta


val bug : unit -> Lemma (requires True) (ensures False)
let bug () = empty_is_empty omega
