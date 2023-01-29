module AdHocEffectPolymorphism

type eff_tag =
  | G
  | T

let eff (t:eff_tag) (b:Type) =
  match t with
  | T -> unit -> Tot b
  | G -> unit -> GTot b


let tot_as_eff #a #b (f:(x:a -> Tot (b x)))
  : x:a -> eff T (b x)
  = fun x () -> f x

let gtot_as_eff #a #b (f:(x:a -> GTot (b x)))
  : x:a -> eff G (b x)
  = fun x () -> f x


let elim_tot (#t:eff_tag{t=T}) (x:eff t 'a)
  : Tot 'a
  = let y : eff T 'a = x in
    y ()

let elim_gtot (#t:eff_tag{t=G}) (x:eff t 'a)
  : GTot 'a
  = let y : eff G 'a = x in
    y ()

let return #a #t (x:a)
  : eff t a
  = match t with
    | T -> fun () -> x
    | G -> fun () -> x

let (let!) #a #b #t (x:eff t a) (f: a -> eff t b) : eff t b =
  match t with
  | T -> (fun () -> elim_tot (f (elim_tot x)))
  | G -> (fun () -> elim_gtot (f (elim_gtot x)))

let apply #a #t #b (f: (x:a -> eff t (b x))) (x:a)
  : eff t (b x)
  = f x
 
let rec map #a #t #b (f: (a -> eff t b)) (l:list a)
  : eff t (list b)
  = match l with
    | [] -> return []
    | hd::tl ->
      let! x = f hd in
      let! tl = map f tl in
      return (x::tl)

let inc (x:nat) : nat = x + 1
let ginc (x:Ghost.erased nat) : GTot nat = Ghost.reveal x + 1

let test (l:list nat)
  : eff T (list nat)
  = map (tot_as_eff inc) l

let test2 (l:list (Ghost.erased nat))
  : eff G (list nat)
  = map (gtot_as_eff ginc) l
