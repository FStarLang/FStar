module OPLSS2021.Vector

////////////////////////////////////////////////////////////////////////////////
// Vectors
////////////////////////////////////////////////////////////////////////////////

type vector (a:Type) : nat -> Type =
  | VNil : vector a 0
  | VCons : hd:a
          -> #n:nat //implicit argument, you don't have to write it in applications or patterns
          -> tl:vector a n
          -> vector a (n + 1)

let head' (v:vector 'a 'n { (match v with VCons _ _ -> true | _ -> false) }) : 'a =
  match v with
  | VCons x xs -> x

//VCons? v is syntactic sugar for saying that v is in the VCons case
let head (v:vector 'a 'n { VCons? v }) : 'a =
  match v with
  | VCons x xs -> x

let rec nth #a (n:nat) (#m:nat{m > n}) (v:vector a m) : a =
  let VCons x xs = v in // F* can prove that since m > n, m > 0, and so v <> VNil
  if n = 0
  then x
  else nth (n-1) xs

let rec append #a #n1 #n2 (v1:vector a n1) (v2:vector a n2)
  : vector a (n1 + n2)
  = match v1 with
    | VNil -> v2
    | VCons hd tl -> VCons hd (append tl v2)

let rec reverse #a #n (v:vector a n)
  : vector a n
  = match v with
    | VNil -> VNil
    | VCons hd tl -> append (reverse tl) (VCons hd VNil)

let rec map #a #b (f:a -> b) #n (v:vector a n)
  : vector b n
  = match v with
    | VNil -> VNil
    | VCons hd tl -> VCons (f hd) (map f tl)

let rec fold_right #a #b (f: a -> b -> b) #n (v:vector a n) (acc: b)
  : b
  = match v with
    | VNil -> acc
    | VCons hd tl -> f hd (fold_right f tl acc)
