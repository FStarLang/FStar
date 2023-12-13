module PulseSyntaxExtension.Err
module R = FStar.Compiler.Range
open FStar.Compiler.Effect
open FStar.Class.HasRange
open FStar.Ident
open FStar.Class.Monad
instance hasRange_ident : hasRange ident = {
    pos = Ident.range_of_id;
    setPos = Ident.set_id_range
}

instance hasRange_lident : hasRange lident = { 
    pos = Ident.range_of_lid;
    setPos = fun x y -> Ident.set_lid_range y x
}
// An error can be "None", which means all relevant
// errors were already logged via the error API.
type error = option (string & R.range)

let err a = nat -> either a error & nat

let bind_err (f:err 'a) (g: 'a -> ML (err 'b)) =
  fun ctr ->
    match f ctr with
    | Inl a, ctr -> g a ctr
    | Inr e, ctr -> Inr e, ctr

let return (x:'a) : err 'a = fun ctr -> Inl x, ctr

instance err_monad : monad err = {
  return = return;
  ( let! ) = bind_err
}

let fail #a (message:string) (range:R.range) : err a =
  fun ctr -> Inr (Some (message, range)), ctr

let fail_if (b:bool) (message:string) (range:R.range) : err unit =
  if b then fail message range else return ()

// Fail without logging another error
let just_fail (#a:Type) () : err a =
  fun ctr -> Inr None, ctr

let next_ctr : err nat = fun ctr -> Inl (ctr + 1), ctr + 1

let map_err_opt (f : 'a -> err 'b) (o:option 'a) : err (option 'b) =
  match o with
  | None -> return None
  | Some v -> let! v' = f v in return (Some v')

let rec map2 (f : 'a -> 'b -> 'c) (xs : list 'a) (ys : list 'b) : err (list 'c) =
  match xs, ys with
  | [], [] ->
    return []
  | x::xx, y::yy ->
    let! r = map2 f xx yy in
    return (f x y :: r)
  | _ ->
    fail "map2: mismatch" FStar.Compiler.Range.dummyRange


let left (f:either 'a 'b) (r:R.range)
  : err 'a
  = match f with
    | Inl x -> return x
    | Inr _ -> fail "Unsupported case" r

let right (f:either 'a 'b) (r:R.range)
  : err 'b
  = match f with
    | Inr x -> return x
    | Inl _ -> fail "Unsupported case" r

