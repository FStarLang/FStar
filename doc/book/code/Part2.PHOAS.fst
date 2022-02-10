(* This example is transcribed from Adam Chlipala's
   Parametric Higher-order Abstract Syntax (ICFP 2008) paper.

   http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
*)
module Part2.PHOAS

type typ =
  | Bool
  | Arrow : typ -> typ -> typ

noeq
type term0 (v: typ -> Type) : typ -> Type =
  | Var : #t:typ -> v t -> term0 v t
  | TT  : term0 v Bool
  | FF  : term0 v Bool
  | App : #t1:typ -> #t2:typ ->
          term0 v (Arrow t1 t2) ->
          term0 v t1 ->
          term0 v t2
  | Lam : #t1:typ -> #t2:typ ->
          (v t1 -> term0 v t2) ->
          term0 v (Arrow t1 t2)

let term (t:typ) = v:(typ -> Type) -> term0 v t

let rec denote_typ (t:typ)
  : Type
  = match t with
    | Bool -> bool
    | Arrow t1 t2 -> (denote_typ t1 -> denote_typ t2)

let rec denote_term0 (#t:typ) (e:term0 denote_typ t)
  : Tot (denote_typ t)
        (decreases e)
  = match e with
    | Var x -> x
    | TT -> true
    | FF -> false
    | App f a -> (denote_term0 f) (denote_term0 a)
    | Lam f -> fun x -> denote_term0 (f x)

let denote_term (t:typ) (e:term t)
  : denote_typ t
  = denote_term0 (e _)
