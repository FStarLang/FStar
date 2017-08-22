#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.Syntax.Syntax

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util

type var = bv
type sort = int

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Sort of sort
  | Prod of t * t
  | Match of t * t * t * (t -> t)
  | Fix of (t -> t) * t * int
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t)
  | Accu of atom * list<t>
  | Construct of int * list<t>
  | Unit
  | Bool of bool
type head = t
type annot = t

let app (f:t) (x:t) =
    match f with
    | Lam f -> f x
    | Accu (a, ts) -> Accu(a, x::ts)
    | Construct(i, ts) -> Construct (i, x::ts)
    | Unit
    | Bool _ -> failwith "Ill-typed application"

let mkConstruct i ts = Construct(i,ts)

let mkAccu (v:var) = Accu(Var v, [])

let rec translate (bs:list<t>) (e:term) : t =
    match (SS.compress e).n with
    | Tm_delayed _ -> failwith "Impossible"

    | Tm_constant (FStar.Const.Const_unit) ->
      Unit

    | Tm_constant (FStar.Const.Const_bool b) ->
      Bool b

    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_name x ->
      mkAccu x

    | Tm_abs ([x], body, _) ->
      Lam (fun (y:t) -> translate (y::bs) body)

    | Tm_abs (x::xs, body, _) ->
      let rest = S.mk (Tm_abs(xs, body, None)) None Range.dummyRange in
      let tm = S.mk (Tm_abs([x], rest, None)) None e.pos in
      translate bs tm

    | Tm_app (e, [arg]) ->
      app (translate bs e) (translate bs (fst arg))

    | Tm_app(head, arg::args) ->
      let first = S.mk (Tm_app(head, [arg])) None Range.dummyRange in
      let tm = S.mk (Tm_app(first, args)) None e.pos in
      translate bs tm

    | _ -> failwith "Not yet implemented"

and readback (x:t) : term =
    match x with
    | Unit -> S.unit_const
    | Bool true -> U.exp_true_bool
    | Bool false -> U.exp_false_bool
    | Lam f ->
      let x = S.new_bv None S.tun in
      let body = readback (f (mkAccu x)) in
      U.abs [S.mk_binder x] body None
    | Accu (Var bv, []) ->
      S.bv_to_name bv
    | Accu (Var bv, ts) ->
      let args = List.map (fun x -> as_arg (readback x)) ts in
      U.mk_app (S.bv_to_name bv) args
    | Accu _
    | Construct _ -> failwith "Not yet implemented"

and normalize (e:term) : term = readback (translate [] e)
