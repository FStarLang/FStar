(* -------------------------------------------------------------------- *)
#light "off"

module Microsoft.FStar.Backends.OCaml.Code

open Microsoft.FStar.Backends.OCaml.Syntax
open FSharp.Format

(* -------------------------------------------------------------------- *)
type assoc  = ILeft | IRight | Left | Right | NonAssoc
type fixity = Prefix | Postfix | Infix of assoc
type opprec = int * fixity
type level  = opprec * assoc

let t_prio_fun  = (10, Infix Right)
let t_prio_tpl  = (20, Infix NonAssoc)
let t_prio_name = (30, Postfix)

let e_bin_prio_lambda = ( 5, Prefix)
let e_bin_prio_if     = (15, Prefix)
let e_bin_prio_letin  = (19, Prefix)
let e_bin_prio_or     = (20, Infix Left)
let e_bin_prio_and    = (25, Infix Left)
let e_bin_prio_eq     = (27, Infix NonAssoc)
let e_bin_prio_order  = (29, Infix NonAssoc)
let e_bin_prio_op1    = (30, Infix Left)
let e_bin_prio_op2    = (40, Infix Left)
let e_bin_prio_op3    = (50, Infix Left)
let e_bin_prio_op4    = (60, Infix Left)
let e_bin_prio_seq    = (100, Infix Left)
let e_app_prio        = (10000, Infix Left)

let min_op_prec = (-1, Infix NonAssoc)
let max_op_prec = (System.Int32.MaxValue, Infix NonAssoc)

(* -------------------------------------------------------------------- *)
let maybe_paren (outer, side) inner doc =
  let noparens ((pi, fi) as _inner) ((po, fo) as _outer) side =
    (pi > po) ||
      match fi, side with
      | Postfix    , Left     -> true
      | Prefix     , Right    -> true
      | Infix Left , Left     -> (pi = po) && (fo = Infix Left )
      | Infix Right, Right    -> (pi = po) && (fo = Infix Right)
      | Infix Left , ILeft    -> (pi = po) && (fo = Infix Left )
      | Infix Right, IRight   -> (pi = po) && (fo = Infix Right)
      | _          , NonAssoc -> (pi = po) && (fi = fo)
      | _          , _        -> false
  in

  if noparens inner outer side then doc else parens doc

(* -------------------------------------------------------------------- *)
let rec doc_of_mltype (outer : level) (ty : mlty) =
    match ty with
    | MLTY_Var x ->
        text (idsym x)

    | MLTY_Tuple tys ->
        let doc = List.map (doc_of_mltype (min_op_prec, NonAssoc)) tys in
        let doc = parens (hbox (combine (parse " *@ ") doc)) in
        doc

    | MLTY_Named (args, name) -> begin
        let args =
            match args with
            | []    -> empty
            | [arg] -> doc_of_mltype (t_prio_name, Left) arg
            | _     ->
                let args = List.map (doc_of_mltype (min_op_prec, NonAssoc)) args in
                parens (hbox (combine (parse ",@ ") args))

        in hbox (reduce1 [args; text (ptsym name)])
    end

    | MLTY_Fun (t1, t2) ->
        let d1 = doc_of_mltype (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype (t_prio_fun, Right) t2 in

        maybe_paren outer t_prio_fun (hbox (reduce1 [d1; parse " ->@ "; d2]))

(* -------------------------------------------------------------------- *)
let doc_of_module (m : module_) =
    empty

(* -------------------------------------------------------------------- *)
let doc_of_sig (s : sig_) =
    empty
