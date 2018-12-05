module FStar.Calc

open FStar.Preorder (* for `relation` *)

noeq
abstract
type calc_proof #t : list (relation t) -> t -> t -> Type =
  | CalcRefl : #x:t -> calc_proof [] x x
  | CalcStep : rs:(list (relation t)) -> #p:(relation t) ->
               #x:t -> #y:t -> #z:t -> calc_proof rs x y -> squash (p y z) -> calc_proof (p::rs) x z

let rec calc_chain_related (#t : Type) (rs : list (relation t)) (x y : t) : Type0 =
  match rs with
  | [] -> x == y
  | r1::rs -> exists w. calc_chain_related rs x w /\ r1 w y

(* Every chain of `t`'s related by `rs` **(reversed!)** has its endpoints related by p *)
let calc_chain_compatible (#t : Type) (rs : list (relation t)) (p : relation t) : Type0 =
  forall x y. calc_chain_related rs x y ==> p x y

abstract
let rec elim_calc_proof #t rs (#x #y : t) (pf : calc_proof rs x y)
    : Lemma (ensures (calc_chain_related rs x y))
            (decreases pf) =
  match pf with
  | CalcRefl -> ()
  | CalcStep rs #p' #x #y #z pf p'xy -> elim_calc_proof rs pf

abstract
let calc_init (#t:Type) (x:t) : calc_proof [] x x = CalcRefl

abstract
let calc_step (#t:Type) (#rs : list (relation t)) (#x #y : t)
         (p : relation t)                 (* Preorder for this step *)
         (z : t)                          (* Next expression *)
         (pf : unit -> calc_proof rs x y) (* Rest of the proof *)
         (j : unit -> squash (p y z))     (* Justification, thunked to avoid confusion such as #1397 *)
         : Tot (calc_proof (p::rs) x z)
         (* Need to annotate #p seemingly due to #1486 *)
         = CalcStep rs #p (pf ()) (j ())

let calc_finish (#t:Type) (#rs : list (relation t)) (p : relation t) (#x #y :t) (pf : calc_proof rs x y)
  : Lemma (requires (calc_chain_compatible rs p))
          (ensures (p x y))
  = elim_calc_proof rs pf
