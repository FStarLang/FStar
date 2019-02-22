module Bug1595

let relation (a:Type) = a -> a -> Type0

(* let preorder (a:Type) = relation a *)
let preorder (a:Type) = rel:relation a{True}

noeq
type calc_proof #t : list (relation t) -> t -> t -> Type =
  | CalcRefl : #x:t -> calc_proof [] x x
  | CalcStep : rs:(list (relation t)) -> #p:(relation t) ->
               #x:t -> #y:t -> #z:t -> calc_proof rs x y -> squash (p y z) -> calc_proof (p::rs) x z

let init (#t:Type) (x:t) : calc_proof [] x x = CalcRefl

let step (#t:Type) (#rs : list (relation t)) (#x #y : t)
         (p : relation t)                 (* Preorder for this step *)
         (z : t)                          (* Next expression *)
         (pf : unit -> calc_proof rs x y) (* Rest of the proof *)
         (j : unit -> squash (p y z))     (* Justification, thunked to avoid confusion such as #1397 *)
         : Tot (calc_proof (p::rs) x z)
         (* Need to annotate #p seemingly due to #1486 *)
         = CalcStep rs #p (pf ()) (j ())

let r1 : preorder int = fun x y -> (>=) x y <: Type
let r2 : preorder int = fun x y -> (<=) x y <: Type

[@(expect_failure [19])]
let test_gt_lt_desugared () : Lemma False =
  let p : calc_proof #int [r2; r1] 10 11 = (
    step #int #[r1] #10 #9 r2 11 (fun () ->
    step #int #[] #10 #10 r1 9 (fun () ->
    init #int 10) (fun () -> ())) (fun () -> ()))
  in
  assert False
