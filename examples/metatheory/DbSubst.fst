module DbSubst

(* TAPL Chapter 6 *)

type var = nat

type exp =
  | EVar: var -> exp        (* de Bruijn index *)
  | EAbs: exp -> exp        (* nameless, untyped for now *)
  | EApp: exp -> exp -> exp

val no_zero: exp -> Tot bool
let rec no_zero e =
  match e with
  | EVar k     -> k <> 0
  | EAbs _     -> true
  | EApp e1 e2 -> no_zero e1 && no_zero e2

val shift : c:nat -> d:int -> e:exp -> Pure exp
              (requires (d >= -1 /\ ((d = -1 /\ c = 0) ==> no_zero e)))
              (ensures (fun _ -> True))
              (decreases e)
let rec shift c d e =
  match e with
  | EVar k     -> if k < c then EVar k else EVar (k + d)
  | EAbs e1    -> EAbs (shift (c + 1) d e1)
  | EApp e1 e2 -> EApp (shift c d e1) (shift c d e2)

let sh1 = assert(shift 0 2 (EAbs (EAbs (EApp (EVar 1) (EApp (EVar 0) (EVar 2)))))
                          = EAbs (EAbs (EApp (EVar 1) (EApp (EVar 0) (EVar 4)))))

let sh2 = assert(shift 0 2 (EAbs (EApp (EApp (EVar 0) (EVar 1))
                                       (EAbs (EApp (EApp (EVar 0) (EVar 1))
                                                   (EVar 2)))))
                         = (EAbs (EApp (EApp (EVar 0) (EVar 3))
                                       (EAbs (EApp (EApp (EVar 0) (EVar 1))
                                                   (EVar 4))))))

val subst: j:nat -> e':exp -> e:exp -> Tot exp (decreases e)
let rec subst j e' e = match e with
  | EVar k     -> if j = k then e' else EVar k
  | EAbs e1    -> EAbs (subst (j + 1) (shift 0 1 e') e1)
  | EApp e1 e2 -> EApp (subst j e' e1) (subst j e' e2)

let sub1 = (subst 0 (EVar 1) (EApp (EVar 0) (EAbs (EAbs (EVar 2))))
                           = (EApp (EVar 1) (EAbs (EAbs (EVar 3)))))

let sub2 = (subst 0 (EApp (EVar 1) (EAbs (EVar 2)))
                    (EApp (EVar 0)
                          (EAbs (EVar 1)))
                  = (EApp (EApp (EVar 1) (EAbs (EVar 2)))
                          (EAbs (EApp (EVar 2) (EAbs (EVar 3))))))

let sub3 = (subst 0 (EVar 1) (EAbs (EApp (EVar 0) (EVar 2)))
                           = (EAbs (EApp (EVar 0) (EVar 2))))

let sub4 = (subst 0 (EVar 1) (EAbs (EApp (EVar 1) (EVar 0)))
                           = (EAbs (EApp (EVar 2) (EVar 0))))

val subst_zero_lem: e1:exp -> e2:exp ->
                      Lemma (requires (no_zero e2))
                            (ensures (no_zero (subst 0 e2 e1)))
                        (decreases e1) [SMTPat (subst 0 e2 e1)]
let rec subst_zero_lem e1 e2 =
  match e1 with
  | EApp e1' e2' -> (subst_zero_lem e1' e2; subst_zero_lem e2' e2)
  | _            -> ()

val is_value: exp -> Tot bool
let is_value = is_EAbs

val step: exp -> Tot (option exp)
let rec step = function
  | EApp e1 e2 ->
     if is_value e1 then
       if is_value e2 then
	 (match e1 with
	  | EAbs e1' -> Some (shift 0 (-1) (subst 0 (shift 0 1 e2) e1')))
       else
	 (match step e2 with
	  | None     -> None
	  | Some e2' -> Some (EApp e1 e2'))
     else
       (match step e1 with
	| None     -> None
	| Some e1' -> Some (EApp e1' e2))
  | _ -> None

let st1 = (step (EApp (EAbs (EApp (EApp (EVar 1) (EVar 0)) (EVar 2)))
                      (EAbs (EVar 0)))
                     = Some (EApp (EApp (EVar 0) (EAbs (EVar 0))) (EVar 1)))
