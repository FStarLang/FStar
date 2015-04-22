module HoareWeakestPrecondition
open Classical

(*We define :
  * types for boolean and arithmetic expressions 'aexp' and 'bexp'
  * a type for formulas 'form'
  * a type for proofs of formulas 'deduce'
  * a type for programs 'com'
  * a type for proofs of reduction of programs 'reval'
  * a type for semantic hoare triples 'hoare'
  * a type for syntactic hoare triples 'hoare_syn'
  * a predicate transformer 'wlp'
We prove :
  * the usual rules for hoare triples are semantically correct -> hoare_{consequence|skip|seq|if|while}
  * {wlp c q} c {q} is a valid semantic hoare triple -> wlp_sound
  * syntactic hoare triples are valid semantic hoare triples -> syn_to_sem
  * wlp is weakest regarding syntactic hoare triples -> wlp_weakest'
*)

type binop =
| Plus
| Minus
| Times

type id = nat

type aexp =
| AInt : int -> aexp
| AVar : id -> aexp 
| AOp  : binop -> aexp -> aexp -> aexp 

type bexp =
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp

type heap = id -> Tot int

val eval_aexp : heap -> aexp -> Tot int
let rec eval_aexp h e =
  match e with 
  | AInt i -> i
  | AVar x -> h x
  | AOp op op1 op2 ->
     let i1 = eval_aexp h op1 in
     let i2 = eval_aexp h op2 in
     (match op with
      | Plus  -> i1 + i2
      | Minus -> i1 - i2
      | Times -> i1 * i2)

val eval_bexp : heap -> bexp -> Tot bool
let rec eval_bexp h be =
  match be with 
  | BTrue -> true
  | BFalse -> false
  | BEq e1 e2 -> eval_aexp h e1  = eval_aexp h e2
  | BLe e1 e2 -> eval_aexp h e1 <= eval_aexp h e2
  | BNot be' -> not (eval_bexp h be')
  | BAnd be1 be2 -> eval_bexp h be1 && eval_bexp h be2

(* Higher-order abstract syntax (HOAS) representation of formulas *)
type form =
| FFalse  : form
| FImpl   : form -> form -> form
| FAnd    : form -> form -> form
| FForall : (heap -> Tot form) -> form
| FEq     : #a:Type -> a -> a -> form

val fnot : form -> Tot form
let fnot f = FImpl f FFalse


val ffor : form -> form -> Tot form
let ffor f1 f2 = FImpl (fnot f1) f2

(* Deduction relation on formulas; using meta-level contexts *)
type deduce : form -> Type =
  | DFalseElim :
             f:form ->
             deduce FFalse ->
             deduce f
  | DImplIntro :
             f1:form ->
             f2:form ->
             (deduce f1 -> Tot (deduce f2)) -> (* <-- meta level implication *)
             deduce (FImpl f1 f2)
  | DImplElim :
	     f1:form ->
             f2:form ->
             deduce (FImpl f1 f2) ->
             deduce f1 ->
             deduce f2
  | DAndIntro :
             f1:form ->
             f2:form ->
             deduce f1 ->
             deduce f2 ->
             deduce (FAnd f1 f2)
  | DAndElim1 :
             f1:form ->
             f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f1
  | DAndElim2 :
             f1:form ->
             f2:form ->
             deduce (FAnd f1 f2) ->
             deduce f2
  | DForallIntro :
             f:(heap->Tot form) ->
             (x:heap -> Tot (deduce (f x))) -> (* <-- meta level quantification *)
             deduce (FForall f)
  | DForallElim :
             f:(heap->Tot form) ->
             deduce (FForall f) ->
             x:heap ->
             deduce (f x)
  | DEqRefl :
              #a:Type ->
              e:a ->
              deduce (FEq e e)
  | DNotEq :
              #a:Type ->
              e1:a ->
              e2:a{e1 <> e2} ->
              deduce (fnot (FEq e1 e2))
  | DEqSubst : (* currently unused *)
              #a:Type ->
              #e1:a ->
              #e2:a ->
              #f:(a -> Tot form) ->
              deduce (FEq e1 e2) ->
              deduce (f e1) ->
              deduce (f e2)
  | DExMid : (* currently unused *)
              f:form ->
              deduce (ffor f (fnot f))

(* Derivable; see bpred below
  | DBexpIntro :
              b:bexp ->
              h:heap{eval_bexp h b = true} ->
              deduce (FBexp b h)
*)
(* Derivable from DEqSubst
  | DEqSymm :
              #a:Type ->
              e1:a ->
              e2:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e1)
  | DEqTran :
              #a:Type ->
              e1:a ->
              e2:a ->
              e3:a ->
              deduce (FEq e1 e2) ->
              deduce (FEq e2 e3) ->
              deduce (FEq e1 e3)
 *)

(* Predicates (aka. assertions) *)
type pred = heap -> Tot form

val pand : pred -> pred -> Tot pred
let pand p1 p2 h = FAnd (p1 h) (p2 h)

val pimpl : pred -> pred -> Tot pred
let pimpl p1 p2 h = FImpl (p1 h) (p2 h)

val pnot : pred -> Tot pred
let pnot p h = fnot (p h)

val pif : pred -> pred -> pred -> Tot pred
let pif pg pt pe = pand (pimpl pg pt) (pimpl (pnot pg) pe)

(* Commands (aka. statements) -- while has loop invariant *)
type com =
| Skip   : com
| Assign : var:id -> term:aexp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:bexp -> then_branch:com -> else_branch:com -> com
| While  : cond:bexp -> body:com -> inv:pred -> com

val update : heap -> id -> int -> Tot heap
let update h x v = fun y -> if y = x then v else h y


(* Evaluation relation *)
type reval : com -> heap -> heap -> Type =
| ESkip      : h0:heap ->
               reval Skip h0 h0

| EAssign    : h0:heap -> x:id -> e:aexp ->
               reval (Assign x e) h0 (update h0 x (eval_aexp h0 e))

| ESeq       : #h0:heap -> #c1:com -> #c2:com -> #h1:heap -> #h2:heap ->
               reval c1 h0 h1 ->
               reval c2 h1 h2 ->
               reval (Seq c1 c2) h0 h2

| EIfTrue    : #h0:heap -> be:bexp{eval_bexp h0 be = true} ->
               ct:com -> ce:com -> #h1:heap ->
               reval ct h0 h1 ->
               reval (If be ct ce) h0 h1

| EIfFalse   : #h0:heap -> be:bexp{eval_bexp h0 be = false} ->
               ct:com -> ce:com -> #h1:heap ->
               reval ce h0 h1 ->
               reval (If be ct ce) h0 h1

| EWhileEnd  : #h0:heap -> be:bexp{eval_bexp h0 be = false} ->
               cb:com -> i:pred ->
               reval (While be cb i) h0 h0

| EWhileLoop : #h0:heap -> be:bexp{eval_bexp h0 be = true} ->
               cb:com -> i:pred -> #h1:heap -> #h2:heap ->
               reval cb h0 h1 ->
               reval (While be cb i) h1 h2 ->
               reval (While be cb i) h0 h2


(* Defining a new eval that is correct with respect to reval
   (needs to be proved in intrinsic (+ constructive) style(s),
   because eval has side-effects) *)

val eval : c:com -> h0:heap -> Dv (|h1:heap * reval c h0 h1|)
let rec eval c h0 =
  match c with
  | Skip ->
     (|h0, ESkip h0|)
  | Assign x e ->
     (|update h0 x (eval_aexp h0 e), EAssign h0 x e|)
  | Seq c1 c2 ->
     let (|h1, p1|) = eval c1 h0 in
     let (|h2, p2|) = eval c2 h1 in
     (|h2, ESeq p1 p2|)
  | If be ct ce ->
     if eval_bexp h0 be then
       let (|h1, p1|) = eval ct h0 in
       (|h1, EIfTrue be ct ce p1|)
     else
       let (|h1, p1|) = eval ce h0 in
       (|h1, EIfFalse be ct ce p1|)
  | While be cb i ->
     if eval_bexp h0 be
     then let (|h1, p1|) = eval cb h0 in
          let (|h2, p2|) = eval c  h1 in
          (|h2, EWhileLoop be cb i p1 p2|)
     else (|h0, EWhileEnd be cb i|)

(* Without whiles we can prove eval total *)
val eval_tot : c:com -> h0:heap -> Tot (|h1:heap * reval c h0 h1|)
let rec eval_tot c h0 =
  match c with
  | Skip ->
     (|h0, ESkip h0|)
  | Assign x e ->
     (|update h0 x (eval_aexp h0 e), EAssign h0 x e|)
  | Seq c1 c2 ->
     let (|h1, p1|) = eval_tot c1 h0 in
     let (|h2, p2|) = eval_tot c2 h1 in
     (|h2, ESeq p1 p2|)
  | If be ct ce ->
     if eval_bexp h0 be then
       let (|h1, p1|) = eval_tot ct h0 in
       (|h1, EIfTrue be ct ce p1|)
     else
       let (|h1, p1|) = eval_tot ce h0 in
       (|h1, EIfFalse be ct ce p1|)
  | While be cb i -> magic()


(* Hoare logic *)

(* Hoare triples -- semantic; constructive style;
                    partial correctness (no termination) *)
type hoare (p:pred) (c:com) (q:pred) : Type =
  (#h:heap -> #h':heap -> reval c h h' -> deduce (p h) -> Tot (deduce (q h')))


val pred_sub : id -> aexp -> pred -> Tot pred
let pred_sub x e p = fun h -> p (update h x (eval_aexp h e))

opaque val hoare_assign : q:pred -> x:id -> e:aexp ->
                          Tot (hoare (pred_sub x e q) (Assign x e) q)
let hoare_assign q x e = fun h h' pr vh -> vh


val pred_impl : pred -> pred -> Tot form
let pred_impl p q = FForall (pimpl p q)

opaque val hoare_consequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
                               hoare p' c q' ->
                               deduce (pred_impl p p') ->
                               deduce (pred_impl q' q) ->
                               Tot (hoare p c q)
let hoare_consequence p p' q q' c hpcq' vpp' vqq' =
    fun h h' pr vph ->
      let vpp'  = DForallElim (pimpl p p') vpp' h in // deduce ((pimpl p p') h)
      let vpph  = DImplElim (p h) (p' h) vpp' vph in
      let vqqh' = hpcq' pr vpph in
      let vqq'  = DForallElim (pimpl q' q) vqq' h' in // deduce ((pimpl q q') h')
      let vqqh' = DImplElim (q' h') (q h') vqq' vqqh' in //deduce (q h')
      vqqh'


opaque val hoare_skip : p:pred -> Tot (hoare p Skip p)
let hoare_skip p = fun h h' pr vph -> vph


opaque val hoare_seq : p:pred -> c1:com -> q:pred -> c2:com -> r:pred ->
                       hpq : hoare p c1 q ->
                       hqr:hoare q c2 r ->
                       Tot (hoare p (Seq c1 c2) r)
let hoare_seq p c1 q c2 r hpq hqr =
    fun h1 h3 pr vph1 ->
        let ESeq r12 r23 = pr in
        let vph2= hpq r12 vph1 in
        hqr r23 vph2


val bpred : bexp -> Tot pred
let bpred be h = FEq bool (eval_bexp h be) true

opaque val hoare_if : p:pred -> q:pred -> be:bexp -> t:com -> e:com ->
                      hoare (pand p (bpred be))  t q ->
                      hoare (pand p (pnot (bpred be))) e q ->
                      Tot (hoare p (If be t e) q)
let hoare_if p q be t e hthen helse =
  fun h h' pr (ph:deduce (p h)) ->
    match pr with
    | EIfTrue be cthen celse rthen ->
       hthen rthen (DAndIntro (p h) (FEq true true) ph (DEqRefl true))
    | EIfFalse be cthen celse relse ->
       helse relse (DAndIntro (p h) (fnot (FEq false true)) ph (DNotEq false true))


(* hoare_while is can only show the annotated invariant *)

opaque val hoare_while_aux : p:pred -> be:bexp -> c:com ->
                             hoare (pand p (bpred be)) c p ->
                             #h:heap -> #h':heap ->
                             pr:reval (While be c p) h h' ->
                             deduce (p h) ->
                             Tot (deduce ((pand p (pnot (bpred be))) h'))
                                 (decreases pr)
let rec hoare_while_aux p be c hbody h h' pr ph =
  match pr with
  | EWhileEnd be' c' p' ->
     DAndIntro (p h) (fnot (FEq false true)) ph (DNotEq false true)
  | EWhileLoop be' c' p' rbody rloop ->
     (let vph1 = hbody rbody (DAndIntro (p h) (FEq true true) ph (DEqRefl true)) in
      let ih = hoare_while_aux p be c hbody in
      ih rloop vph1)

opaque val hoare_while : p:pred -> be:bexp -> c:com ->
                         hoare (pand p (bpred be)) c p ->
                         Tot (hoare p (While be c p) (pand p (pnot (bpred be))))
let hoare_while c p be hbody = hoare_while_aux c p be hbody


(* Weakest Liberal Precondition (aka. predicate transformer semantics) *)

val wlp : com -> pred -> Tot pred
let rec wlp c q =
  match c with
  | Skip -> q
  | Assign x e -> pred_sub x e q
  | Seq c1 c2 -> wlp c1 (wlp c2 q)
  | If be ct ce -> pif (bpred be) (wlp ct q) (wlp ce q)
  | While be c' i ->
     pand i (fun _ -> FForall (pimpl i (pif (bpred be) (wlp c' i) q)))

opaque val proof_if_true_temp : c : pred -> p1 : pred -> p2 : pred -> h : heap ->
                                deduce (FAnd (pif c p1 p2 h) (c h)) ->
                                Tot (deduce (p1 h))
let proof_if_true_temp c p1 p2 h lhs =
    let pc = DAndElim2 (pif c p1 p2 h) (c h) lhs in
    let pcp1 = DAndElim1 ((pimpl c p1) h) ((pimpl (pnot c) p2) h)
                         (DAndElim1 (pif c p1 p2 h) (c h) lhs) in
    DImplElim (c h) (p1 h) pcp1 pc

opaque val proof_if_true : c : pred -> p1 : pred -> p2 : pred -> h : heap ->
                           Tot (deduce (FImpl (pand (pif c p1 p2) c h) (p1 h)))
let proof_if_true c p1 p2 h =
  DImplIntro (FAnd (pif c p1 p2 h) (c h)) (p1 h) (proof_if_true_temp c p1 p2 h)

opaque val proof_if_false_temp : c : pred -> p1 : pred -> p2 : pred -> h : heap ->
                                 deduce (FAnd (pif c p1 p2 h) (fnot (c h))) ->
                                 Tot (deduce (p2 h))
let proof_if_false_temp c p1 p2 h lhs =
    let pcf = DAndElim2 (pif c p1 p2 h) (fnot (c h)) lhs in
    let pcp2 = DAndElim2 ((pimpl c p1) h) ((pimpl (pnot c) p2) h)
                         (DAndElim1 (pif c p1 p2 h) (fnot (c h)) lhs) in
    DImplElim (fnot (c h)) (p2 h) pcp2 pcf

opaque val proof_if_false : c : pred -> p1 : pred -> p2 : pred -> h : heap ->
                     Tot (deduce (FImpl (pand (pif c p1 p2) (pnot c) h) (p2 h)))
let proof_if_false c p1 p2 h =
    DImplIntro (FAnd (pif c p1 p2 h) (pnot c h)) (p2 h)
               (proof_if_false_temp c p1 p2 h)

opaque val plouf : q : pred -> h : heap -> deduce (q h) -> Tot (deduce (q h))
let plouf q h p = p

opaque val while1 : be : bexp -> c : com -> i : pred -> q : pred ->
                    deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                    h : heap ->
                    deduce (pand i (bpred be) h) ->
                    Tot (deduce (wlp c i h))
let while1 be c i q vprop h vand =
    (* i h ==> if .... h *)
    let v1 = DForallElim (pimpl i (pif (bpred be) (wlp c i) q )) vprop h in
    let vih = DAndElim1 (i h) (bpred be h) vand in
    let vbh = DAndElim2 (i h) (bpred be h) vand in
    let v2 = DImplElim (i h) ((pif (bpred be) (wlp c i) q) h) v1 vih in
    let v3 = DAndElim1 (pimpl (bpred be) (wlp c i) h)
                       (pimpl (pnot (bpred be)) q h) v2 in
    DImplElim (bpred be h) (wlp c i h) v3 vbh

opaque val while2 : be : bexp -> c : com -> i : pred -> q : pred ->
                    deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                    h : heap ->
                    Tot (deduce (pimpl (pand i (bpred be)) (wlp c i) h))
let while2 be c i q vprop h =
    DImplIntro (pand i (bpred be) h ) (wlp c i h) (while1 be c i q vprop h)

opaque val while3 : be : bexp -> c : com -> i : pred -> q : pred ->
                   deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                   h : heap ->
                   deduce (wlp (While be c i) q h) ->
                   Tot (deduce (i h))
let while3 be c i q vprop h vwlpcih =
    DAndElim1 (i h) (FForall (pimpl i (pif (bpred be) (wlp c i) q))) vwlpcih

opaque val while4 : be : bexp -> c : com -> i : pred -> q : pred ->
                    deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                    h : heap ->
                    Tot (deduce (pimpl (wlp (While be c i) q) i h))
let while4 be c i q vprop h =
    DImplIntro (wlp (While be c i) q h) (i h) (while3 be c i q vprop h)

opaque val while5 : be : bexp -> c : com -> i : pred -> q : pred ->
                    deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                    h : heap ->
                    deduce (pand i (pnot (bpred be)) h) ->
                    Tot (deduce (q h))
let while5 be c i q vprop h vand =
    (* i h ==> if .... h *)
    let v1 = DForallElim (pimpl i (pif (bpred be) (wlp c i) q )) vprop h in
    let vih = DAndElim1 (i h) (pnot (bpred be) h) vand in
    let vbnh = DAndElim2 (i h) (pnot (bpred be) h) vand in
    let v2 = DImplElim (i h) ((pif (bpred be) (wlp c i) q) h) v1 vih in
    let v3 = DAndElim2 (pimpl (bpred be) (wlp c i) h)
                       (pimpl (pnot (bpred be)) q h) v2 in
    DImplElim (pnot (bpred be) h) (q h) v3 vbnh

opaque val while6 : be : bexp -> c : com -> i : pred -> q : pred ->
                    deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                    h : heap ->
                    Tot (deduce (pimpl (pand i (pnot (bpred be))) q h))
let while6 be c i q vprop h =
    DImplIntro (pand i (pnot (bpred be)) h ) (q h) (while5 be c i q vprop h)


opaque val whilecase : be : bexp -> c : com -> i : pred -> q : pred ->
                       deduce (FForall (pimpl i (pif (bpred be) (wlp c i) q))) ->
                       h : heap ->
                       h' : heap ->
                       hwlpi : hoare (wlp c i) c i ->
                       Tot (hoare (wlp (While be c i) q) (While be c i) q)
let whilecase be c i q vforall h h' hwlpi =
    (*forall. i /\ b ==> wlp c i *)
    let v1 = DForallIntro (pimpl (pand i (bpred be)) (wlp c i))
                          (while2 be c i q vforall) in
    (*forall. i ==> i*)
    let v2 = DForallIntro (pimpl i i)
                          (fun h -> DImplIntro (i h) (i h) (plouf i h)) in
    (*{i /\ b} c i *)
    let  hibci = hoare_consequence (pand i (bpred be))
                                   (wlp c i) i i c hwlpi v1 v2 in
    (*{i} While be c i {i /\ not be}*)
    let hiwhileinbe = hoare_while i be c hibci in
    (*forall. wlp c i ==> i*)
    let v3 = DForallIntro (pimpl (wlp (While be c i) q) i)
                          (while4 be c i q vforall) in
    (*forall. i /\ not be ==> q*)
    let v4 = DForallIntro (pimpl (pand i (pnot (bpred be))) q)
                          (while6 be c i q vforall) in
    hoare_consequence (wlp (While be c i) q) i q (pand i (pnot (bpred be)))
                      (While be c i) hiwhileinbe v3 v4

opaque val wlp_sound : c:com -> q:pred -> Tot (hoare (wlp c q) c q)
let rec wlp_sound c q =
  match c with
  | Skip -> hoare_skip q
  | Assign x e -> hoare_assign q x e
  | Seq c1 c2 ->
      let wlp_c1 = wlp_sound c1 (wlp c2 q) in
      let wlp_c2 = wlp_sound c2 q in
      hoare_seq (wlp c1 (wlp c2 q)) c1 (wlp c2 q) c2 q wlp_c1 wlp_c2
  | If be ct ce ->
      let wlp_t = wlp_sound ct q in
      let wlp_e = wlp_sound ce q in
      let vpp' = DForallIntro (pimpl (pand (pif (bpred be) (wlp ct q) (wlp ce q))
                                           (bpred be)) (wlp ct q))
                              (proof_if_true (bpred be) (wlp ct q) (wlp ce q)) in
      let p = pimpl (pand (pif (bpred be) (wlp ct q) (wlp ce q)) (bpred be))
                    (wlp ct q) in
      let p' = wlp ct q in
      let hthen = hoare_consequence
                    (pand (pif (bpred be) (wlp ct q) (wlp ce q)) (bpred be))
                    (wlp ct q) q q ct wlp_t vpp'
                    (DForallIntro (pimpl q q)
                       (fun (h:heap) -> (DImplIntro (q h) (q h) (plouf q h)))) in
      let vpp'' = DForallIntro (pimpl (pand (pif (bpred be) (wlp ct q) (wlp ce q))
                                            (pnot (bpred be)))
                                      (wlp ce q))
                             (proof_if_false (bpred be) (wlp ct q) (wlp ce q)) in
      let helse = hoare_consequence
                    (pand (pif (bpred be) (wlp ct q) (wlp ce q)) (pnot (bpred be)))
                    (wlp ce q) q q ce wlp_e vpp''
                    (DForallIntro (pimpl q q)
                      (fun (h:heap) -> (DImplIntro (q h) (q h) (plouf q h)))) in
      hoare_if (wlp c q) q be ct ce hthen helse
  | While be body i ->
     (* Here we have to get the proof of the forall inside the
        argument, that is why we have to write this with lambda *)

      fun h h' pr vph ->
          let vforall = DAndElim2 (i h)
               (FForall (pimpl i (pif (bpred be) (wlp body i) q))) vph in
          whilecase be body i q vforall h h' (wlp_sound body i) pr vph
          (* Proof of i /\ be ==> wlp c i *)

(* Some informal proofs:

Case: c = if be then st else se
-------------------------------

to show:
{ if be then wlp ct q else wlp ce q } if be then ct else ce { q }

by hoare_if, still to show:
1. {     be /\ if be then wlp ct q else wlp ce q } ct { q }
2. { not be /\ if be then wlp ct q else wlp ce q } ce { q }

by consequence (with logical equivalence in pre), still to show:
1. { wlp ct q } ct { q }
2. { wlp ce q } ce { q }

both of these are immediate from the induction hypothesis


Case: c = while be do c' inv i  (TODO)
------------------------------
*)

(* Weakest precondition property; first semantically (failed attempt),
                                  then syntactically *)

opaque val skip : p : pred ->  q : pred -> hpcq : hoare p Skip q -> h : heap ->
                  deduce (p h) ->
                  Tot (deduce (q h))
let skip p q hpcq h ph = hpcq (ESkip h) ph

opaque val assign1 : x : nat -> e : aexp -> p:pred -> q:pred ->
                     hpcq:hoare p (Assign x e) q ->
                     h:heap ->
                     vph:deduce (p h) ->
                     Tot (deduce (wlp (Assign x e) q h))
let assign1  x e p q hpcq h vph =
    let h' = update h x (eval_aexp h e) in
    let pr = EAssign h x e in
    let vqh' = hpcq pr vph in
    vqh'

opaque val assign2 : x : nat -> e : aexp -> p:pred -> q:pred ->
                     hpcq:hoare p (Assign x e) q ->
                     h:heap ->
                     Tot (deduce (FImpl (p h) (wlp (Assign x e) q h)))
let assign2 x e p q hpcq h =
    DImplIntro (p h) (wlp (Assign x e) q h) (assign1 x e p q hpcq h)
(*Idea of proof for the seq case, which does not typecheck*)
(*
type heap_equal (h1:heap) (h2:heap) = (h1=h2)
val seq1 : c1:com -> c2:com -> p : pred -> q:pred ->
           hpc1c2q :hoare p (Seq c1 c2) q ->
           h0 : heap -> vph0 : deduce (p h0) -> h1 : heap ->
           pr1 : reval c1 h0 h1 -> Tot(hoare (fun x -> FEq h1 x) c2 q)
let seq1 c1 c2 p q hpc1c2q h0 vph0 h1 pr1 =
    fun h1' h2 pr2 veq ->
        if excluded_middle (heap_equal h1 h1') then
            hpc1c2q (ESeq pr1 pr2) vph0
        else
            let vfalse = DImplElim (FEq h1 h1') FFalse (DNotEq h1 h1') veq in
            DFalseElim (q h2) vfalse
*)
opaque val iftrue : be:bexp -> ct:com -> ce:com -> p : pred -> q:pred ->
                    hpifq:hoare p (If be ct ce) q ->
                    Tot (hoare (pand p (bpred be)) ct q)
let iftrue be ct ce p q hpifq =
    fun h h' pr vpbeh ->
        if eval_bexp h be then
            hpifq (EIfTrue be ct ce pr) (DAndElim1 (p h) (bpred be h) vpbeh)
        else
            let vbe = DAndElim2 (p h) (bpred be h) vpbeh in
            let vnbe = DNotEq false true in
            let vfalse = DImplElim (bpred be h) FFalse vnbe vbe in
            DFalseElim (q h') vfalse

opaque val iffalse : be:bexp -> ct:com -> ce:com -> p : pred -> q:pred ->
                     hpifq:hoare p (If be ct ce) q ->
                     Tot (hoare (pand p (pnot (bpred be))) ce q)
let iffalse be ct ce p q hpifq =
    fun h h' pr vpnbeh ->
        if eval_bexp h be = false then
            hpifq (EIfFalse be ct ce pr) (DAndElim1 (p h) (pnot (bpred be) h) vpnbeh)
        else
            let vnbe = DAndElim2 (p h) (pnot (bpred be) h) vpnbeh in
            let vbe = DEqRefl true in
            let vfalse = DImplElim (bpred be h) FFalse vnbe vbe in
            DFalseElim (q h') vfalse

opaque val if5 : be :bexp -> ct : com -> ce:com -> p : pred -> q : pred ->
     vimpltrue:deduce (FForall (pimpl (pand p (bpred be)) (wlp ct q))) ->
     vimplfalse:deduce (FForall (pimpl (pand p (pnot (bpred be))) (wlp ce q))) ->
     h:heap ->
     vph:deduce (p h) ->
     vnbe:deduce (pnot (bpred be) h) ->
     Tot(deduce (wlp ce q h))
let if5 be ct ce p q vimpltrue vimplfalse h vph vnbe =
    let vimplfalseh = DForallElim (pimpl (pand p (pnot (bpred be))) (wlp ce q))
                                  vimplfalse h in
    let vand = DAndIntro (p h) (pnot (bpred be) h) vph vnbe in
    DImplElim (pand p (pnot (bpred be)) h) (wlp ce q h) vimplfalseh vand

opaque val if4 : be :bexp -> ct : com -> ce:com -> p : pred -> q : pred ->
     vimpltrue:deduce (FForall (pimpl (pand p (bpred be)) (wlp ct q))) ->
     vimplfalse:deduce (FForall (pimpl (pand p (pnot (bpred be))) (wlp ce q))) ->
     h:heap ->
     vph:deduce (p h) ->
     vbe:deduce (bpred be h) ->
     Tot (deduce ((wlp ct q) h))
let if4 be ct ce p q vimpltrue vimplfalse h vph vbe =
    let vimpltrueh = DForallElim (pimpl (pand p (bpred be)) (wlp ct q))
                                 vimpltrue h in
    let vand = DAndIntro (p h) (bpred be h) vph vbe in
    DImplElim (pand p (bpred be) h) (wlp ct q h) vimpltrueh vand

opaque val if3 : be :bexp -> ct : com -> ce:com -> p : pred -> q : pred ->
    vimpltrue : deduce (FForall (pimpl (pand p (bpred be)) (wlp ct q))) ->
    vimplfalse : deduce (FForall (pimpl (pand p (pnot (bpred be))) (wlp ce q))) ->
    h : heap ->
    vph : deduce (p h) ->
    Tot (deduce ((pif (bpred be) (wlp ct q) (wlp ce q)) h))
let if3 be ct ce p q vimpltrue vimplfalse h vph =
  DAndIntro (pimpl (bpred be) (wlp ct q) h)
            (pimpl (pnot (bpred be)) (wlp ce q) h)
            (DImplIntro (bpred be h) (wlp ct q h)
                        (if4 be ct ce p q vimpltrue vimplfalse h vph))
            (DImplIntro (pnot (bpred be) h) (wlp ce q h)
                        (if5 be ct ce p q vimpltrue vimplfalse h vph))

opaque val if2 : be :bexp -> ct : com -> ce:com -> p : pred -> q : pred ->
    vimpltrue : deduce (FForall (pimpl (pand p (bpred be)) (wlp ct q))) ->
    vimplfalse : deduce (FForall (pimpl (pand p (pnot (bpred be))) (wlp ce q))) ->
    h : heap ->
    Tot(deduce ((pimpl p (pif (bpred be) (wlp ct q) (wlp ce q))) h))
let if2 be ct ce p q vimpltrue vimplfalse h =
    DImplIntro (p h) (pif (bpred be) (wlp ct q) (wlp ce q) h)
               (if3 be ct ce p q vimpltrue vimplfalse h)

opaque val if1 : be :bexp -> ct : com -> ce:com -> p : pred -> q : pred ->
    vimpltrue : deduce (FForall (pimpl (pand p (bpred be)) (wlp ct q))) ->
    vimplfalse : deduce (FForall (pimpl (pand p (pnot (bpred be))) (wlp ce q))) ->
    Tot (deduce (FForall (pimpl p (pif (bpred be) (wlp ct q) (wlp ce q)))))
let if1 be ct ce p q vimpltrue vimplfalse =
    DForallIntro (pimpl p (pif (bpred be) (wlp ct q) (wlp ce q)))
                 (if2 be ct ce p q vimpltrue vimplfalse)

(*wlp_weakest proof (if the While case is removed) *)                 
(*
opaque val wlp_weakest : c:com -> p:pred -> q:pred ->
                         hpcq:hoare p c q ->
                         Tot (deduce (pred_impl p (wlp c q))) (decreases c)
let rec wlp_weakest c p q hpcq =
    match c with
      | Skip ->
          DForallIntro (pimpl p (wlp Skip q))
            (fun h -> DImplIntro (p h) (wlp Skip q h) (skip p q hpcq h))
      | Assign x e ->
          DForallIntro (pimpl p (wlp (Assign x e) q)) (assign2 x e p q hpcq)
      (* The rule for Seq should be true. But my idea to
         prove it can not be written in FStar *)
      | Seq c1 c2 -> magic ()
      | If be ct ce ->
          let hoaretrue = iftrue be ct ce p q hpcq in
          let vimpltrue = wlp_weakest ct (pand p (bpred be)) q hoaretrue in
          let hoarefalse = iffalse be ct ce p q hpcq in
          let vimplfalse = wlp_weakest ce (pand p (pnot (bpred be)))
                                       q hoarefalse in
          if1 be ct ce p q vimpltrue vimplfalse
      (* It is anyway false for While *)
      | While be body i -> magic ()
*)

(*The fact that the weakest property is false for the semantic hoare triples
 * makes it necessary to use syntactic hoare triples instead of semantic ones*)

(* Syntactic Hoare triples (needed for wlp_weakest) *)

type hoare_syn : pred -> com -> pred -> Type =
  | HoareSynAssign : q:pred -> x:id -> e:aexp ->
                     Tot (hoare_syn (pred_sub x e q) (Assign x e) q)
  | HoareSynConsequence : p:pred -> p':pred -> q:pred -> q':pred -> c:com ->
                          hoare_syn p' c q' ->
                          deduce (pred_impl p p') ->
                          deduce (pred_impl q' q) ->
                          Tot (hoare_syn p c q)
  | HoareSynSkip : p:pred ->
                   Tot (hoare_syn p Skip p)
  | HoareSynSeq : p:pred -> c1:com -> q:pred -> c2:com -> r:pred ->
                  hoare_syn p c1 q ->
                  hoare_syn q c2 r ->
                  Tot (hoare_syn p (Seq c1 c2) r)
  | HoareSynIf : p:pred -> q:pred -> be:bexp -> t:com -> e:com ->
                 hoare_syn (pand p (bpred be)) t q ->
                 hoare_syn (pand p (pnot (bpred be))) e q ->
                 Tot (hoare_syn p (If be t e) q)
  | HoareSynWhile : p:pred -> be:bexp -> c:com ->
                    hoare_syn (pand p (bpred be)) c p ->
                    Tot (hoare_syn p (While be c p) (pand p (pnot (bpred be))))
(*Syntactic triples are semantic triples*)
val syn_to_sem : #p:pred -> #c:com -> #q:pred -> hsyn : hoare_syn p c q -> Tot (hoare p c q)
let rec syn_to_sem p c q hsyn = match hsyn with
| HoareSynAssign q x e -> hoare_assign q x e
| HoareSynConsequence p p' q q' c hsyn' vpp' vqq' -> hoare_consequence p p' q q' c (syn_to_sem hsyn') vpp' vqq'
| HoareSynSkip p -> hoare_skip p
| HoareSynSeq p c1 q c2 r hsyn1 hsyn2 -> hoare_seq p c1 q c2 r (syn_to_sem hsyn1) (syn_to_sem hsyn2)
| HoareSynIf p q be t e hthen helse -> hoare_if p q be t e (syn_to_sem hthen) (syn_to_sem helse)
| HoareSynWhile p be c hloop -> hoare_while p be c (syn_to_sem hloop) 

val impl_comp_aux : p1 : pred -> p2 : pred -> p3 : pred ->
                    vp12 : deduce(pred_impl p1 p2) ->
                    vp23 : deduce(pred_impl p2 p3) ->
                    h : heap -> 
		    vp1h : deduce (p1 h) ->
                    Tot(deduce (p3 h))
let impl_comp_aux p1 p2 p3 vp12 vp23 h vp1h =
let vp12h = DForallElim (pimpl p1 p2) vp12 h in
let vp23h = DForallElim (pimpl p2 p3) vp23 h in
let vp2h = DImplElim (p1 h) (p2 h) vp12h vp1h in
DImplElim (p2 h) (p3 h) vp23h vp2h

(* (p1 => p2) -> (p2 => p3) -> (p1 => p3)*)
val impl_comp : p1 : pred -> p2 : pred -> p3 : pred ->
                       deduce (pred_impl p1 p2) ->
                       deduce (pred_impl p2 p3) ->
                       Tot (deduce (pred_impl p1 p3))

let impl_comp p1 p2 p3 vp12 vp23 =
DForallIntro (pimpl p1 p3) (fun (h:heap) -> DImplIntro (p1 h) (p3 h) (impl_comp_aux p1 p2 p3 vp12 vp23 h))
(* (q'=>q) -> (wlp c q' => wlp c q) *)
val impl_comp_form : f1 : form -> f2 : form -> f3 : form ->
                     deduce (FImpl f1 f2) -> deduce (FImpl f2 f3) ->
		     Tot(deduce (FImpl f1 f3))
let impl_comp_form f1 f2 f3 vimpl12 vimpl23 =
DImplIntro f1 f3 (fun vf1 -> let vf2 = DImplElim f1 f2 vimpl12 vf1 in
    DImplElim f2 f3 vimpl23 vf2)

val impl_if : be : bexp -> ct : com -> ce : com ->
              q : pred -> q' : pred -> h : heap -> 
	      deduce (pred_impl (wlp ct q) (wlp ct q')) ->
	      deduce (pred_impl (wlp ce q) (wlp ce q')) ->
	      deduce (pred_impl q q') ->
	      deduce (wlp (If be ct ce) q h) ->
	      Tot(deduce(wlp (If be ct ce) q' h))
let impl_if be ct ce q q' h vimplwlp1 vimplwlp2 vqq' vwlpqh =
  let vimplwlp1h = DForallElim (pimpl (wlp ct q) (wlp ct q')) vimplwlp1 h in
  let vimplwlp2h = DForallElim (pimpl (wlp ce q) (wlp ce q')) vimplwlp2 h in
  let lhs = impl_comp_form (bpred be h) (wlp ct q h) (wlp ct q' h) (DAndElim1 (pimpl (bpred be) (wlp ct q) h) (pimpl (pnot (bpred be)) (wlp ce q) h) vwlpqh) vimplwlp1h in
  let rhs = impl_comp_form (pnot (bpred be) h) (wlp ce q h) (wlp ce q' h) (DAndElim2 (pimpl (bpred be) (wlp ct q) h) (pimpl (pnot (bpred be)) (wlp ce q) h) vwlpqh) vimplwlp2h in
  DAndIntro (pimpl (bpred be) (wlp ct q') h) (pimpl (pnot (bpred be)) (wlp ce q') h) lhs rhs

val impl_while2 : be : bexp -> body : com -> p : pred -> q : pred -> q' : pred -> vqq' : deduce (pred_impl q q') -> vpropq : deduce (pred_impl p (pif (bpred be) (wlp body p) q)) -> h : heap -> vph : deduce (p h) -> Tot(deduce (pif (bpred be) (wlp body p) q' h))
let impl_while2 be body p q q' vqq' vpropq h vph = 
let vpropqh = DForallElim (pimpl p (pif (bpred be) (wlp body p) q)) vpropq h in
let vifqh = DImplElim (p h) (pif (bpred be) (wlp body p) q h) vpropqh vph in
let lhs = DAndElim1 (pimpl (bpred be) (wlp body p) h) (pimpl (pnot (bpred be)) q h) vifqh in
let vimplq = DAndElim2 (pimpl (bpred be) (wlp body p) h) (pimpl (pnot (bpred be)) q h) vifqh in
let rhs = impl_comp_form (pnot (bpred be) h) (q h) (q' h) vimplq (DForallElim (pimpl q q') vqq' h) in
DAndIntro (pimpl (bpred be) (wlp body p) h) (pimpl (pnot (bpred be)) q' h) lhs rhs

val impl_while1 : be : bexp -> body : com -> p : pred -> q : pred -> q' : pred -> vqq' : deduce (pred_impl q q') -> h : heap -> vwlpqh : deduce (wlp (While be body p) q h ) -> Tot(deduce (wlp (While be body p) q' h))
let impl_while1 be body p q q' vqq' h vwlpqh = 
let vph = DAndElim1 (p h) (pred_impl p (pif (bpred be) (wlp body p) q)) vwlpqh in
let vpropq = DAndElim2 (p h) (pred_impl p (pif (bpred be) (wlp body p) q)) vwlpqh in
let vpropq' = DForallIntro (pimpl p (pif (bpred be) (wlp body p) q')) (fun h -> DImplIntro (p h) (pif (bpred be) (wlp body p) q' h) (impl_while2 be body p q q' vqq' vpropq h)) in
DAndIntro (p h) (pred_impl p (pif (bpred be) (wlp body p) q')) vph vpropq'

 
val impl_wlp : c:com -> q:pred -> q':pred ->
                      deduce (pred_impl q q') ->
                      Tot (deduce (pred_impl (wlp c q) (wlp c q')))
let rec impl_wlp c q q' vqq' =
match c with 
| Skip -> vqq'
| Assign x e -> DForallIntro (pimpl (wlp c q) (wlp c q')) (fun h -> DForallElim (pimpl q q') vqq' (update h x (eval_aexp h e)))
| Seq c1 c2 -> let vimplwlpc2 = impl_wlp c2 q q' vqq' in
               impl_wlp c1 (wlp c2 q) (wlp c2 q') vimplwlpc2
| If be ct ce -> let vimplwlp1 = impl_wlp ct q q' vqq' in
                 let vimplwlp2 = impl_wlp ce q q' vqq' in
		 DForallIntro (pimpl (wlp c q) (wlp c q')) (fun h -> DImplIntro (wlp c q h) (wlp c q' h) (impl_if be ct ce q q' h vimplwlp1 vimplwlp2 vqq'))
| While be body p -> DForallIntro (pimpl (wlp c q) (wlp c q')) (fun h -> DImplIntro (wlp c q h) (wlp c q' h) (impl_while1 be body p q q' vqq' h))
(*p,be |- wlp body p*)
opaque val while1' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap -> deduce (p h) -> deduce (bpred be h) ->
                     Tot (deduce (wlp body p h))
let while1' be body p vpbewlp h vph vbe =
  let vpbewlph = DForallElim (pimpl (pand p (bpred be)) (wlp body p)) vpbewlp h in
  let vand = DAndIntro (p h) (bpred be h) vph vbe in
  DImplElim (pand p (bpred be) h) (wlp body p h) vpbewlph vand

opaque val while2' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap -> deduce (p h) ->
                     Tot (deduce (FImpl (bpred be h) (wlp body p h)))
let while2' be body p vpbewlp h vph =
  DImplIntro (bpred be h) (wlp body p h) (while1' be body p vpbewlp h vph)

opaque val while3' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap -> deduce (p h) -> deduce (pnot (bpred be) h) ->
                     Tot (deduce (FAnd (p h) (pnot (bpred be) h) ))
let while3' be body p vpbewlp h vph vnbe =
  DAndIntro (p h) (pnot (bpred be) h) vph vnbe

opaque val while4' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap -> deduce (p h) ->
                     Tot (deduce (FImpl (pnot (bpred be) h)
                                        (pand p (pnot (bpred be)) h)))
let while4' be body p vpbewlp h vph =
  DImplIntro (pnot (bpred be) h) (pand p (pnot (bpred be)) h)
             (while3' be body p vpbewlp h vph)

(*
val while5' : be : bexp -> body : com -> p : pred ->
              deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
              h : heap -> deduce (p h) ->
              Tot (deduce (FAnd (pimpl (bpred be) (wlp body p) h)
                                (pimpl (pnot (bpred be))
                                       (pand p (pnot (bpred be))) h)))
let while5' be body p vpbewlp h vph vbe iaun =
  DAndIntro (pimpl (bpred be) (wlp body p) h)
            (pimpl (pnot (bpred be)) (pand p (pnot (bpred be))) h)
            (while2' be body p vpbewlp h vph) (while4' be body p vpbewlp h vph)
*)

opaque val while6' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap ->
  Tot (deduce (FImpl (p h) (FAnd (pimpl (bpred be) (wlp body p) h)
                                 (pimpl (pnot (bpred be))
                                        (pand p (pnot (bpred be))) h))))
let while6' be body p vpbewlp h =
  DImplIntro (p h) (FAnd (pimpl (bpred be) (wlp body p) h)
                         (pimpl (pnot (bpred be)) (pand p (pnot (bpred be))) h))
             (fun vph -> DAndIntro (pimpl (bpred be) (wlp body p) h)
                                   (pimpl (pnot (bpred be))
                                          (pand p (pnot (bpred be))) h)
                                   (while2' be body p vpbewlp h vph)
                                   (while4' be body p vpbewlp h vph))

opaque val while7' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap -> deduce (p h) ->
                     Tot (deduce (FAnd (p h) (pred_impl (p)
                                          (pand (pimpl (bpred be) (wlp body p))
                                          (pimpl (pnot (bpred be))
                                                 (pand p (pnot (bpred be))))))))
let while7' be body p vpbewlp h vph =
  DAndIntro (p h) (pred_impl (p) (pand (pimpl (bpred be) (wlp body p) )
                                       (pimpl (pnot (bpred be))
                                              (pand p (pnot (bpred be))) )))
            vph (DForallIntro (pimpl p (pand (pimpl (bpred be) (wlp body p) )
                                             (pimpl (pnot (bpred be))
                                                    (pand p (pnot (bpred be))) )))
                              (while6' be body p vpbewlp))

opaque val while8' : be : bexp -> body : com -> p : pred ->
                     deduce (pred_impl (pand p (bpred be)) (wlp body p)) ->
                     h : heap ->
                     Tot (deduce (FImpl (p h) (FAnd (p h) (pred_impl (p)
                                  (pand (pimpl (bpred be) (wlp body p) )
                                        (pimpl (pnot (bpred be))
                                               (pand p (pnot (bpred be))) ))))))
let while8' be body p vpbewlp h =
  let aux _ = pred_impl p (pand (pimpl (bpred be) (wlp body p) )
                                (pimpl (pnot (bpred be))
                                       (pand p (pnot (bpred be))) )) in
  DImplIntro (p h) (pand p aux h) (while7' be body p vpbewlp h)
(*Now we can prove that our wlp is actually weakest in the syntactic sense*)
opaque val wlp_weakest' : c:com -> p:pred -> q:pred ->
                         hpcq:hoare_syn p c q ->
                         Tot (deduce (pred_impl p (wlp c q))) (decreases hpcq)
let rec wlp_weakest' c p q hpcq =
  match hpcq with
  | HoareSynAssign q' x e ->
     DForallIntro (pimpl p p) (fun h -> DImplIntro (p h) (p h) (plouf p h))
  | HoareSynConsequence p' p'' q' q'' c' hc vpp' vq'q ->
     let impl3 = impl_wlp c' q'' q' vq'q in
     let impl2 = wlp_weakest' c p'' q'' hc in
     let vpwlp' = impl_comp p' p'' (wlp c q'') vpp' impl2 in
     impl_comp p' (wlp c q'') (wlp c q') vpwlp' impl3
  | HoareSynSkip p' ->
     DForallIntro (pimpl p' p') (fun h -> DImplIntro (p' h) (p' h) (plouf p' h))
  | HoareSynSeq p' c1 q' c2  r' hc1 hc2 ->
     let implqwlpc2 = wlp_weakest' c2 q' r' hc2 in
     let implwlpc1 = impl_wlp c1 q' (wlp c2 r') implqwlpc2 in
     let implpwlp = wlp_weakest' c1 p' q' hc1 in
     impl_comp p' (wlp c1 q') (wlp c1 (wlp c2 r')) implpwlp implwlpc1
  | HoareSynIf p' q' be ct ce hct hce ->
     let vimpltrue = wlp_weakest' ct (pand p' (bpred be)) q' hct in
     let vimplfalse = wlp_weakest' ce (pand p' (pnot (bpred be))) q' hce in
     if1 be ct ce p' q' vimpltrue vimplfalse
  | HoareSynWhile p be body hbody ->
     let vimplbody = wlp_weakest' body (pand p (bpred be)) p hbody in
     let prop = DForallIntro (pimpl p (pand (pimpl (bpred be) (wlp body p))
                                            (pimpl (pnot (bpred be))
                                                   (pand p (pnot (bpred be))))))
                             (while6' be body p vimplbody) in
     DForallIntro (pimpl p (wlp c q)) (while8' be body p vimplbody)

(* Seq case now trivial

  {p} c1; c2 {q}  ==> {p} c1 {p'} and {p'} c2 {q}

  IH1: p => wlp c1 p'
  IH2: p' => wlp c2 q  =monotonicity=>  wlp c1 p' => wlp c1 (wlp c2 q)

  TS: p => wlp (c1; c2) q
  TS: p => wlp c1 (wlp c2 q)

 *)


