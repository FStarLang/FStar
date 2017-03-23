module PEMFstar


type universe_level = nat

type var = nat
type universes = list universe_level

type term =
 | Var : var -> universes -> term
 | Const : const -> universes -> term
 | Type_ : universe_level -> term
 | App : term -> term -> term
 | Lam : term -> term -> term
 | Prod : term -> comp -> term
 | Refine : term -> term -> term

and comp =
  | Tot_ : term -> comp
  | Pure_ : term -> term -> comp

and const =
  (* Natural numbers *)
  | Nat : const
  | Zero : const
  | Succ : const
  | NatElim : const

  (* Equality *)
  | Eq : const
  | Refl : const
  | EqElim : const


let cnat = Const Nat
let czero = Const Zero
let csucc = Const Succ
let cnat_elim = Const NatElim
let ceq = Const Eq
let crefl = Const Refl
let ceq_elim = Const EqElim
let arr t1 t2 = Prod t1 (Tot_ t2)
let app e1 e2 = App e1 e2
let type_0 = Type_ 0
let succ n = app csucc n
let refl e = app refl e
let eq t e1 e2 = eq `app` t `app` e1 `app` e2



(* Derived term (one hole term contexts) *)
type dterm =
  | Hole : dterm
  | DApp1 : dterm -> term -> dterm
  | DApp2 : term -> dterm -> dterm
  | 








type sub = var -> universes -> Tot term
type renaming (s:sub) = (forall (x:var) (uvs:universes) . Var? (s x uvs))

let b2i b = if b then 0 else 1

let is_renaming (s:sub)
  : Ghost nat (requires True) (ensures (fun n -> renaming s ==> n = 0 /\ ~(renaming s) ==> n = 1))
= b2i (FStar.StrongExcludedMiddle.strong_excluded_middle (renaming s))

let is_evar (e:term) = b2i (Var? e)

let sub_id : s:sub{renaming s} = Var
let sub_inc : s:sub{renaming s} = fun x uvs -> Var (x+1) uvs
let sub_dec : s:sub{renaming s} = fun x uvs -> if x = 0 then Var x uvs else Var (x - 1) uvs
let sub_inc_above (y:var) : s:sub{renaming s} = fun x uvs -> if x < y then Var x uvs else Var (x+1) uvs

let rec subst (s:sub) (e:term)
  : Pure term
    (requires True)
    (ensures (fun e' -> renaming s /\ Var? e ==> Var? e'))
    (decreases %[is_evar e ; is_renaming s ; 1 ; e])
=
  match e with
  | Var x l -> s x l
  | Const _ _
  | Type_ _ -> e
  | App e1 e2 -> App (subst s e1) (subst s e2)
  | Lam t e -> Lam (subst s t) (subst (sub_lam s) e)
  | Prod t1 c -> Prod (subst s t1) (subst_comp (sub_lam s) c)
  | Refine t1 t2 -> Refine (subst s t1) (subst (sub_lam s) t2)

and sub_lam (s:sub)
  : Tot (s':sub{renaming s ==> renaming s'})
    (decreases %[1; is_renaming s ; 0 ; ()])
=
  fun y uvs -> if y = 0 then Var y uvs else subst sub_inc (s (y - 1) uvs)

and subst_comp (s:sub) (c:comp)
  : Tot comp
  (decreases %[1; is_renaming s ; 1 ; c])
=
  match c with
  | Tot_ t -> Tot_ (subst s t)
  | Pure_ t wp -> Pure_ (subst s t) (subst s wp)


module Ext = FStar.FunctionalExtensionality

(* Substitution extensional; trivial with the extensionality axiom *)
val subst_extensional: s1:sub -> s2:sub{Ext.feq s1 s2} -> e:term ->
                        Lemma (requires True) (ensures (subst s1 e = subst s2 e))
                       (* [SMTPat (subst s1 e);  SMTPat (subst s2 e)] *)
let subst_extensional s1 s2 e = ()

let sub_lam_hoist (t:term) (e:term) (s:sub)
  : Lemma (requires True)
    (ensures (subst s (Lam t e) = Lam (subst s t) (subst (sub_lam s) e)))
= ()

let sub_prod_hoist (t:term) (c:comp) (s:sub)
  : Lemma (subst s (Prod t c) = Prod (subst s t) (subst_comp (sub_lam s) c))
= ()

let sub_refine_hoist (t:term) (phi:term) (s:sub)
  : Lemma (subst s (Refine t phi) = Refine (subst s t) (subst (sub_lam s) phi))
= ()

let sub_beta (e:term) : sub = fun y uvs -> if y = 0 then e else Var (y-1) uvs
let subst_beta (e:term) : term -> term = subst (sub_beta e)


(* Identity *)

let sub_lam_id () : Lemma (sub_lam sub_id == sub_id)
=
  let aux (y:var) (uvs:universes) : Lemma (sub_lam sub_id y uvs = sub_id y uvs) =
    if y = 0 then () else ()
  in
  Ext.intro_feq2 (sub_lam sub_id) sub_id aux

let rec subst_id (e:term)
  : Lemma (subst sub_id e = e)
= match e with
  | Var _ _ -> ()
  | Const _ _
  | Type_ _ -> ()
  | App e1 e2 -> subst_id e1 ; subst_id e2
  | Lam t e -> subst_id t ; sub_lam_id () ; subst_id e ; sub_lam_hoist t e sub_id
  | Prod t c -> subst_id t ; sub_lam_id () ; subst_id_comp c ; sub_prod_hoist t c sub_id
  | Refine t e -> subst_id t ; sub_lam_id () ; subst_id e ; sub_refine_hoist t e sub_id

and subst_id_comp (c:comp)
  : Lemma (subst_comp sub_id c = c)
= match c with
  | Tot_ t -> subst_id t
  | Pure_ t wp -> subst_id t ; subst_id wp

let sub_comp (s1 s2 : sub) : sub = fun y uvs -> subst s2 (s1 y uvs)

let sub_comp_id_left (s:sub)
  : Lemma (sub_comp sub_id s == s)
= let h (y:var) (uvs:universes) : Lemma (sub_comp sub_id s y uvs == s y uvs) = () in
  Ext.intro_feq2 (sub_comp sub_id s) s h

let sub_comp_id_right (s:sub)
  : Lemma (sub_comp s sub_id == s)
=
  let h (y:var) (uvs:universes) : Lemma (sub_comp s sub_id y uvs == s y uvs) =
    subst_id (s y uvs)
  in
  Ext.intro_feq2 (sub_comp s sub_id) s h


(* unneeded *)
let sub_inc_sub_dec_id_retract () : Lemma (sub_comp sub_inc sub_dec == sub_id)
= let h (y:var) (uvs:universes) : Lemma (sub_comp sub_inc sub_dec y uvs == sub_id y uvs) = () in
  Ext.intro_feq2 (sub_comp sub_inc sub_dec) sub_id h


(* Associativity of substitution *)

let sub_comp_inc (s:sub)
  : Lemma (sub_comp s sub_inc == sub_comp sub_inc (sub_lam s))
= let s1 = sub_comp s sub_inc in
  let s2 = sub_comp sub_inc (sub_lam s) in
  let h (y:var) (uvs:universes) : Lemma (s1 y uvs == s2 y uvs) = () in
  Ext.intro_feq2 s1 s2 h

let rec subst_sub_comp (s1 s2 : sub) (e:term)
  : Lemma (requires True)
    (ensures (subst (sub_comp s1 s2) e = subst s2 (subst s1 e)))
    (decreases %[is_evar e ; is_renaming s1 ; is_renaming s2 ; 1 ; e])
= match e with
  | Var _ _ -> ()
  | Const _ _
  | Type_ _ -> ()
  | App e1 e2 -> subst_sub_comp s1 s2 e1 ; subst_sub_comp s1 s2 e2
  | Lam t e ->
    subst_sub_comp s1 s2 t ; sub_lam_comp s1 s2 ; subst_sub_comp (sub_lam s1) (sub_lam s2) e
  | Prod t c ->
    subst_sub_comp s1 s2 t ; sub_lam_comp s1 s2 ; subst_comp_sub_comp (sub_lam s1) (sub_lam s2) c
  | Refine t e ->
    subst_sub_comp s1 s2 t ; sub_lam_comp s1 s2 ; subst_sub_comp (sub_lam s1) (sub_lam s2) e

and sub_lam_comp (s1 s2 : sub)
  : Lemma (requires True)
    (ensures (sub_lam (sub_comp s1 s2) == sub_comp (sub_lam s1) (sub_lam s2)))
    (decreases %[1 ; is_renaming s1 ; is_renaming s2 ; 0 ; ()])
=
  let h (y : var) (uvs:universes)
    : Lemma (sub_lam (sub_comp s1 s2) y uvs == sub_comp (sub_lam s1) (sub_lam s2) y uvs)
  = if y = 0 then () else begin
      (* sub_lam (sub_comp s1 s2) y uvs *)
      (* = subst sub_inc ((sub_comp s1 s2) (y -1) uvs) *)
      (* = subst sub_inc (subst s2 (s1 (y - 1) uvs)) *)

      subst_sub_comp s2 sub_inc (s1 (y - 1) uvs) ;

      (* = subst (sub_comp s2 sub_inc) (s1 (y-1) uvs) *)

      sub_comp_inc s2 ;
      subst_extensional (sub_comp s2 sub_inc) (sub_comp sub_inc (sub_lam s2)) (s1 (y-1) uvs) ;

      (* = subst (sub_comp sub_inc (sub_lam s2)) (s1 (y-1) uvs) *)

      subst_sub_comp sub_inc (sub_lam s2) (s1 (y - 1) uvs)

      (* = subst (sub_lam s2) (subst sub_inc (s1 (y-1) uvs)) *)
      (* = sub_comp (sub_lam s1) (sub_lam s2) y uvs *)
    end
  in Ext.intro_feq2 (sub_lam (sub_comp s1 s2)) (sub_comp (sub_lam s1) (sub_lam s2)) h

and subst_comp_sub_comp (s1 s2 : sub) (c:comp)
  : Lemma (requires True)
    (ensures (subst_comp (sub_comp s1 s2) c == subst_comp s2 (subst_comp s1 c)))
    (decreases %[1 ; is_renaming s1 ; is_renaming s2 ; 1 ; c])
= match c with
  | Tot_ t -> subst_sub_comp s1 s2 t
  | Pure_ t wp -> subst_sub_comp s1 s2 t ; subst_sub_comp s1 s2 wp


let o = sub_comp

let sub_comp_assoc (s1 s2 s3:sub) : Lemma (s1 `o` (s2 `o` s3) == (s1 `o` s2) `o` s3)
=
  let sl = s1 `o` (s2 `o` s3) in
  let sr = (s1 `o` s2) `o` s3 in
  let h (y:var) (uvs:universes) : Lemma (sl y uvs == sr y uvs) =
    subst_sub_comp s2 s3 (s1 y uvs)
  in
  Ext.intro_feq2 sl sr h

(* Shifts *)

let shift_up_above (x:var) (t:term) = subst (sub_inc_above x) t
let shift_up = shift_up_above 0

(* Environments *)

type env = var -> Tot (option term)
let empty : env = fun _ -> None

let extend (g:env) (x:var) (t:term) : env =
  fun (y:var) ->
    if y < x then g y
    else if y = x then Some (n, t)
    else match g y with
    | None -> None
    | Some (n', t') -> Some (n', shift_up_above x t')

(* Definitional equality *)

type def_eq : term -> term -> Type0 =

  (* Equivalence relation *)
  | DEqRefl :
    t:term ->
    def_eq t t
  | DEqSymm :
    #t1:term ->
    #t2:term ->
    def_eq t1 t2 ->
    def_eq t2 t1
  | DEqTrans :
    #t1:term ->
    #t2:term ->
    #t3:term ->
    def_eq t1 t2 ->
    def_eq t2 t3 ->
    def_eq t1 t3

  (* Congruences *)
  | DEqApp :
    #t1:term ->
    #t1':term ->
    #t2:term ->
    #t2':term ->
    def_eq t1 t2 ->
    def_eq t1' t2' ->
    def_eq (App t1 t2) (App t1' t2')
  | DEqLam :
    #t1:term ->
    #t1':term ->
    #t2:term ->
    #t2':term ->
    def_eq t1 t1' ->
    def_eq t2 t2' ->
    def_eq (Lam t1 t2) (Lam t1' t2')
  | DEqProd :
    #t:term ->
    #t':term ->
    #c:comp ->
    #c':comp ->
    def_eq t t' ->
    def_eq_comp c c' ->
    def_eq (Prod t c) (Prod t' c')
  | DEqRefine :
    #t:term ->
    #t':term ->
    #phi:term ->
    #phi':term ->
    def_eq t t' ->
    def_eq phi phi' ->
    def_eq (Refine t phi) (Refine t' phi')

  (* Computation rules *)
  | DEqBeta :
    #t:term ->
    #e1:term ->
    #e2:term ->
    def_eq (App (Lam t e1) e2) (subst_beta e2 e1)
  | DEqNatElimZero :
    #t:term ->
    #e0:term ->
    #esucc:term ->
    def_eq (App (App (App (App (Const NatElim []) t) e0) esucc) (Const Zero [])) e0
  | DEqNatElimSucc :
    #t:term ->
    #e0:term ->
    #esucc:term ->
    #n:term ->
    def_eq (App (App (App (App (Const NatElim []) t) e0) esucc) (App (Const Succ []) n))
           (App esucc (App (App (App (App (Const NatElim []) t) e0) esucc) n))
  | DEqEqElimRefl :
    #t:term ->
    #erefl:term ->
    def_eq (App (App (App (Const EqElim []) t) erefl) (Const Refl [])) erefl

and def_eq_comp : comp -> comp -> Type0 =
  | DEqCompTot :
    #t:term ->
    #t':term ->
    def_eq t t' ->
    def_eq_comp (Tot_ t) (Tot_ t')
  | DEqCompPure :
    #t:term ->
    #t':term ->
    #wp:term ->
    #wp':term ->
    def_eq t t' ->
    def_eq wp wp' ->
    def_eq_comp (Pure_ t wp) (Pure_ t wp')


(* Typing *)


let nat_elim_type =
  List.Tot.fold_right app [
    (* p:nat -> Type0 *)
    cnat `arr` type0 ;
    (* p 0 *)
    Var 0 `app` czero ;
    (* forall n, p n -> p (n + 1) *)
    cnat `arr` (Var 2 `app` Var 0) `arr` (Var 3 `app` succ (Var 1)) ;
    (* n *)
    cnat
  ]
  (* p n *)
  (Var 3 `app` Var 0)

(* a:Type0 -> a -> a -> Type0 *)
let eq_type = type_0 `arr` Var 0 `arr` Var 1 `arr` type_0

let eq_elim_type =
  List.Tot.fold_right app [
    (* a:Type0 *)
    type_0 ;
    (* x:a *)
    Var 0 ;
    (* p: a -> Type0 *)
    (Var 1 `arr` type_0) ;
    (* p x *)
    (Var 0 `app` Var 1) ;
    (* y *)
    Var 3 ;
    (* x = y *)
    eq (Var 4) (Var 3) (Var 0) ;
  ]
  (* p y *)
  (Var 3 `app` Var 1)

let max (u1 u2 : nat) = if u1 < u2 then u2 else u1

type typing : env -> term -> comp -> Type =
  | TyVar :
    #g:env ->
    valid g ->
    x:var{Some? (g x)} ->
    typing g (tot (Var x []))

  | TyConst :
    #g:env ->
    #c:const ->
    #t:term ->
    typing_const c t ->
    typing g (Const c) (tot t)

  (* Since we don't want constructors to contain type parameters we need to have a *)
  (* specific typing rule *)
  | TyRefl :
    #g:env ->
    #e:term ->
    #t:term ->
    typing g e (tot t) ->
    typing g (refl `app` e) (tot (eq t e e))

  | TyType :
    u:universe_level ->
    typing env (Type_ u) (tot (Type_ (u+1)))

  | TyLam :
    #g:env ->
    #t:term ->
    #c:term ->
    e:term ->
    typing (extend g 0 t) e c ->
    typing g (Lam t e) (tot (Prod t c))

  | TyApp :
    #g:env ->
    #t:term ->
    #e1:term ->
    #c:comp ->
    #e2:term ->
    he1:typing env e1 (tot (Prod t c)) ->
    he2:typing env e2 (tot t) ->
    typing_comp env (App e1 e2) c

  | TyProd :
    #g:env ->
    #t:term ->
    #c:comp ->
    #u1:universe ->
    #u2:universe ->
    typing g t (tot (Type_ u1)) ->
    comp_typing g c (tot (Type_ u2)) ->
    typing g (Prod t c) (tot (Type_ (max u1 u2)))

  (* Impredicative *)
  | TyRefine :
    #g:env ->
    #t:term ->
    #phi:term ->
    #u:universe ->
    #v:universe ->
    typing g t (tot (Type_ u)) ->
    typing g phi (tot (Type_ v)) ->
    typing g (Refine t phi) (tot (Type_ u))

  | TyConv :
    #g:env ->
    #e:term ->
    #t1:term ->
    #t2:term ->
    typing g e (tot t1) ->
    def_eq t1 t2 ->
    typing g e t2

and typing_comp : env -> term -> comp -> Type =

  | TyTot :
    #g:env ->
    #e:term ->
    #t:term ->
    typing g e t ->
    typing_comp g e (Tot_ t)

and comp_typing : env -> comp -> term -> Type =
  | TyTot_ :
    #g:env ->
    #t:term ->
    #u:universe ->
    typing g t (Type_ u) ->
    comp_typing g (Tot_ t) (Type_ u)

  (* Impredicative *)
  | TyPure_ :
    #g:env ->
    #t:term ->
    #wp:term ->
    #u:universe ->
    typing g t (Type_ u) ->
    typing g wp ((t `arr` type_0) `arr` type_0) ->
    comp_typing g (Pure_ t wp) (Type_ u)

and typing_const : env -> const -> term -> Type =
  | TyNat : typing_const Nat type_0
  | TyZero : typing_const Zero cnat
  | TySucc : typing_const Succ (cnat `arr` cnat)
  | TyNatElim : typing_const NatElim nat_elim_type
  | TyEq : typing_const Eq eq_type
  | TyEqElim : typing_const EqElim eq_elim_type


let typing_equiv (g:env) (t1 t2 : term) =
    (tt:term -> typing g t1 tt -> typing g t2 tt) * (tt:term -> typing g t2 tt -> typing g t1 tt)

let rec def_eq_well_typed #g #t1 #t2 (deq:def_eq t1 t2)
  : Tot (typing_equiv g t1 t2)
= match deq with
  | DEqRefl _ -> let id (t:term) (x:typing g t1 t) = x in id, id
  | DEqSymm deq -> let (a,b) = def_eq_well_typed deq in (b,a)
  | DEqTrans deq1 deq2 ->
    let (a1, b1) = def_eq_well_typed deq1 in
    let (a2, b2) = def_eq_well_typed deq2 in
    (fun t x -> a2 t (a1 t x)), (fun t x -> b1 t (b2 t x))
  | DEqApp deq1 deq2 ->
    let (a1, b1) = def_eq_well_typed deq1 in
    let (a2, b2) = def_eq_well_typed deq2 in
    let a tt (x:typing g t1 t) =
      match x with
      | TyApp #g #t #e1 #c #e2 he1 he2 ->
        TyApp (a1 he1) (a2 he2)
      | TyConv 
      let TyApp ()

let rec typing_type_well_typed #g #e #t (d:typing g e t) : u:universe & typing g t (Type_ u)
= match d with
  |
