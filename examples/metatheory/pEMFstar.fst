module PEMFstar

module L = FStar.List.Pure

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


let cnat = Const Nat []
let czero = Const Zero []
let csucc = Const Succ []
(* TODO : put the right universes *)
let cnat_elim = Const NatElim []
let ceq = Const Eq []
let crefl = Const Refl []
let ceq_elim = Const EqElim []
let arr t1 t2 = Prod t1 (Tot_ t2)
let app e1 e2 = App e1 e2
let type_0 = Type_ 0
let succ n = app csucc n
let refl e = app crefl e
let eq t e1 e2 = ceq `app` t `app` e1 `app` e2
let var_ x = Var x []



(* Derived term (n hole term contexts) *)
type dterm : nat -> Type =
  | Term : term -> dterm 0
  | Hole : dterm 1
  | DApp : #n1:nat -> #n2:nat -> dterm n1 -> dterm n2 -> dterm (n1 + n2)
  | DLam : #n1:nat -> #n2:nat -> dterm n1 -> dterm n2 -> dterm (n1 + n2)
  | DProd : #n1:nat -> #n2:nat -> dterm n1 -> dcomp n2 -> dterm (n1 + n2)
  | DRefine : #n1:nat -> #n2:nat -> dterm n1 -> dterm n2 -> dterm (n1 + n2)

(* Derived computation (n hole computation context) *)
and dcomp : nat -> Type =
  | DTot : #n:nat -> dterm n -> dcomp n
  | DPure : #n1:nat -> #n2:nat -> dterm n1 -> dterm n2 -> dcomp (n1 + n2)

let add (x y:nat): nat = x + y
let sum :list nat -> nat = L.fold_left add 0
let nat_monoid ()
  : Lemma (
    (forall u v w. add u (add v w) == add (add u v) w) /\
    (forall u. add u 0 == u) /\
    (forall u. add 0 u == u)
  )
= ()

let rec sum_plus (l1 l2 : list nat)
  : Lemma (requires True) (ensures (sum l1 + sum l2 == sum (l1 @ l2))) (decreases l1)
=
  nat_monoid () ;
  L.fold_left_append_monoid add 0 l1 l2


let (<|) f x = f x

let rec dterm_as_term : dterm 0 -> term = function
  | Term t -> t
  | DApp dt1 dt2 -> App (dterm_as_term dt1) (dterm_as_term dt2)
  | DLam dt1 dt2 -> Lam (dterm_as_term dt1) (dterm_as_term dt2)
  | DProd dt dc -> Prod (dterm_as_term dt) (dcomp_as_comp dc)
  | DRefine dt1 dt2 -> Refine (dterm_as_term dt1) (dterm_as_term dt2)

and dcomp_as_comp : dcomp 0 -> comp = function
  | DTot dt -> Tot_ (dterm_as_term dt)
  | DPure dt1 dt2 -> Pure_ (dterm_as_term dt1) (dterm_as_term dt2)

let split_rebuild_lemma (#a:Type) (n1 n2:nat) (l:list a) (f : a -> nat)
  : Lemma (requires (b2t (L.length l >= n1 + n2)))
    (ensures begin
      let l1, l2 = L.first_N n1 l in
      let l2', l3 = L.first_N n2 l2 in
      L.length l2 >= n2 /\
      sum (L.map f (l1 @ l2')) == sum (L.map f l1) + sum (L.map f l2') /\
      (l1@l2', l3) == L.first_N (n1 + n2) l
    end)
=
  let l1, l2 = L.first_N n1 l in
  let l2', l3 = L.first_N n2 l2 in
  L.first_N_length n1 l ;
  L.first_N_assoc n1 n2 l ;
  sum_plus (L.map f l1) (L.map f l2') ;
  L.map_append f l1 l2'

(* Operadic composition for derived term *)
let rec dterm_comp_extended (#n:nat) (c:dterm n) (l:list (k:nat & dterm k))
  : Pure (dterm (sum <| L.map (dfst #nat #dterm) (fst <| L.first_N n l)) * list (k:nat & dterm k))
    (requires (b2t (L.length l >= n)))
    (ensures (fun (c', l') -> snd (L.first_N n l) == l'))
    (decreases c)
= match c with
  | Term t -> c, l
  | Hole ->
    let (|k, x|) :: xs = l in
    assert_norm (sum <| L.map (dfst #nat #dterm) (fst <| L.first_N 1 l) == k) ;
    x, xs
  | DApp #n1 #n2 c1 c2 ->
    split_rebuild_lemma n1 n2 l (dfst #nat #dterm) ;
    let c1', l = dterm_comp_extended c1 l in
    let c2', l = dterm_comp_extended c2 l in
    DApp c1' c2', l
  | DLam #n1 #n2 c1 c2 ->
    split_rebuild_lemma n1 n2 l (dfst #nat #dterm) ;
    let c1', l = dterm_comp_extended c1 l in
    let c2', l = dterm_comp_extended c2 l in
    DLam c1' c2', l
  | DProd #n1 #n2 c1 c2 ->
    split_rebuild_lemma n1 n2 l (dfst #nat #dterm) ;
    let c1', l = dterm_comp_extended c1 l in
    let c2', l = dterm_comp_extended_comp c2 l in
    DProd c1' c2', l
  | DRefine #n1 #n2 c1 c2 ->
    split_rebuild_lemma n1 n2 l (dfst #nat #dterm) ;
    let c1', l = dterm_comp_extended c1 l in
    let c2', l = dterm_comp_extended c2 l in
    DRefine c1' c2', l

and dterm_comp_extended_comp (#n:nat) (c:dcomp n) (l:list (k:nat & dterm k))
  : Pure (dcomp (sum <| L.map (dfst #nat #dterm) (fst <| L.first_N n l)) * list (k:nat & dterm k))
    (requires (b2t (L.length l >= n)))
    (ensures (fun (c', l') -> snd (L.first_N n l) == l'))
    (decreases c)
= match c with
  | DTot c -> let c', l = dterm_comp_extended c l in DTot c', l
  | DPure #n1 #n2 c1 c2 ->
    split_rebuild_lemma n1 n2 l (dfst #nat #dterm) ;
    let c1', l = dterm_comp_extended c1 l in
    let c2', l = dterm_comp_extended c2 l in
    DPure c1' c2', l


let dterm_comp (#n:nat) (c:dterm n) (l:list (k:nat & dterm k){L.length l == n})
  : dterm (sum <| L.map dfst l)
= L.first_N_length_total l ;
  fst <| dterm_comp_extended c l




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
let sub_dec_above (y:var) (z:var{z <= y + 1}) : s:sub{renaming s} = fun x uvs -> if x <= y + 1 then Var 0 uvs else Var (x-z) uvs

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

let map_opt f = function
  | None -> None
  | Some x -> Some (f x)

let extend (g:env) (x:var) (t:term) : env =
  fun (y:var) ->
    if y < x then g y
    else if y = x then Some t
    else map_opt (shift_up_above x) <| g (y - 1)

let rec count_under (g:env) (x:var) : Tot (n:nat{n <= x + 1}) (decreases x) =
  let k = if None? (g x) then 0 else 1 in
  if x = 0 then k else count_under g (x-1) + k

let restrict_above (g:env) (x:var) : env =
  let n = count_under g x in
  fun y -> if y <= x then None else map_opt (subst <| sub_dec_above x n) (g y)

let valid (typing : env -> term -> comp -> Type0) (g:env) : Type0 =
  forall (x:var). None? (g x) \/
    (exists (u:universe_level). typing (restrict_above g x) (Some?.v (g x)) (Tot_ (Type_ u)))

let rec extend_with_ctx1 (g:env) (ctx:dterm 1) : Tot env (decreases ctx) =
  match ctx with
  | Hole -> g
  | DApp #n1 #n2 dt1 dt2 ->
    if n1 = 1
    then extend_with_ctx1 g dt1
    else extend_with_ctx1 g dt2
  | DLam #n1 #n2 dt1 dt2
  | DRefine #n1 #n2 dt1 dt2 ->
    if n1 = 1
    then extend_with_ctx1 g dt1
    else extend_with_ctx1 (extend g 0 (dterm_as_term dt1)) dt2
  | DProd #n1 #n2 dt dc ->
    if n1 = 1
    then extend_with_ctx1 g dt
    else extend_with_comp_ctx1 (extend g 0 (dterm_as_term dt)) dc

and extend_with_comp_ctx1 (g:env) (ctx:dcomp 1) : Tot env (decreases ctx) =
  match ctx with
  | DTot dt -> extend_with_ctx1 g dt
  | DPure #n1 #n2 dt1 dt2 ->
    if n1 = 1
    then extend_with_ctx1 g dt1
    else extend_with_ctx1 g dt2


(* Definitions used during typing *)

let nat_elim_type =
  List.Tot.fold_right app [
    (* p:nat -> Type0 *)
    cnat `arr` type_0 ;
    (* p 0 *)
    var_ 0 `app` czero ;
    (* forall n, p n -> p (n + 1) *)
    cnat `arr` (var_ 2 `app` var_ 0) `arr` (var_ 3 `app` succ (var_ 1)) ;
    (* n *)
    cnat
    ]
    (* p n *)
    (var_ 3 `app` var_ 0)

(* a:Type0 -> a -> a -> Type0 *)
let eq_type = type_0 `arr` var_ 0 `arr` var_ 1 `arr` type_0

let eq_elim_type =
  List.Tot.fold_right app [
    (* a:Type0 *)
    type_0 ;
    (* x:a *)
    var_ 0 ;
    (* p: a -> Type0 *)
    (var_ 1 `arr` type_0) ;
    (* p x *)
    (var_ 0 `app` var_ 1) ;
    (* y *)
    var_ 3 ;
    (* x = y *)
    eq (var_ 4) (var_ 3) (var_ 0) ;
    ]
    (* p y *)
    (var_ 3 `app` var_ 1)

let max (u1 u2 : nat) = if u1 < u2 then u2 else u1

(* Typing *)

let tot = Tot_

noeq
type typing (def_eq : env -> term -> term -> Type0) : env -> term -> comp -> Type0 =
  | TyVar :
    #g:env ->
    valid (typing def_eq) g ->
    x:var{Some? (g x)} ->
    typing def_eq g (Var x []) (tot (Some?.v <| g x))

  | TyConst :
    #g:env ->
    #c:const ->
    #t:term ->
    typing_const c t ->
    typing def_eq g (Const c []) (tot t)

  (* Since we don't want constructors to contain type parameters we need to have a *)
  (* specific typing rule *)
  | TyRefl :
    #g:env ->
    #e:term ->
    #t:term ->
    typing def_eq g e (tot t) ->
    typing def_eq g (refl e) (tot (eq t e e))

  | TyType :
    #g:env ->
    u:universe_level ->
    typing def_eq g (Type_ u) (tot (Type_ (u+1)))

  | TyLam :
    #g:env ->
    #t:term ->
    #c:comp ->
    e:term ->
    typing def_eq (extend g 0 t) e c ->
    typing def_eq g (Lam t e) (tot (Prod t c))

  | TyApp :
    #g:env ->
    #t:term ->
    #e1:term ->
    #c:comp ->
    #e2:term ->
    he1:typing def_eq g e1 (tot (Prod t c)) ->
    he2:typing def_eq g e2 (tot t) ->
    typing def_eq g (App e1 e2) c

  | TyProd :
    #g:env ->
    #t:term ->
    #c:comp ->
    #u1:universe_level ->
    #u2:universe_level ->
    typing def_eq g t (tot (Type_ u1)) ->
    comp_typing def_eq g c (tot (Type_ u2)) ->
    typing def_eq g (Prod t c) (tot (Type_ (max u1 u2)))

  (* Impredicative *)
  | TyRefine :
    #g:env ->
    #t:term ->
    #phi:term ->
    #u:universe_level ->
    #v:universe_level ->
    typing def_eq g t (tot (Type_ u)) ->
    typing def_eq g phi (tot (Type_ v)) ->
    typing def_eq g (Refine t phi) (tot (Type_ u))

  | TyConv :
    #g:env ->
    #e:term ->
    #t1:term ->
    #t2:term ->
    typing def_eq g e (tot t1) ->
    def_eq g t1 t2 ->
    typing def_eq g e (tot t2)

and comp_typing (def_eq : env -> term -> term -> Type) : env -> comp -> comp -> Type =
  | TyTot_ :
    #g:env ->
    #t:term ->
    #u:universe_level ->
    typing def_eq g t (tot (Type_ u)) ->
    comp_typing def_eq g (Tot_ t) (tot (Type_ u))

  (* Impredicative *)
  | TyPure_ :
    #g:env ->
    #t:term ->
    #wp:term ->
    #u:universe_level ->
    typing def_eq g t (tot <| Type_ u) ->
    typing def_eq g wp (tot <| (t `arr` type_0) `arr` type_0) ->
    comp_typing def_eq g (Pure_ t wp) (tot <| Type_ u)

and typing_const : const -> term -> Type =
  | TyNat : typing_const Nat type_0
  | TyZero : typing_const Zero cnat
  | TySucc : typing_const Succ (cnat `arr` cnat)
  | TyNatElim : typing_const NatElim nat_elim_type
  | TyEq : typing_const Eq eq_type
  | TyEqElim : typing_const EqElim eq_elim_type


(* Atomic steps generating the definitional equality *)

type reduce : term -> term -> Type =
  | RedBeta :
    #t:term ->
    #e1:term ->
    #e2:term ->
    reduce (App (Lam t e1) e2) (subst_beta e2 e1)

  | RedNatElimZero :
    #t:term ->
    #e0:term ->
    #esucc:term ->
    reduce (App (App (App (App (Const NatElim []) t) e0) esucc) (Const Zero [])) e0

  | RedNatElimSucc :
    #t:term ->
    #e0:term ->
    #esucc:term ->
    #n:term ->
    reduce (App (App (App (App (Const NatElim []) t) e0) esucc) (App (Const Succ []) n))
           (App esucc (App (App (App (App (Const NatElim []) t) e0) esucc) n))

  | RedEqElimRefl :
    #t:term ->
    #erefl:term ->
    reduce (App (App (App (Const EqElim []) t) erefl) (Const Refl [])) erefl

(* Definitional equality *)

(* let apply_ctx (#n:nat) (ctx:dterm n) (ts:list term{L.length ts == n}) *)
(*   : Tot term *)
(* = let to_dterm (t:term) : k:nat & dterm k = (|0, Term t |) in *)
(*   let ts : l:list (k:nat & dterm k){L.length l == n} = L.map to_dterm ts in *)
(*   (\* TODO : this fails to prove (I guess it needs induction) *\) *)
(*   assert_norm (sum <| L.map dfst ts == 0) ; *)
(*   dterm_as_term (dterm_comp ctx ts) *)

let apply_ctx (ctx:dterm 1) (l:list term{match l with | [_] -> True | _ -> False}) : term =
  let l : l:list (k:nat & dterm k){L.length l = 1} = [(|0, Term (L.hd l)|)]in
  assert_norm (sum <| L.map dfst l == 0) ;
  dterm_as_term (dterm_comp ctx l)

noeq
type def_eq : env -> term -> term -> Type0 =

  (* Equivalence relation *)
  | DEqRefl :
    #g:env ->
    #t:term ->
    #a:term ->
    typing def_eq g t (tot a) ->
    def_eq g t t

  | DSTClosure :
    #g:env ->
    #t1:term ->
    #t2:term ->
    SymmetricTransitiveClosure.stc (def_eq g) t1 t2 ->
    def_eq g t1 t2

  | DCongr :
    #g:env ->
    #n:nat ->
    #t1:term ->
    #t2:term ->
    ctx:dterm 1 ->
    def_eq (extend_with_ctx1 g ctx) t1 t2 ->
    def_eq g (apply_ctx ctx [t1]) (apply_ctx ctx [t2])

  | DComputation :
    #g:env ->
    #t1:term ->
    #t2:term ->
    #a:term ->
    typing def_eq g t1 (tot a) ->
    typing def_eq g t2 (tot a) ->
    reduce t1 t2 ->
    def_eq g t1 t2




(* type def_eq : env -> term -> term -> Type0 = *)

(*   (\* Equivalence relation *\) *)
(*   | DEqRefl : *)
(*     #g:env -> *)
(*     #t:term -> *)
(*     #a:term -> *)
(*     typing g t a -> *)
(*     def_eq g t t *)
(*   | DEqSymm : *)
(*     #g:env -> *)
(*     #t1:term -> *)
(*     #t2:term -> *)
(*     def_eq g t1 t2 -> *)
(*     def_eq g t2 t1 *)
(*   | DEqTrans : *)
(*     #g:env -> *)
(*     #t1:term -> *)
(*     #t2:term -> *)
(*     #t3:term -> *)
(*     def_eq g t1 t2 -> *)
(*     def_eq g t2 t3 -> *)
(*     def_eq g t1 t3 *)

(*   (\* Congruences *\) *)
(*   | DEqApp : *)
(*     #g:env -> *)
(*     #t1:term -> *)
(*     #t1':term -> *)
(*     #t2:term -> *)
(*     #t2':term -> *)
(*     def_eq g t1 t2 -> *)
(*     def_eq g t1' t2' -> *)
(*     def_eq g (App t1 t2) (App t1' t2') *)

(*   | DEqLam : *)
(*     #g:env -> *)
(*     #t1:term -> *)
(*     #t1':term -> *)
(*     #t2:term -> *)
(*     #t2':term -> *)
(*     def_eq g t1 t1' -> *)
(*     def_eq (extend g 0 t1) t2 t2' -> *)
(*     def_eq g (Lam t1 t2) (Lam t1' t2') *)

(*   | DEqProd : *)
(*     #g:env -> *)
(*     #t:term -> *)
(*     #t':term -> *)
(*     #c:comp -> *)
(*     #c':comp -> *)
(*     def_eq g t t' -> *)
(*     def_eq_comp (extend g 0 t) c c' -> *)
(*     def_eq g (Prod t c) (Prod t' c') *)

(*   | DEqRefine : *)
(*     #g:env -> *)
(*     #t:term -> *)
(*     #t':term -> *)
(*     #phi:term -> *)
(*     #phi':term -> *)
(*     def_eq g t t' a -> *)
(*     def_eq (extend g 0 t) phi phi' -> *)
(*     def_eq g (Refine t phi) (Refine t' phi') *)

(*   (\* Computation rules *\) *)
(*   | DEqBeta : *)
(*     #g:env -> *)
(*     #t:term -> *)
(*     #e1:term -> *)
(*     #e2:term -> *)
(*     #a:term -> *)
(*     typing (extend g 0 t) e1 a -> *)
(*     typing g e2 t -> *)
(*     def_eq (App (Lam t e1) e2) (subst_beta e2 e1) *)

(*   | DEqNatElimZero : *)
(*     #g:env -> *)
(*     #t:term -> *)
(*     #e0:term -> *)
(*     #esucc:term -> *)
(*     typing g t (Prod cnat ctype) *)
(*     def_eq (App (App (App (App (Const NatElim []) t) e0) esucc) (Const Zero [])) e0 *)

(*   | DEqNatElimSucc : *)
(*     #t:term -> *)
(*     #e0:term -> *)
(*     #esucc:term -> *)
(*     #n:term -> *)
(*     def_eq (App (App (App (App (Const NatElim []) t) e0) esucc) (App (Const Succ []) n)) *)
(*            (App esucc (App (App (App (App (Const NatElim []) t) e0) esucc) n)) *)
(*   | DEqEqElimRefl : *)
(*     #t:term -> *)
(*     #erefl:term -> *)
(*     def_eq (App (App (App (Const EqElim []) t) erefl) (Const Refl [])) erefl *)

(* and def_eq_comp : comp -> comp -> Type0 = *)
(*   | DEqCompTot : *)
(*     #t:term -> *)
(*     #t':term -> *)
(*     def_eq g t t' a -> *)
(*     def_eq_comp (Tot_ t) (Tot_ t') *)
(*   | DEqCompPure : *)
(*     #t:term -> *)
(*     #t':term -> *)
(*     #wp:term -> *)
(*     #wp':term -> *)
(*     def_eq g t t' a -> *)
(*     def_eq wp wp' -> *)
(*     def_eq_comp (Pure_ t wp) (Pure_ t wp') *)




(* let typing_equiv (g:env) (t1 t2 : term) = *)
(*     (tt:term -> typing g t1 tt -> typing g t2 tt) * (tt:term -> typing g t2 tt -> typing g t1 tt) *)

(* let rec def_eq_well_typed #g #t1 #t2 (deq:def_eq t1 t2) *)
(*   : Tot (typing_equiv g t1 t2) *)
(* = match deq with *)
(*   | DEqRefl _ -> let id (t:term) (x:typing g t1 t) = x in id, id *)
(*   | DEqSymm deq -> let (a,b) = def_eq_well_typed deq in (b,a) *)
(*   | DEqTrans deq1 deq2 -> *)
(*     let (a1, b1) = def_eq_well_typed deq1 in *)
(*     let (a2, b2) = def_eq_well_typed deq2 in *)
(*     (fun t x -> a2 t (a1 t x)), (fun t x -> b1 t (b2 t x)) *)
(*   | DEqApp deq1 deq2 -> *)
(*     let (a1, b1) = def_eq_well_typed deq1 in *)
(*     let (a2, b2) = def_eq_well_typed deq2 in *)
(*     let a tt (x:typing g t1 t) = *)
(*       match x with *)
(*       | TyApp #g #t #e1 #c #e2 he1 he2 -> *)
(*         TyApp (a1 he1) (a2 he2) *)
(*       | TyConv  *)
(*       let TyApp () *)

(* let rec typing_type_well_typed #g #e #t (d:typing g e t) : u:universe & typing g t (Type_ u) *)
(* = match d with *)
(*   | *)
