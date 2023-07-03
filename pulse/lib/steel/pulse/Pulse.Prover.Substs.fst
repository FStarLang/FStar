module Pulse.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Typing.Metatheory

module L = FStar.List.Tot

module Env = Pulse.Typing.Env

let rec nt_subst_st_comp_commutes (s:st_comp) (ss:nt_substs)
  : Lemma (ensures nt_subst_st_comp s ss ==
           { s with res = nt_subst_term s.res ss;
                    pre = nt_subst_term s.pre ss;
                    post = nt_subst_term s.post ss; })
          (decreases L.length ss) =
  match ss with
  | [] -> ()
  | (NT x e)::tl ->
    nt_subst_st_comp_commutes (subst_st_comp s [ NT x e ]) tl


let rec nt_subst_comp_commutes (c:comp) (ss:nt_substs)
  : Lemma (ensures (let r = nt_subst_comp c ss in
           (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) ss)) /\
           (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
           (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) ss)
                                              (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
           (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) ss)
                                            (nt_subst_st_comp (st_comp_of_comp c) ss))))
          (decreases L.length ss) =
  
  match ss with
  | [] -> ()
  | (NT x e)::tl ->
    nt_subst_comp_commutes (subst_comp c [ NT x e ]) tl

let rec nt_subst_term_compose (t:term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_term (nt_subst_term t ss1) ss2 ==
                 nt_subst_term t (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_term_compose (subst_term t [ NT x e ]) tl ss2

let rec nt_subst_st_term_compose (t:st_term) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_st_term (nt_subst_st_term t ss1) ss2 ==
                 nt_subst_st_term t (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_st_term_compose (subst_st_term t [ NT x e ]) tl ss2

let rec nt_subst_comp_compose (c:comp) (ss1 ss2:nt_substs)
: Lemma (ensures nt_subst_comp (nt_subst_comp c ss1) ss2 ==
                 nt_subst_comp c (compose_nt_substs ss1 ss2))
        (decreases L.length ss1) =

match ss1 with
| [] -> ()
| (NT x e)::tl -> nt_subst_comp_compose (subst_comp c [ NT x e ]) tl ss2

let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b{y == x} = x

let rec st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (ss:nt_substs { well_typed_ss g uvs ss })
: Tot (st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss))
      (decreases L.length ss) =

match bindings uvs with
| [] ->
  assert (equal (push_env uvs g') g');
  t_typing

| _ ->
  let x, ty, uvs' = remove_binding uvs in
  let (NT y e)::ss' = ss in
  let e_typing = FStar.IndefiniteDescription.elim_squash #(tot_typing g e ty) () in
  push_env_assoc (singleton_env (fstar_env uvs) x ty) uvs' g';
  let t_typing
    : st_typing (push_env g (push_env (singleton_env (fstar_env g) x ty) (push_env uvs' g'))) t c
    = coerce_eq t_typing () in
  let t_typing
    : st_typing (push_env g (subst_env (push_env uvs' g') [ NT y e ]))
                (subst_st_term t [ NT y e ])
                (subst_comp c [ NT y e ])
    = st_typing_subst g x ty (push_env uvs' g') e_typing t_typing in

  assume (subst_env (push_env uvs' g') [ NT y e ] ==
          push_env (subst_env uvs' [ NT y e ]) (subst_env g' [ NT y e ]));

  st_typing_nt_substs g
    (subst_env uvs' [ NT y e ])
    (subst_env g' [ NT y e ])
    t_typing ss'

let vprop_equiv_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#p1 #p2:vprop) (veq:vprop_equiv (push_env g (push_env uvs g')) p1 p2)
  (ss:nt_substs { well_typed_ss g uvs ss })
: vprop_equiv (push_env g (nt_subst_env g' ss)) (nt_subst_term p1 ss) (nt_subst_term p2 ss) =

admit ()

let vprop_equiv_nt_substs_derived _ _ _ _ = admit ()


type map = m:Map.t var term {
  forall (x:var). (~ (Map.contains m x)) ==> Map.sel m x == tm_unknown
}

let related (l:list (var & term)) (m:map) =
  (forall (b:var & term).
          L.memP b l ==> (Map.contains m (fst b) /\
                          Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var). Map.contains m x ==> L.memP (x, Map.sel m x) l)

noeq
type t = {
  l : list (var & term);
  m : m:map { related l m }
}

let rec as_nt_substs_aux (l:list (var & term)) : nt_substs =
  match l with
  | [] -> []
  | (x, t)::tl -> (NT x t)::(as_nt_substs_aux tl)

let as_nt_substs s = as_nt_substs_aux s.l

let as_map s = s.m

let empty = {
  l = [];
  m = Map.const_on Set.empty tm_unknown;
}

let empty_dom () = assert (Set.equal (dom empty) Set.empty)

let singleton (x:var) (t:term) = {
  l = [ (x, t) ];
  m = Map.upd (Map.const_on Set.empty tm_unknown) x t;
}

//
// TODO: Move to ulib
//
let rec append_memP (#a:Type) (l1 l2:list a) (x:a)
  : Lemma (L.memP x (l1 @ l2) <==> (L.memP x l1 \/ L.memP x l2))
          [SMTPat (L.memP x (l1 @ l2))] =
  match l1 with
  | [] -> ()
  | _::tl -> append_memP tl l2 x

let push s1 s2 = {
  l = s1.l @ s2.l;
  m = Map.concat s1.m s2.m;
}

let push_as_map _ _ = ()

let check_well_typedness g uvs ss = admit (); true

// let t _ = magic ()
// let as_subst _ = magic ()
// let as_map _ = magic ()
// let subst_as_map _ = admit ()
// let equal_elim _ _ = admit ()
// let empty _ = magic ()
// let empty_dom _ = admit ()
// let singleton _ = magic ()
// let singleton_dom _ _ = admit ()
// let push _ _ = magic ()
// let push_substs_as_map _ _ = admit ()
// let push_subst_term _ _ _ = admit ()
// let push_subst_st_term _ _ _ = admit ()
// let push_subst_comp _ _ _ = admit ()
// let subst_closed_term _ _ = admit ()
// let subst_closed_st_term _ _ = admit ()
// let subst_closed_comp _ _ = admit ()
// let diff _ _ = magic ()
// let diff_push _ _ = admit ()
