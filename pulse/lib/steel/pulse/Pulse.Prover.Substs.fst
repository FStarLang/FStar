module Pulse.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Typing.Metatheory

module L = FStar.List.Tot

module Env = Pulse.Typing.Env

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b {y == x} = x

let rec no_repeats (l:list var) : Type0 =
  match l with
  | [] -> True
  | x::tl -> (~ (L.memP x tl)) /\ no_repeats tl  

type ss_dom = l:list var { no_repeats l }

type ss_map = m:Map.t var term {
  forall (x:var). (~ (Map.contains m x)) ==> Map.sel m x == tm_unknown
}

let remove_map (m:ss_map) (x:var) =
  Map.restrict (Set.complement (Set.singleton x)) (Map.upd m x tm_unknown)

let rec is_dom (l:ss_dom) (m:ss_map) : Type0 =
  match l with
  | [] -> Set.equal (Map.domain m) Set.empty
  | x::tl ->
    Map.contains m x /\ is_dom tl (remove_map m x)

let rec is_dom_mem (l:ss_dom) (m:ss_map)
  : Lemma
      (requires is_dom l m)
      (ensures forall (x:var).{:pattern L.memP x l \/ Map.contains m x}
                              L.memP x l <==> Map.contains m x)
      [SMTPat (is_dom l m)] =
  match l with
  | [] -> ()
  | y::tl -> is_dom_mem tl (remove_map m y)

noeq
type ss_t = {
  l : ss_dom;
  m : m:ss_map { is_dom l m }
}

let as_map (ss:ss_t) = ss.m

let empty = { l = []; m = Map.const_on Set.empty tm_unknown }

let is_dom_push
  (l:ss_dom)
  (m:ss_map { is_dom l m })
  (x:var { ~ (Map.contains m x ) })
  (t:term)
  : Lemma (is_dom (x::l) (Map.upd m x t)) =

  assert (Map.equal (remove_map (Map.upd m x t) x) m)

let push (ss:ss_t) (x:var { ~ (contains ss x) }) (t:term) : ss_t =
  
  is_dom_push ss.l ss.m x t;
  { l = x::ss.l;
    m = Map.upd ss.m x t }

let tail (ss:ss_t { Cons? ss.l }) : ss_t =
   { l = L.tl ss.l; m = remove_map ss.m (L.hd ss.l) }

let rec push_ss (ss1:ss_t) (ss2:ss_t { Set.disjoint (dom ss1) (dom ss2) })
  : Tot ss_t (decreases L.length ss2.l) =
  match ss2.l with
  | [] -> ss1
  | x::tl ->
    push_ss (push ss1 x (Map.sel ss2.m x)) (tail ss2)

#push-options "--warn_error -271"
let push_as_map (ss1 ss2:ss_t)
  : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
          (ensures Map.equal (as_map (push_ss ss1 ss2))
                             (Map.concat (as_map ss1) (as_map ss2)))
          (decreases L.length ss2.l)
          [SMTPat (as_map (push_ss ss1 ss2))] =

  let rec aux (ss1 ss2:ss_t)
    : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
            (ensures Map.equal (as_map (push_ss ss1 ss2))
                               (Map.concat (as_map ss1) (as_map ss2)))
            (decreases L.length ss2.l)
            [SMTPat ()] =
    match ss2.l with
    | [] -> ()
    | x::tl -> aux (push ss1 x (Map.sel ss2.m x)) (tail ss2)
  in
  ()
#pop-options

let rec remove_l (l:ss_dom) (x:var { L.memP x l })
  : Pure ss_dom
         (requires True)
         (ensures fun r -> forall (y:var). L.memP y r <==> (L.memP y l /\ y =!= x)) =
  match l with
  | [] -> assert False; []
  | y::tl ->
    if y = x then tl
    else y::(remove_l tl x)

let rec is_dom_remove
  (l:ss_dom)
  (m:ss_map { is_dom l m })
  (x:var { Map.contains m x })
  : Lemma (is_dom (remove_l l x) (remove_map m x))
          [SMTPat (remove_l l x); SMTPat (remove_map m x)] =
 
  match l with
  | [] -> ()
  | y::tl ->
    if x = y then ()
    else let t_y = Map.sel m y in
         let m1 = remove_map m y in
         is_dom_remove tl m1 x;
         assert (is_dom (remove_l tl x) (remove_map m1 x));
         is_dom_push (remove_l tl x) (remove_map m1 x) y t_y;
         assert (Map.equal (Map.upd (remove_map m1 x) y t_y)
                           (remove_map m x))

let rec ss_term (t:term) (ss:ss_t) : Tot term (decreases L.length ss.l) =
  match ss.l with
  | [] -> t
  | y::tl ->
    let t = subst_term t [ NT y (Map.sel ss.m y) ] in
    ss_term t (tail ss)

let rec ss_st_term (t:st_term) (ss:ss_t) : Tot st_term (decreases L.length ss.l) =
  match ss.l with
  | [] -> t
  | y::tl ->
    let t = subst_st_term t [ NT y (Map.sel ss.m y) ] in
    ss_st_term t (tail ss)

let rec ss_st_comp (s:st_comp) (ss:ss_t)
  : Tot st_comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> s
  | y::tl ->
    let s = subst_st_comp s [ NT y (Map.sel ss.m y) ] in
    ss_st_comp s (tail ss)

let rec ss_comp (c:comp) (ss:ss_t)
  : Tot comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> c
  | y::tl ->
    let c = subst_comp c [ NT y (Map.sel ss.m y) ] in
    ss_comp c (tail ss)

let rec ss_binder (b:binder) (ss:ss_t)
  : Tot binder (decreases L.length ss.l) =
  match ss.l with
  | [] -> b
  | y::tl ->
    let b = subst_binder b [ NT y (Map.sel ss.m y) ] in
    ss_binder b (tail ss)

let rec ss_env (g:env) (ss:ss_t)
  : Tot (g':env { fstar_env g' == fstar_env g /\
                  Env.dom g' == Env.dom g })
        (decreases L.length ss.l) =
  admit ();
  match ss.l with
  | [] -> g
  | y::tl -> ss_env (subst_env g [ NT y (Map.sel ss.m y) ]) (tail ss)

let rec ss_st_comp_commutes (s:st_comp) (ss:ss_t)
  : Lemma (ensures
             ss_st_comp s ss ==
             { s with res = ss_term s.res ss;
                      pre = ss_term s.pre ss;
                      post = ss_term s.post ss; })  // no shifting required
          (decreases L.length ss.l)
          [SMTPat (ss_st_comp s ss)] =
  match ss.l with
  | [] -> ()
  | y::tl -> ss_st_comp_commutes (subst_st_comp s [ NT y (Map.sel ss.m y) ]) (tail ss)

let rec ss_comp_commutes (c:comp) (ss:ss_t)
  : Lemma (ensures
             (let r = ss_comp c ss in
              (C_Tot? c ==> r == C_Tot (ss_term (comp_res c) ss)) /\
              (C_ST? c ==> r == C_ST (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STAtomic? c ==> r == C_STAtomic (ss_term (comp_inames c) ss)
                                                 (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STGhost? c ==> r == C_STGhost (ss_term (comp_inames c) ss)
                                               (ss_st_comp (st_comp_of_comp c) ss))))
          (decreases L.length ss.l)
          [SMTPat (ss_comp c ss)] =
  match ss.l with
  | [] -> ()
  | y::tl -> ss_comp_commutes (subst_comp c [ NT y (Map.sel ss.m y) ]) (tail ss)

let rec is_permutation (nts:nt_substs) (ss:ss_t) : Type0 =
  match nts, ss.l with
  | [], [] -> True
  | (NT x e)::nts_rest, _::_ ->
    Map.contains ss.m x /\
    Map.sel ss.m x == e /\
    is_permutation nts_rest ({l=remove_l ss.l x; m=remove_map ss.m x})
  | _ -> False

let rec ss_to_nt_substs (g:env) (uvs:env) (ss:ss_t)
  : T.Tac (option (nts:nt_substs { well_typed_nt_substs g uvs nts /\
                                   is_permutation nts ss })) =
  
  match bindings uvs with
  | [] ->
    (match ss.l with
     | [] -> Some []
     | _ -> None)
  | _ ->
    let x, ty, rest_uvs = remove_binding uvs in
    if Map.contains ss.m x
    then let t = Map.sel ss.m x in
         let d : tot_typing g t ty = magic () in
         let _ = FStar.Squash.return_squash d in
         let nts_opt =
           ss_to_nt_substs g (subst_env rest_uvs [ NT x t ]) {l=remove_l ss.l x;
                                                              m=remove_map ss.m x} in
         match nts_opt with
         | None -> None
         | Some nts ->
           let nts : nts:nt_substs { well_typed_nt_substs g uvs nts } = (NT x t)::nts in
           Some nts
    else None

let ss_nt_subst (g:env) (uvs:env) (ss:ss_t) (nts:nt_substs)
  : Lemma (requires disjoint uvs g /\ well_typed_nt_substs g uvs nts /\ is_permutation nts ss)
          (ensures
             (forall (t:term). nt_subst_term t nts == ss_term t ss) /\
             (forall (b:binder). nt_subst_binder b nts == ss_binder b ss) /\
             (forall (t:st_term). nt_subst_st_term t nts == ss_st_term t ss) /\
             (forall (c:comp). nt_subst_comp c nts == ss_comp c ss) /\
             (forall (s:st_comp). nt_subst_st_comp s nts == ss_st_comp s ss)) = admit ()

let rec st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (nts:nt_substs { well_typed_nt_substs g uvs nts })
  : Tot (st_typing (push_env g (nt_subst_env g' nts)) (nt_subst_st_term t nts) (nt_subst_comp c nts))
        (decreases L.length nts) =

  match bindings uvs with
  | [] ->
    assert (equal (push_env uvs g') g');
    t_typing
  | _ ->
    let x, ty, uvs_rest = remove_binding uvs in
    let (NT _ e)::nts_rest = nts in
    let e_typing : tot_typing g e ty = FStar.IndefiniteDescription.elim_squash () in
    push_env_assoc (singleton_env (fstar_env uvs) x ty) uvs_rest g';
    let t_typing
      : st_typing (push_env g (push_env (singleton_env (fstar_env g) x ty) (push_env uvs_rest g'))) t c
      = coerce_eq t_typing () in
    let t_typing
      : st_typing (push_env g (subst_env (push_env uvs_rest g') [ NT x e ]))
                  (subst_st_term t [ NT x e ])
                  (subst_comp c [ NT x e ])
      = st_typing_subst g x ty (push_env uvs_rest g') e_typing t_typing in

    assume (subst_env (push_env uvs_rest g') [ NT x e ] ==
            push_env (subst_env uvs_rest [ NT x e ]) (subst_env g' [ NT x e ]));

    st_typing_nt_substs g
      (subst_env uvs_rest [ NT x e ])
      (subst_env g' [ NT x e ])
      t_typing nts_rest
   

// let well_typed_nt_substs 

// let permutation #uvs (ss1 ss2:ss_t uvs) =
//   Map.equal ss1.m ss2.m

// let rec ss_term_permutation #uvs (t:term) (ss1 ss2:ss_t uvs)
//   : Lemma (requires permutation ss1 ss2)
//           (ensures ) 

// let rec nt_subst_st_comp_commutes (s:st_comp) (ss:nt_substs)
//   : Lemma (ensures nt_subst_st_comp s ss ==
//            { s with res = nt_subst_term s.res ss;
//                     pre = nt_subst_term s.pre ss;
//                     post = nt_subst_term s.post ss; })
//           (decreases L.length ss) =
//   match ss with
//   | [] -> ()
//   | (NT x e)::tl ->
//     nt_subst_st_comp_commutes (subst_st_comp s [ NT x e ]) tl


// let rec nt_subst_comp_commutes (c:comp) (ss:nt_substs)
//   : Lemma (ensures (let r = nt_subst_comp c ss in
//            (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) ss)) /\
//            (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
//            (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) ss)
//                                               (nt_subst_st_comp (st_comp_of_comp c) ss)) /\
//            (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) ss)
//                                             (nt_subst_st_comp (st_comp_of_comp c) ss))))
//           (decreases L.length ss) =
  
//   match ss with
//   | [] -> ()
//   | (NT x e)::tl ->
//     nt_subst_comp_commutes (subst_comp c [ NT x e ]) tl

// let rec nt_subst_term_compose (t:term) (ss1 ss2:nt_substs)
// : Lemma (ensures nt_subst_term (nt_subst_term t ss1) ss2 ==
//                  nt_subst_term t (compose_nt_substs ss1 ss2))
//         (decreases L.length ss1) =

// match ss1 with
// | [] -> ()
// | (NT x e)::tl -> nt_subst_term_compose (subst_term t [ NT x e ]) tl ss2

// let rec nt_subst_st_term_compose (t:st_term) (ss1 ss2:nt_substs)
// : Lemma (ensures nt_subst_st_term (nt_subst_st_term t ss1) ss2 ==
//                  nt_subst_st_term t (compose_nt_substs ss1 ss2))
//         (decreases L.length ss1) =

// match ss1 with
// | [] -> ()
// | (NT x e)::tl -> nt_subst_st_term_compose (subst_st_term t [ NT x e ]) tl ss2

// let rec nt_subst_comp_compose (c:comp) (ss1 ss2:nt_substs)
// : Lemma (ensures nt_subst_comp (nt_subst_comp c ss1) ss2 ==
//                  nt_subst_comp c (compose_nt_substs ss1 ss2))
//         (decreases L.length ss1) =

// match ss1 with
// | [] -> ()
// | (NT x e)::tl -> nt_subst_comp_compose (subst_comp c [ NT x e ]) tl ss2

// let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b{y == x} = x

// let rec st_typing_nt_substs
//   (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
//   (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
//   (ss:nt_substs { well_typed_ss g uvs ss })
// : Tot (st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss))
//       (decreases L.length ss) =

// match bindings uvs with
// | [] ->
//   assert (equal (push_env uvs g') g');
//   t_typing

// | _ ->
//   let x, ty, uvs' = remove_binding uvs in
//   let (NT y e)::ss' = ss in
//   let e_typing = FStar.IndefiniteDescription.elim_squash #(tot_typing g e ty) () in
//   push_env_assoc (singleton_env (fstar_env uvs) x ty) uvs' g';
//   let t_typing
//     : st_typing (push_env g (push_env (singleton_env (fstar_env g) x ty) (push_env uvs' g'))) t c
//     = coerce_eq t_typing () in
//   let t_typing
//     : st_typing (push_env g (subst_env (push_env uvs' g') [ NT y e ]))
//                 (subst_st_term t [ NT y e ])
//                 (subst_comp c [ NT y e ])
//     = st_typing_subst g x ty (push_env uvs' g') e_typing t_typing in

//   assume (subst_env (push_env uvs' g') [ NT y e ] ==
//           push_env (subst_env uvs' [ NT y e ]) (subst_env g' [ NT y e ]));

//   st_typing_nt_substs g
//     (subst_env uvs' [ NT y e ])
//     (subst_env g' [ NT y e ])
//     t_typing ss'

// let vprop_equiv_nt_substs
//   (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
//   (#p1 #p2:vprop) (veq:vprop_equiv (push_env g (push_env uvs g')) p1 p2)
//   (ss:nt_substs { well_typed_ss g uvs ss })
// : vprop_equiv (push_env g (nt_subst_env g' ss)) (nt_subst_term p1 ss) (nt_subst_term p2 ss) =

// admit ()

let vprop_equiv_nt_substs_derived _ _ _ _ = admit ()


// type map = m:Map.t var term {
//   forall (x:var). (~ (Map.contains m x)) ==> Map.sel m x == tm_unknown
// }

// let related (l:list (var & term)) (m:map) =
//   (forall (b:var & term).
//           L.memP b l ==> (Map.contains m (fst b) /\
//                           Map.sel m (fst b) == snd b)) /\
  
//   (forall (x:var). Map.contains m x ==> L.memP (x, Map.sel m x) l)

// noeq
// type t = {
//   l : list (var & term);
//   m : m:map { related l m }
// }

// let rec as_nt_substs_aux (l:list (var & term)) : nt_substs =
//   match l with
//   | [] -> []
//   | (x, t)::tl -> (NT x t)::(as_nt_substs_aux tl)

// let as_nt_substs s = as_nt_substs_aux s.l

// let as_map s = s.m

// let empty = {
//   l = [];
//   m = Map.const_on Set.empty tm_unknown;
// }

// let empty_dom () = assert (Set.equal (dom empty) Set.empty)

// let singleton (x:var) (t:term) = {
//   l = [ (x, t) ];
//   m = Map.upd (Map.const_on Set.empty tm_unknown) x t;
// }

// //
// // TODO: Move to ulib
// //
// let rec append_memP (#a:Type) (l1 l2:list a) (x:a)
//   : Lemma (L.memP x (l1 @ l2) <==> (L.memP x l1 \/ L.memP x l2))
//           [SMTPat (L.memP x (l1 @ l2))] =
//   match l1 with
//   | [] -> ()
//   | _::tl -> append_memP tl l2 x

// let push s1 s2 = {
//   l = s1.l @ s2.l;
//   m = Map.concat s1.m s2.m;
// }

// let push_as_map _ _ = ()

// let check_well_typedness g uvs ss = admit (); true

// // let t _ = magic ()
// // let as_subst _ = magic ()
// // let as_map _ = magic ()
// // let subst_as_map _ = admit ()
// // let equal_elim _ _ = admit ()
// // let empty _ = magic ()
// // let empty_dom _ = admit ()
// // let singleton _ = magic ()
// // let singleton_dom _ _ = admit ()
// // let push _ _ = magic ()
// // let push_substs_as_map _ _ = admit ()
// // let push_subst_term _ _ _ = admit ()
// // let push_subst_st_term _ _ _ = admit ()
// // let push_subst_comp _ _ _ = admit ()
// // let subst_closed_term _ _ = admit ()
// // let subst_closed_st_term _ _ = admit ()
// // let subst_closed_comp _ _ = admit ()
// // let diff _ _ = magic ()
// // let diff_push _ _ = admit ()
