(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Checker.Pure

module L = FStar.List.Tot

module Env = Pulse.Typing.Env
module Metatheory = Pulse.Typing.Metatheory

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

let rec separate_map (sep:document)
   (f : 'a -> T.Tac document)
   (xs : list 'a)
   : T.Tac document =
  match xs with
  | [] -> empty
  | [x] -> f x
  | x::xs ->
    let doc = f x in
    let docs = separate_map sep f xs in
    doc ^^ sep ^^ docs

instance pp_ss_t : printable ss_t = {
  pp = (function {l;m} ->
        //  doc_of_string "dom="
        //  pp (l <: list int) ^^
        //  doc_of_string " |-> " ^^
        l |> separate_map (comma ^^ break_ 1) (fun k ->
               pp (k <: int) ^^ doc_of_string " -> " ^^ pp (Map.sel m k))
          |> brackets
        );
}
instance showable_ss_t : tac_showable ss_t = show_from_pp

let ln_ss_t (s:ss_t) =
  List.Tot.for_all (fun x -> ln (Map.sel s.m x)) s.l

let as_map (ss:ss_t) = ss.m

let empty = { l = []; m = Map.const_on Set.empty tm_unknown }

let is_dom_push
  (l:ss_dom)
  (m:ss_map { is_dom l m })
  (x:var { ~ (Map.contains m x ) })
  (t:term)
  : Lemma (is_dom (x::l) (Map.upd m x t)) =

  assert (Map.equal (remove_map (Map.upd m x t) x) m)

let lemma_dom_empty () = ()

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

let check_disjoint ss1 ss2 =
  admit ();
  not (L.existsb (fun v1 -> L.mem v1 ss2.l) ss1.l)

let rec diff_aux (ss1 ss2:ss_t) (acc:ss_t { Set.disjoint (dom acc) (dom ss2) })
  : Tot (ss:ss_t { Set.disjoint (dom ss) (dom ss2) }) (decreases L.length ss1.l) =
  match ss1.l with
  | [] -> acc
  | x::l ->
    if L.mem x ss2.l
    then let ss1 = { ss1 with l; m = remove_map ss1.m x } in
         diff_aux ss1 ss2 acc
    else let acc_l = x::acc.l in
         let acc_m = Map.upd acc.m x (Map.sel ss1.m x) in
         assume (no_repeats acc_l /\ is_dom acc_l acc_m);
         let acc = { l = acc_l; m = acc_m } in
         let ss1 = { ss1 with l; m = remove_map ss1.m x } in
         diff_aux ss1 ss2 acc

let diff ss1 ss2 = diff_aux ss1 ss2 empty

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
    let t = subst_term t [ RT.NT y (Map.sel ss.m y) ] in
    ss_term t (tail ss)

let rec ss_st_term (t:st_term) (ss:ss_t) : Tot st_term (decreases L.length ss.l) =
  match ss.l with
  | [] -> t
  | y::tl ->
    let t = subst_st_term t [ RT.NT y (Map.sel ss.m y) ] in
    ss_st_term t (tail ss)

let rec ss_st_comp (s:st_comp) (ss:ss_t)
  : Tot st_comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> s
  | y::tl ->
    let s = subst_st_comp s [ RT.NT y (Map.sel ss.m y) ] in
    ss_st_comp s (tail ss)

let rec ss_comp (c:comp) (ss:ss_t)
  : Tot comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> c
  | y::tl ->
    let c = subst_comp c [ RT.NT y (Map.sel ss.m y) ] in
    ss_comp c (tail ss)

let rec ss_binder (b:binder) (ss:ss_t)
  : Tot binder (decreases L.length ss.l) =
  match ss.l with
  | [] -> b
  | y::tl ->
    let b = subst_binder b [ RT.NT y (Map.sel ss.m y) ] in
    ss_binder b (tail ss)

let lemma_subst_empty_term (t:term)
  : Lemma (ss_term t empty == t)
  = ()

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
  | y::tl -> ss_st_comp_commutes (subst_st_comp s [ RT.NT y (Map.sel ss.m y) ]) (tail ss)

let rec ss_comp_commutes (c:comp) (ss:ss_t)
  : Lemma (ensures
             (let r = ss_comp c ss in
              (C_Tot? c ==> r == C_Tot (ss_term (comp_res c) ss)) /\
              (C_ST? c ==> r == C_ST (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STAtomic? c ==> r == C_STAtomic (ss_term (comp_inames c) ss)
                                                 (C_STAtomic?.obs c)
                                                 (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STGhost? c ==> r == C_STGhost (ss_term (comp_inames c) ss)
                                               (ss_st_comp (st_comp_of_comp c) ss))))
          (decreases L.length ss.l)
          [SMTPat (ss_comp c ss)] =
  match ss.l with
  | [] -> ()
  | y::tl -> ss_comp_commutes (subst_comp c [ RT.NT y (Map.sel ss.m y) ]) (tail ss)
