module SCC

open FStar.Fin
open FStar.Ghost
open FStar.Map
module S = FStar.Seq
module L = FStar.List.Tot
module OS = FStar.OrdSet
module OM = FStar.OrdMap

type vertex (n:nat) = fin n
type vset (n:nat) = OS.ordset (vertex n) (fin_cmp n)
type vmap (n:nat) (a:eqtype) = OM.ordmap (vertex n) a (fin_cmp n)

type graph (n:nat) = s:S.seq (vset n){S.length s == n}

noeq
type scc_env (n:nat) = {
  blacks : erased (vset n) ;
  grays : erased (vset n) ;
  stack : list (vertex n) ;
  sccs : OS.ordset (vset n) (OS.ordset_cmp (fin_cmp n)) ;
  sn : nat ;
  num : vmap n (option nat)
}


let rec split' (#a:eqtype) acc (l:list a) (x:a) : Tot (list a * list a) (decreases l)=
  match l with
  | [] -> L.rev acc, []
  | y :: ys -> if y = x then L.rev (y::acc), ys else split' (y::acc) ys x

let split (#a:eqtype) (l:list a) (x:a) = split' [] l x

let opt_nat_lt (p1 p2:option nat) =
  match p1, p2 with
  | None, _ -> false
  | _, None -> true
  | Some n1, Some n2 -> n1 < n2

let opt_nat_min p1 p2 = if p1 `opt_nat_lt` p2 then p1 else p2

let vertices (#n:nat) (g:graph n) : vset n =
  if n = 0 then OS.empty else OS.from_list (range 0 (n-1 <: fin n))


let rec dfs1 (#n:nat) (g:graph n) (x:vertex n) (e:scc_env n)
  : Dv (option nat * scc_env n)
= let n = e.sn in
  let n1, e1 =
    dfs' g (S.index g x) ({e with grays = elift1 (fun s -> OS.add_elt s x) e.grays ; sn = n + 1 ; stack = x::e.stack})
  in
  if n1 `opt_nat_lt` Some n then
    n1, {e1 with blacks = elift1 (fun s -> OS.add_elt s x) e1.blacks ; grays = elift1 (OS.remove x) e1.grays}
  else
    let s2, s3 = split e.stack x in
    None, {e1 with
      blacks = elift1 (fun s -> OS.add_elt s x) e1.blacks ;
      stack = s3 ;
      sccs = OS.add_elt e1.sccs (OS.from_list s2) ;
      num = L.fold_left (fun m x -> OM.update x None m) e1.num s2
      }

and dfs' (#n:nat) (g:graph n) (roots:vset n) (e:scc_env n)
  : Dv (option nat * scc_env n)
= if roots = OS.empty then
     None, e
  else
    let x = Some?.v (OS.choose roots) in
    let n1, e1 = if OM.contains x e.num then Some?.v (OM.select x e.num), e else dfs1 g x e in
    let n2, e2 = dfs' g (OS.remove x roots) e1 in
    opt_nat_min n1 n2, e2

let tarjan (#n:nat) (g:graph n) =
  let e0 = {blacks = hide OS.empty ; grays = hide OS.empty; stack = Nil; sccs = OS.empty; sn = 0; num = OM.empty} in
  (snd (dfs' g (vertices g) e0)).sccs

assume val cardinal_vset_n : n:nat -> Lemma (forall (v:vset n). OS.cardinal v < n+1)

let dom_card (#n:nat) (#a:eqtype) (num:vmap n a) : fin (n + 1) = cardinal_vset_n n ; OS.cardinal (OM.dom num)

assume val cardinal_not_mem (#a:eqtype) (#n:nat) (num:vmap n a) (x:fin n)
  : Lemma
    (requires not (OS.mem x (OM.dom num)))
    (ensures (forall v. dom_card (OM.update x v num) == 1 + dom_card num))

assume val cardinal_remove (#n:nat) (x:fin n) (s:vset n) : Lemma (s =!= OS.empty ==> OS.cardinal (OS.remove x s) = OS.cardinal s - 1)

assume val update_preserves_dom_card (#n:nat) (#a:eqtype) : Lemma (forall (num:vmap n a) (x:_) (v:_). dom_card num <= dom_card (OM.update x v num))

let inv (#n:nat) (k:nat) : Lemma (forall (m:vmap n (option nat)) x. k <= dom_card m ==> k <= dom_card (OM.update x None m))
= update_preserves_dom_card #n #(option nat)

(* let f (#n:nat) (m:vmap n (option nat)) x = OM.update x None m *)
(* let inv (#n:nat) l : Lemma (forall (m:vmap n (option nat)) x. k <= dom_card m ==> k <= dom_card (OM.update x None m)) *)
(*     = let aux (m:vmap n (option nat)) (x:fin n) : Lemma (dom_card m <= dom_card (OM.update x None m)) = update_preserves_dom_card #n #(option nat) m x None in *)
(*     FStar.Classical.forall_intro_2 aux *)

#set-options "--print_implicits --print_universes --prn"

let rec dfs1_pure (#n:nat) (g:graph n) (x:vertex n) (e:scc_env n)
  : Pure (option nat * scc_env n)
    (requires not (OS.mem x (OM.dom e.num)))
    (ensures (fun (n,e') -> dom_card e.num <= dom_card e'.num))
    (decreases %[n - dom_card e.num ; 0])
= let n1, e1 =
      let e0 = {e with
        grays = elift1 (fun s -> OS.add_elt s x) e.grays ;
        sn = e.sn + 1 ;
        stack = x::e.stack ;
        num = OM.update x (Some n) e.num
      } in
    cardinal_not_mem e.num x;
  assert (dom_card e.num <= dom_card e0.num) ;
    dfs'_pure g (S.index g x) e0
  in
  assert (dom_card e.num <= dom_card e1.num) ;
  if n1 `opt_nat_lt` Some n then
    n1, {e1 with blacks = elift1 (fun s -> OS.add_elt s x) e1.blacks ; grays = elift1 (OS.remove x) e1.grays}
  else
    let s2, s3 = split e.stack x in
    let num = L.fold_left (fun m x -> OM.update x None m) e1.num s2 in
    update_preserves_dom_card #n #(option nat) ;
    L.fold_left_invar (fun m (x:vertex n) -> OM.update x None m) s2 (fun (m:vmap n (option nat)) -> dom_card e.num <= dom_card m) ;
    None, {e1 with
      blacks = elift1 (fun s -> OS.add_elt s x) e1.blacks ;
      stack = s3 ;
      sccs = OS.add_elt e1.sccs (OS.from_list s2) ;
      num = num
      }

and dfs'_pure (#n:nat) (g:graph n) (roots:vset n) (e:scc_env n)
  : Pure (option nat * scc_env n)
    (requires True)
    (ensures (fun (n, e') -> dom_card e.num <= dom_card e'.num))
    (decreases %[n - dom_card e.num; 1 ; OS.cardinal roots])
= if roots = OS.empty then
     None, e
  else
    let x = Some?.v (OS.choose roots) in
    let n1, e1 = if OM.contains x e.num then Some?.v (OM.select x e.num), e else dfs1_pure g x e in
    assert (dom_card e.num <= dom_card e1.num) ;
    cardinal_remove x roots ;
    let n2, e2 = dfs'_pure g (OS.remove x roots) e1 in
    opt_nat_min n1 n2, e2

let tarjan_pure (#n:nat) (g:graph n) =
  let e0 = {blacks = hide OS.empty ; grays = hide OS.empty; stack = Nil; sccs = OS.empty; sn = 0; num = OM.empty} in
  (snd (dfs'_pure g (vertices g) e0)).sccs

let processing_size (#n:nat) (e:scc_env n) : GTot (fin (n+1)) =
  cardinal_vset_n n;
  OS.cardinal (reveal e.blacks `OS.union` reveal e.grays)
