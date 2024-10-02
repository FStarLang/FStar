(*
   Copyright 2008-2023 Microsoft Research

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

module FStar.Reflection.Typing

(** This module defines a typing judgment for (parts of) the total
    fragment of F*. We are using it in the meta DSL framework as an
    official specification for the F* type system.

    We expect it to grow to cover more of the F* language.

    IT IS HIGHLY EXPERIMENTAL AND NOT YET READY TO USE.
  *)

open FStar.List.Tot
open FStar.Reflection.V2

module R = FStar.Reflection.V2
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
module RTB = FStar.Reflection.Typing.Builtins

let inspect_pack = R.inspect_pack_inv
let pack_inspect = R.pack_inspect_inv
  
let inspect_pack_namedv = R.inspect_pack_namedv
let pack_inspect_namedv = R.pack_inspect_namedv

let inspect_pack_bv = R.inspect_pack_bv
let pack_inspect_bv = R.pack_inspect_bv

let inspect_pack_binder = R.inspect_pack_binder
let pack_inspect_binder = R.pack_inspect_binder

let inspect_pack_comp = R.inspect_pack_comp_inv
let pack_inspect_comp = R.pack_inspect_comp_inv

let inspect_pack_fv = R.inspect_pack_fv
let pack_inspect_fv = R.pack_inspect_fv

let inspect_pack_universe = R.inspect_pack_universe
let pack_inspect_universe = R.pack_inspect_universe

let inspect_pack_lb = R.inspect_pack_lb
let pack_inspect_lb = R.pack_inspect_lb

let inspect_pack_sigelt = R.inspect_pack_sigelt
let pack_inspect_sigelt = R.pack_inspect_sigelt

let lookup_bvar (e:env) (x:int) : option term = magic ()

let lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe)
  : option R.term = magic ()

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term) = admit ()

let lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term) = admit ()

let subst_ctx_uvar_and_subst _ _ = magic ()

let open_with (t:term) (v:term) = RTB.open_with t v
  
let open_with_spec (t v:term) = admit ()

let open_term (t:term) (v:var) = RTB.open_term t v

let open_term_spec (t:term) (v:var) = admit ()
  
let close_term (t:term) (v:var) = RTB.close_term t v

let close_term_spec (t:term) (v:var) = admit ()

let rename (t:term) (x y:var)= RTB.rename t x y

let rename_spec (t:term) (x y:var) = admit ()
  
let bv_index_of_make_bv (n:nat) = ()
let namedv_uniq_of_make_namedv (n:nat) = ()

let bindings_ok_for_pat bnds pat = magic ()
let bindings_ok_pat_constant c = admit ()

let subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1) = magic ()

let subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                              (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1) = magic ()

let well_typed_terms_are_ln _ _ _ _ = admit ()

let type_correctness _ _ _ _ = admit ()

let rec binder_offset_pattern_invariant (p:pattern) (ss:subst)
  : Lemma (ensures binder_offset_pattern p ==
                   binder_offset_pattern (subst_pattern p ss))
          (decreases p)
  = match p with
    | Pat_Cons _ _ pats ->
      binder_offset_patterns_invariant pats ss
    | _ -> ()

and binder_offset_patterns_invariant (p:list (pattern & bool)) (ss:subst)
  : Lemma (ensures binder_offset_patterns p ==
                   binder_offset_patterns (subst_patterns p ss))
          (decreases p)
  = match p with
    | [] -> ()
    | (hd, _)::tl ->
      binder_offset_pattern_invariant hd ss;
      let n = binder_offset_pattern hd in
      binder_offset_patterns_invariant tl (shift_subst_n n ss)

let rec open_close_inverse' (i:nat) (t:term { ln' t (i - 1) }) (x:var)
  : Lemma
         (ensures subst_term 
                  (subst_term t [ ND x i ])
                  (open_with_var x i)
                == t)
       (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unsupp
    | Tv_Unknown
    | Tv_BVar _ -> ()
    | Tv_Var _  -> ()
    | Tv_App t1 a ->
      open_close_inverse' i t1 x;
      open_close_inverse' i (fst a) x
     
     | Tv_Abs b body -> 
      open_close_inverse'_binder i b x;
      open_close_inverse' (i + 1) body x

    | Tv_Arrow b c ->
      open_close_inverse'_binder i b x;
      open_close_inverse'_comp (i + 1) c x

    | Tv_Refine b f ->
      open_close_inverse'_binder i b x;
      open_close_inverse' (i + 1) f x
      
    | Tv_Let recf attrs b def body ->
      open_close_inverse'_terms i attrs x;
      open_close_inverse'_binder i b x;
      (if recf 
      then open_close_inverse' (i + 1) def x
      else open_close_inverse' i def x);
      open_close_inverse' (i + 1) body x

    | Tv_Match scr ret brs ->
      open_close_inverse' i scr x;
      (match ret with
       | None -> ()
       | Some m -> open_close_inverse'_match_returns i m x);
      open_close_inverse'_branches i brs x
      
    | Tv_AscribedT e t tac b ->
      open_close_inverse' i e x;
      open_close_inverse' i t x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse' i tac x)

    | Tv_AscribedC e c tac b ->
      open_close_inverse' i e x;
      open_close_inverse'_comp i c x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse' i tac x)
    

and open_close_inverse'_binder (i:nat) (b:binder { ln'_binder b (i - 1) }) (x:var)
  : Lemma (ensures subst_binder
                     (subst_binder b [ ND x i ])
                     (open_with_var x i)
                   == b)
          (decreases b)                   
  = let bndr  = inspect_binder b in
    let {ppname; qual=q; attrs=attrs; sort=sort} = bndr in
    open_close_inverse' i sort x;
    open_close_inverse'_terms i attrs x;
    assert (subst_terms (subst_terms attrs [ ND x i ])
                        (open_with_var x i) == attrs);    
    pack_inspect_binder b;    
    assert (pack_binder {ppname; qual=q; attrs=attrs; sort=sort} == b)

and open_close_inverse'_terms (i:nat) (ts:list term { ln'_terms ts (i - 1) }) (x:var)
  : Lemma (ensures subst_terms
                     (subst_terms ts [ ND x i ])
                     (open_with_var x i)
                   == ts)
          (decreases ts)                   
  = match ts with
    | [] -> ()
    | t::ts -> 
      open_close_inverse' i t x;
      open_close_inverse'_terms i ts x

and open_close_inverse'_comp (i:nat) (c:comp { ln'_comp c (i - 1) }) (x:var)
  : Lemma 
    (ensures subst_comp
               (subst_comp c [ ND x i ])
               (open_with_var x i)
             == c)
    (decreases c)
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t -> open_close_inverse' i t x

    | C_Lemma pre post pats ->
      open_close_inverse' i pre x;
      open_close_inverse' i post x;
      open_close_inverse' i pats x

    | C_Eff us eff_name res args decrs ->
      open_close_inverse' i res x;
      open_close_inverse'_args i args x;
      open_close_inverse'_terms i decrs x          

and open_close_inverse'_args (i:nat) 
                            (ts:list argv { ln'_args ts (i - 1) })
                            (x:var)
  : Lemma
    (ensures subst_args
               (subst_args ts [ ND x i ])
               (open_with_var x i)
             == ts)
    (decreases ts)
  = match ts with
    | [] -> ()
    | (t,q)::ts -> 
      open_close_inverse' i t x;
      open_close_inverse'_args i ts x

and open_close_inverse'_patterns (i:nat)
                                (ps:list (pattern & bool) { ln'_patterns ps (i - 1) })
                                (x:var)
  : Lemma 
    (ensures subst_patterns
               (subst_patterns ps [ ND x i ])
               (open_with_var x i)
             == ps)
    (decreases ps)
  = match ps with
    | [] -> ()
    | (p, b)::ps' ->
      open_close_inverse'_pattern i p x;
      let n = binder_offset_pattern p in
      binder_offset_pattern_invariant p [ ND x i ];
      open_close_inverse'_patterns (i + n) ps' x

and open_close_inverse'_pattern (i:nat) (p:pattern{ln'_pattern p (i - 1)}) (x:var)
  : Lemma 
    (ensures subst_pattern
               (subst_pattern p [ ND x i ])
               (open_with_var x i)
             == p)
    (decreases p)
  = match p with
    | Pat_Constant _ -> ()

    | Pat_Cons fv us pats -> 
      open_close_inverse'_patterns i pats x
      
    | Pat_Var bv _ -> ()

    | Pat_Dot_Term topt ->
      match topt with
      | None -> ()
      | Some t -> open_close_inverse' i t x

    
and open_close_inverse'_branch (i:nat) (br:branch{ln'_branch br (i - 1)}) (x:var)
 : Lemma
    (ensures subst_branch
               (subst_branch br [ ND x i ])
               (open_with_var x i)
             == br)
    (decreases br)  
  = let p, t = br in
    let j = binder_offset_pattern p in
    binder_offset_pattern_invariant p [ ND x i ];
    open_close_inverse'_pattern i p x;
    open_close_inverse' (i + j) t x
  
and open_close_inverse'_branches (i:nat)
                                (brs:list branch { ln'_branches brs (i - 1) })
                                (x:var)
  : Lemma
    (ensures subst_branches
               (subst_branches brs [ ND x i ])
               (open_with_var x i)
             == brs)
    (decreases brs)
  = match brs with
    | [] -> ()
    | br::brs -> 
      open_close_inverse'_branch i br x;
      open_close_inverse'_branches i brs x
  
and open_close_inverse'_match_returns (i:nat) 
                                     (m:match_returns_ascription { ln'_match_returns m (i - 1) })
                                     (x:var)
  : Lemma 
    (ensures subst_match_returns
               (subst_match_returns m [ ND x i ])
               (open_with_var x i)
             == m)
    (decreases m)
  = let b, (ret, as_, eq) = m in
    open_close_inverse'_binder i b x;
    let ret =
      match ret with
      | Inl t ->
        open_close_inverse' (i + 1) t x
      | Inr c ->
        open_close_inverse'_comp (i + 1) c x
    in
    let as_ =
      match as_ with
      | None -> ()
      | Some t ->
        open_close_inverse' (i + 1) t x
    in
    ()

let open_close_inverse (e:R.term { ln e }) (x:var)
  : Lemma (open_term (close_term e x) x == e)
   = close_term_spec e x;
     open_term_spec (close_term e x) x;
     open_close_inverse' 0 e x

let rec close_open_inverse' (i:nat)
                            (t:term) 
                            (x:var { ~(x `Set.mem` freevars t) })
  : Lemma 
       (ensures subst_term 
                  (subst_term t (open_with_var x i))
                  [ ND x i ]
                == t)
       (decreases t)
  = match inspect_ln t with
    | Tv_Uvar _ _ -> assert false
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unsupp
    | Tv_Unknown -> ()
    | Tv_BVar _ -> ()
    | Tv_Var _ -> ()
    | Tv_App t1 a ->
      close_open_inverse' i t1 x;
      close_open_inverse' i (fst a) x
      
    | Tv_Abs b body -> 
      close_open_inverse'_binder i b x;
      close_open_inverse' (i + 1) body x

    | Tv_Arrow b c ->
      close_open_inverse'_binder i b x;
      close_open_inverse'_comp (i + 1) c x

    | Tv_Refine b f ->
      close_open_inverse'_binder i b x;
      close_open_inverse' (i + 1) f x
      
    | Tv_Let recf attrs b def body ->
      close_open_inverse'_terms i attrs x;
      close_open_inverse'_binder i b x;
      close_open_inverse' (if recf then (i + 1) else i) def x;
      close_open_inverse' (i + 1) body x

    | Tv_Match scr ret brs ->
      close_open_inverse' i scr x;
      (match ret with
       | None -> ()
       | Some m -> close_open_inverse'_match_returns i m x);
      close_open_inverse'_branches i brs x

    | Tv_AscribedT e t tac b ->
      close_open_inverse' i e x;
      close_open_inverse' i t x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse' i t x)

    | Tv_AscribedC e c tac b ->
      close_open_inverse' i e x;
      close_open_inverse'_comp i c x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse' i t x)
      
and close_open_inverse'_comp (i:nat)
                             (c:comp)
                             (x:var{ ~(x `Set.mem` freevars_comp c) })
  : Lemma
       (ensures subst_comp 
                  (subst_comp c (open_with_var x i))
                  [ ND x i ]
                == c)
       (decreases c)
   = match inspect_comp c with
    | C_Total t 
    | C_GTotal t ->    
      close_open_inverse' i t x

    | C_Lemma pre post pats ->
      close_open_inverse' i pre x;
      close_open_inverse' i post x;
      close_open_inverse' i pats x

    | C_Eff us eff_name res args decrs ->
      close_open_inverse' i res x;
      close_open_inverse'_args i args x;
      close_open_inverse'_terms i decrs x

and close_open_inverse'_args (i:nat) (args:list argv) (x:var{ ~(x `Set.mem` freevars_args args) })
  : Lemma
       (ensures subst_args 
                  (subst_args args (open_with_var x i))
                  [ ND x i]
                == args)
       (decreases args)
  = match args with
    | [] -> ()
    | (a, q) :: args ->
      close_open_inverse' i a x;
      close_open_inverse'_args i args x

and close_open_inverse'_binder (i:nat) (b:binder) (x:var{ ~(x `Set.mem` freevars_binder b) })
  : Lemma 
       (ensures subst_binder 
                  (subst_binder b (open_with_var x i))
                  [ ND x i ]
                == b)
       (decreases b)
  = let bndr  = inspect_binder b in
    close_open_inverse' i bndr.sort x;
    close_open_inverse'_terms i bndr.attrs x;
    pack_inspect_binder b

and close_open_inverse'_terms (i:nat) (ts:list term) (x:var{ ~(x `Set.mem` freevars_terms ts) })
  : Lemma 
       (ensures subst_terms 
                  (subst_terms ts (open_with_var x i))
                  [ ND x i ]
                == ts)
       (decreases ts)
  = match ts with
    | [] -> ()
    | hd :: tl ->
      close_open_inverse' i hd x;
      close_open_inverse'_terms i tl x

and close_open_inverse'_branches (i:nat) (brs:list branch) 
                                 (x:var{ ~(x `Set.mem` freevars_branches brs) })
  : Lemma
    (ensures subst_branches
               (subst_branches brs (open_with_var x i))
               [ ND x i ]
                == brs)
       (decreases brs)
  = match brs with
    | [] -> ()
    | b :: brs ->
      close_open_inverse'_branch i b x;
      close_open_inverse'_branches i brs x

and close_open_inverse'_branch (i:nat)
                               (br:branch)
                               (x:var{ ~(x `Set.mem` freevars_branch br) })
  : Lemma
    (ensures subst_branch
               (subst_branch br (open_with_var x i))
               [ ND x i ]
                == br)
    (decreases br)
  = let p, t = br in
    close_open_inverse'_pattern i p x;
    binder_offset_pattern_invariant p (open_with_var x i);
    close_open_inverse' (i + binder_offset_pattern p) t x


and close_open_inverse'_pattern (i:nat)
                                (p:pattern)
                                (x:var{ ~(x `Set.mem` freevars_pattern p) })
  : Lemma
    (ensures subst_pattern
               (subst_pattern p (open_with_var x i))
               [ ND x i ]
                == p)
    (decreases p)
  = match p with
    | Pat_Constant _ -> ()

    | Pat_Cons fv us pats -> 
      close_open_inverse'_patterns i pats x
      
    | Pat_Var bv _ -> ()

    | Pat_Dot_Term topt ->
      match topt with
      | None -> ()
      | Some t -> close_open_inverse' i t x

and close_open_inverse'_patterns (i:nat)
                                 (ps:list (pattern & bool))
                                 (x:var {~ (x `Set.mem` freevars_patterns ps) })
  : Lemma 
    (ensures subst_patterns
               (subst_patterns ps (open_with_var x i))
               [ ND x i ]
             == ps)
    (decreases ps)
  = match ps with
    | [] -> ()
    | (p, b)::ps' ->
      close_open_inverse'_pattern i p x;
      let n = binder_offset_pattern p in
      binder_offset_pattern_invariant p (open_with_var x i);
      close_open_inverse'_patterns (i + n) ps' x

and close_open_inverse'_match_returns (i:nat) (m:match_returns_ascription)
                                      (x:var{ ~(x `Set.mem` freevars_match_returns m) })
  : Lemma
    (ensures subst_match_returns
               (subst_match_returns m (open_with_var x i))
               [ ND x i ]
                == m)
       (decreases m)
  = let b, (ret, as_, eq) = m in
    close_open_inverse'_binder i b x;
    (match ret with
      | Inl t -> close_open_inverse' (i + 1) t x
      | Inr c -> close_open_inverse'_comp (i + 1) c x);
    (match as_ with
     | None -> ()
     | Some t -> close_open_inverse' (i + 1) t x)


let close_open_inverse (e:R.term) (x:var {~ (x `Set.mem` freevars e) })
  : Lemma (close_term (open_term e x) x == e)
   = open_term_spec e x;
     close_term_spec (open_term e x) x;
     close_open_inverse' 0 e x

let rec close_with_not_free_var (t:R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars t)))
      (ensures subst_term t [ ND x i ] == t)
      (decreases t) =

  match inspect_ln t with
  | Tv_Var _
  | Tv_BVar _
  | Tv_FVar _
  | Tv_UInst _ _ -> ()
  | Tv_App hd (arg, _) ->
    close_with_not_free_var hd x i;
    close_with_not_free_var arg x i
  | Tv_Abs b body ->
    close_binder_with_not_free_var b x i;
    close_with_not_free_var body x (i + 1)
  | Tv_Arrow b c ->
    close_binder_with_not_free_var b x i;
    close_comp_with_not_free_var c x (i + 1)
  | Tv_Type _ -> ()
  | Tv_Refine b t ->
    close_binder_with_not_free_var b x i;
    close_with_not_free_var t x (i + 1)
  | Tv_Const _ -> ()
  | Tv_Uvar _ _ -> assert False
  | Tv_Let recf attrs b e1 e2 ->
    close_terms_with_not_free_var attrs x i;
    close_binder_with_not_free_var b x i;
    (if recf then close_with_not_free_var e1 x (i + 1)
     else close_with_not_free_var e1 x i);
    close_with_not_free_var e2 x (i + 1)
  | Tv_Match scrutinee ret_opt brs ->
    close_with_not_free_var scrutinee x i;
    (match ret_opt with
     | None -> ()
     | Some ret -> close_match_returns_with_not_free_var ret x i);
    close_branches_with_not_free_var brs x i

  | Tv_AscribedT e t tacopt _ ->
    close_with_not_free_var e x i;
    close_with_not_free_var t x i;
    (match tacopt with
     | None -> ()
     | Some tac -> close_with_not_free_var tac x i)

  | Tv_AscribedC e c tacopt _ ->
    close_with_not_free_var e x i;
    close_comp_with_not_free_var c x i;
    (match tacopt with
     | None -> ()
     | Some tac -> close_with_not_free_var tac x i)

  | Tv_Unknown -> ()
  | Tv_Unsupp -> ()

and close_match_returns_with_not_free_var
  (r:match_returns_ascription)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_match_returns r)))
      (ensures subst_match_returns r [ ND x i ] == r)
      (decreases r) =

  let b, (ret, as_opt, _) = r in
  close_binder_with_not_free_var b x i;
  (match ret with
   | Inl t -> close_with_not_free_var t x (i + 1)
   | Inr c -> close_comp_with_not_free_var c x (i + 1));
  (match as_opt with
   | None -> ()
   | Some t -> close_with_not_free_var t x (i + 1))

and close_branches_with_not_free_var
  (brs:list R.branch)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branches brs)))
      (ensures subst_branches brs [ ND x i ] == brs)
      (decreases brs) =

  match brs with
  | [] -> ()
  | hd::tl ->
    close_branch_with_not_free_var hd x i;
    close_branches_with_not_free_var tl x i

and close_branch_with_not_free_var
  (br:R.branch)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branch br)))
      (ensures subst_branch br [ ND x i ] == br)
      (decreases br) =

  let p, t = br in
  close_pattern_with_not_free_var p x i;
  close_with_not_free_var t x (binder_offset_pattern p + i)
  
and close_pattern_with_not_free_var (p:R.pattern) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_pattern p)))
      (ensures subst_pattern p [ ND x i ] == p)
      (decreases p) =

  match p with
  | Pat_Constant _ -> ()
  | Pat_Cons _ _ pats ->
    close_patterns_with_not_free_var pats x i
  | Pat_Var bv _ -> ()
  | Pat_Dot_Term topt ->
    (match topt with
     | None -> ()
     | Some t -> close_with_not_free_var t x i)

and close_patterns_with_not_free_var (l:list (R.pattern & bool)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_patterns l)))
      (ensures subst_patterns l [ ND x i ] == l)
      (decreases l) =

  match l with
  | [] -> ()
  | (p, _)::tl ->
    close_pattern_with_not_free_var p x i;
    close_patterns_with_not_free_var tl x (binder_offset_pattern p + i)

and close_terms_with_not_free_var (l:list R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_terms l)))
      (ensures subst_terms l [ ND x i ] == l)
      (decreases l) =

  match l with
  | [] -> ()
  | hd::tl ->
    close_with_not_free_var hd x i;
    close_terms_with_not_free_var tl x i

and close_binder_with_not_free_var (b:R.binder) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_binder b)))
      (ensures subst_binder b [ ND x i ] == b)
      (decreases b) =

  let {attrs; sort} = inspect_binder b in
  close_with_not_free_var sort x i;
  close_terms_with_not_free_var attrs x i

and close_comp_with_not_free_var (c:R.comp) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_comp c)))
      (ensures subst_comp c [ ND x i ] == c)
      (decreases c) =

  match inspect_comp c with
  | C_Total t
  | C_GTotal t -> close_with_not_free_var t x i
  | C_Lemma pre post pats ->
    close_with_not_free_var pre x i;
    close_with_not_free_var post x i;
    close_with_not_free_var pats x i
  | C_Eff _ _ t args decrs ->
    close_with_not_free_var t x i;
    close_args_with_not_free_var args x i;
    close_terms_with_not_free_var decrs x i

and close_args_with_not_free_var (l:list R.argv) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_args l)))
      (ensures subst_args l [ ND x i ] == l)
      (decreases l) =

  match l with
  | [] -> ()
  | (t, _)::tl ->
    close_with_not_free_var t x i;
    close_args_with_not_free_var tl x i

let equiv_arrow #g #e1 #e2 ty q x eq =
  assume (~ (x `Set.mem` (freevars e1 `Set.union` freevars e2)));
  let c1 = E_Total, e1 in
  let c2 = E_Total, e2 in
  Rel_arrow _ _ _ _ c1 c2 _ _ (Rel_refl _ _ _) (Relc_typ _ _ _ _ _ eq)

let equiv_abs_close #g #e1 #e2 ty q x eq =
  // TODO: the following can be the preconditions?
  //       or derived from equiv?
  assume (ln' e1 (-1));
  assume (ln' e2 (-1));
  // this should be a lemma
  assume (~ (x `Set.mem` (freevars (subst_term e1 [ ND x 0 ]) `Set.union`
                          freevars (subst_term e2 [ ND x 0 ]))));
  open_close_inverse' 0 e1 x;
  open_close_inverse' 0 e2 x;
  let eq
    : equiv (extend_env g x ty)
        (subst_term
           (subst_term e1 [ ND x 0 ])
           (open_with_var x 0))
        (subst_term
           (subst_term e2 [ ND x 0 ])
           (open_with_var x 0)) =
    eq in

  Rel_abs _ _ _ _ _ _ _ (Rel_refl _ _ _) eq

let rec open_with_gt_ln e i t j
  : Lemma (requires ln' e i /\ i < j)
          (ensures subst_term e [ DT j t ] == e)
          (decreases e) =
  match inspect_ln e with
  | Tv_UInst _ _
  | Tv_FVar _
  | Tv_Type _
  | Tv_Const _
  | Tv_Unsupp
  | Tv_Unknown
  | Tv_Var _
  | Tv_BVar _ -> ()
  | Tv_App hd argv -> 
    open_with_gt_ln hd i t j;
    open_with_gt_ln (fst argv) i t j
  | Tv_Abs b body ->
    open_with_gt_ln_binder b i t j;
    open_with_gt_ln body (i + 1) t (j + 1)
  | Tv_Arrow b c ->
    open_with_gt_ln_binder b i t j;
    open_with_gt_ln_comp c (i + 1) t (j + 1)
  | Tv_Refine b f ->
    open_with_gt_ln_binder b i t j;
    open_with_gt_ln f (i + 1) t (j + 1)
  | Tv_Uvar j c -> admit ()
  | Tv_Let recf attrs b def body ->
    open_with_gt_ln_terms attrs i t j;
    open_with_gt_ln_binder b i t j;
    (if recf
     then open_with_gt_ln def (i + 1) t (j + 1)
     else open_with_gt_ln def i t j);
    open_with_gt_ln body (i + 1) t (j + 1)
  | Tv_Match scr ret brs ->
    open_with_gt_ln scr i t j;
    (match ret with
     | None -> ()
     | Some ret -> open_with_gt_ln_match_returns ret i t j);
    open_with_gt_ln_branches brs i t j
  | Tv_AscribedT e t1 tac _ ->
    open_with_gt_ln e i t j;
    open_with_gt_ln t1 i t j;
    (match tac with
     | None -> ()
     | Some tac -> open_with_gt_ln tac i t j)
  | Tv_AscribedC e c tac _ ->
    open_with_gt_ln e i t j;
    open_with_gt_ln_comp c i t j;
    (match tac with
     | None -> ()
     | Some tac -> open_with_gt_ln tac i t j)

and open_with_gt_ln_binder (b:binder) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_binder b i /\ i < j)
          (ensures subst_binder b [ DT j t ] == b)
          (decreases b) =

  let {attrs;sort} = inspect_binder b in
  open_with_gt_ln sort i t j;
  open_with_gt_ln_terms attrs i t j

and open_with_gt_ln_comp (c:comp) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_comp c i /\ i < j)
          (ensures subst_comp c [ DT j t ] == c)
          (decreases c) =
  
  match inspect_comp c with
  | C_Total t1
  | C_GTotal t1 -> open_with_gt_ln t1 i t j
  | C_Lemma pre post pats ->
    open_with_gt_ln pre i t j;
    open_with_gt_ln post i t j;
    open_with_gt_ln pats i t j
  | C_Eff _ _ res args decrs ->
    open_with_gt_ln res i t j;
    open_args_with_gt_ln_args args i t j;
    open_with_gt_ln_terms decrs i t j

and open_with_gt_ln_terms (l:list term) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_terms l i /\ i < j)
          (ensures subst_terms l [ DT j t ] == l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd::tl ->
    open_with_gt_ln hd i t j;
    open_with_gt_ln_terms tl i t j

and open_with_gt_ln_match_returns (m:match_returns_ascription) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_match_returns m i /\ i < j)
          (ensures subst_match_returns m [ DT j t ] == m)
          (decreases m) =
  
  let b, (ret, as_, _) = m in
  open_with_gt_ln_binder b i t j;
  (match ret with
   | Inl t1 -> open_with_gt_ln t1 (i + 1) t (j + 1)
   | Inr c -> open_with_gt_ln_comp c (i + 1) t (j + 1));
  (match as_ with
   | None -> ()
   | Some t1 -> open_with_gt_ln t1 (i + 1) t (j + 1))


and open_with_gt_ln_branches (l:list branch) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_branches l i /\ i < j)
          (ensures subst_branches l [ DT j t ] == l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd::tl ->
    open_with_gt_ln_branch hd i t j;
    open_with_gt_ln_branches tl i t j

and open_args_with_gt_ln_args (l:list argv) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_args l i /\ i < j)
          (ensures subst_args l [ DT j t ] == l)
          (decreases l) =
  
  match l with
  | [] -> ()
  | (t1, _)::tl ->
    open_with_gt_ln t1 i t j;
    open_args_with_gt_ln_args tl i t j

and open_with_gt_ln_branch (b:branch) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_branch b i /\ i < j)
          (ensures subst_branch b [ DT j t ] == b)
          (decreases b) =
  
  let p, t1 = b in
  open_with_gt_ln_pat p i t j;
  let k = binder_offset_pattern p in
  open_with_gt_ln t1 (i + k) t (j + k)

and open_with_gt_ln_pat (p:pattern) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_pattern p i /\ i < j)
          (ensures subst_pattern p [ DT j t ] == p)
          (decreases p) =
  
  match p with
  | Pat_Constant _ -> ()
  | Pat_Cons _ _ pats ->
    open_with_gt_ln_pats pats i t j
  | Pat_Var bv _ -> ()
  | Pat_Dot_Term topt ->
    (match topt with
     | None -> ()
     | Some t1 -> open_with_gt_ln t1 i t j)

and open_with_gt_ln_pats (l:list (pattern & bool)) (i:nat) (t:term) (j:nat)
  : Lemma (requires ln'_patterns l i /\ i < j)
          (ensures subst_patterns l [ DT j t ] == l)
          (decreases l) =
  
  match l with
  | [] -> ()
  | hd::tl ->
    open_with_gt_ln_pat (fst hd) i t j;
    let k = binder_offset_pattern (fst hd) in
    open_with_gt_ln_pats tl (i + k) t (j + k)

let if_complete_match (g:env) (t:term) = magic()

let mkif
    (g:fstar_env)
    (scrutinee:term)
    (then_:term)
    (else_:term)
    (ty:term)
    (u_ty:universe)
    (hyp:var { None? (lookup_bvar g hyp) /\ ~(hyp `Set.mem` (freevars then_ `Set.union` freevars else_)) })
    (eff:tot_or_ghost)
    (ty_eff:tot_or_ghost)
    (ts : typing g scrutinee (eff, bool_ty))
    (tt : typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee true_bool)) then_ (eff, ty))
    (te : typing (extend_env g hyp (eq2 (pack_universe Uv_Zero) bool_ty scrutinee false_bool)) else_ (eff, ty))
    (tr : typing g ty (ty_eff, tm_type u_ty))
: typing g (mk_if scrutinee then_ else_) (eff, ty)
= let brt = (Pat_Constant C_True, then_) in
  let bre = (Pat_Constant C_False, else_) in
  bindings_ok_pat_constant g C_True;
  bindings_ok_pat_constant g C_False;
  let brty () : branches_typing g u_zero bool_ty scrutinee (eff,ty) [brt; bre] [[]; []] =
    BT_S (Pat_Constant C_True, then_) []
         (BO (Pat_Constant C_True) [] hyp then_ () tt)
         _ _ (
      BT_S (Pat_Constant C_False, else_) []
           (BO (Pat_Constant C_False) [] hyp else_ () te)
           _ _
        BT_Nil)
  in
  T_Match g u_zero bool_ty scrutinee E_Total (T_FVar g bool_fv) eff ts [brt; bre] (eff, ty)
    [[]; []]
    (MC_Tok g scrutinee bool_ty _ _ (Squash.return_squash (if_complete_match g scrutinee)))
    (brty ())

let typing_to_token (#g:env) (#e:term) (#c:comp_typ) (_ : typing g e c) = magic()
