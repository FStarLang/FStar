(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String;
    other-files:ghost.fst listTot.fst set.fsi ordset.fsi ordmap.fsi classical.fst heap.fst st.fst all.fst io.fsti string.fst prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst
 --*)

module Inliner

open AST
open FStar.OrdSet
open FStar.IO

val is_inlined_ffi: string -> Tot bool
let is_inlined_ffi s = true

val is_inlined: exp -> Tot bool
val is_inlined_l: list exp -> Tot bool
let rec is_inlined = function
  | E_box ps e                  -> is_inlined ps && is_inlined e
  | E_unbox e                   -> is_inlined e
  | E_mkwire e1 e2              -> is_inlined e1 && is_inlined e2
  | E_projwire e1 e2            -> is_inlined e1 && is_inlined e2
  | E_concatwire e1 e2          -> is_inlined e1 && is_inlined e2

  | E_const _                   -> true
  | E_var _                     -> true
  | E_let _ e1 e2               -> is_inlined e1 && is_inlined e2
  | E_ffi 'a 'b _ fname _ args _  -> is_inlined_ffi fname && is_inlined_l args
  | E_cond e e1 e2              -> is_inlined e && is_inlined e1 && is_inlined e2
  | _                           -> false

and is_inlined_l = function
  | []   -> true
  | e::tl -> is_inlined e && is_inlined_l tl

val v_cmp: varname -> varname -> Tot bool
let v_cmp v1 v2 = if FStar.String.compare v1 v2 <= 0 then true else false

assume V_cmp_is_total_order: total_order string v_cmp

type varset = ordset varname v_cmp

val fvs: exp -> Tot varset
val fvs_l: list exp -> Tot varset
let rec fvs = function
  | E_aspar ps e                -> union (fvs ps) (fvs e)
  | E_assec ps e                -> union (fvs ps) (fvs e)
  | E_box ps e                  -> union (fvs ps) (fvs e)
  | E_unbox e                   -> fvs e
  | E_mkwire e1 e2              -> union (fvs e1) (fvs e2)
  | E_projwire e1 e2            -> union (fvs e1) (fvs e2)
  | E_concatwire e1 e2          -> union (fvs e1) (fvs e2)

  | E_const _                   -> empty
  | E_var x                     -> singleton x
  | E_let x e1 e2               -> union (fvs e1) (remove x (fvs e2))
  | E_abs x e                   -> remove x (fvs e)
  | E_fix f x e                 -> remove f (remove x (fvs e))
  | E_empabs x e                -> remove x (fvs e)
  | E_app e1 e2                 -> union (fvs e1) (fvs e2)
  | E_ffi 'a 'b _ fname _ args _  -> fvs_l args
  | E_cond e e1 e2              -> union (fvs e) (union (fvs e1) (fvs e2))

and fvs_l = function
  | []   -> empty
  | e::tl -> union (fvs e) (fvs_l tl)

val subst: exp -> varname -> exp -> exp
val subst_l: list exp -> varname -> exp -> list exp
let rec subst e v ev = match e with
  | E_aspar ps e                -> E_aspar (subst ps v ev) (subst e v ev)
  | E_assec ps e                -> E_assec (subst ps v ev) (subst e v ev)
  | E_box ps e                  -> E_box (subst ps v ev) (subst e v ev)
  | E_unbox e                   -> E_unbox (subst e v ev)
  | E_mkwire e1 e2              -> E_mkwire (subst e1 v ev) (subst e2 v ev)
  | E_projwire e1 e2            -> E_projwire (subst e1 v ev) (subst e2 v ev)
  | E_concatwire e1 e2          -> E_concatwire (subst e1 v ev) (subst e2 v ev)

  | E_const _                   -> e
  | E_var x                     -> if x = v then ev else e
  | E_let x e1 e2               ->
    let e1' = subst e1 v ev in
    if x = v then E_let x e1' e2
    else if mem x (fvs ev) then failwith "let substitution failed"
    else E_let x (subst e1 v ev) (subst e2 v ev)
  | E_abs x e                   ->
    if x = v then E_abs x e
    else if mem x (fvs ev) then failwith "abs substitution failed"
    else E_abs x (subst e v ev)
  | E_fix f x e                 ->
    if f = v || x = v then E_fix f x e
    else if mem f (fvs ev) || mem x (fvs ev) then failwith "fix substitution failed"
    else E_fix f x (subst e v ev)
  | E_empabs x e                ->
    if x = v then E_empabs x e
    else if mem x (fvs ev) then failwith "empabs substitution failed"
    else E_empabs x (subst e v ev)
  | E_app e1 e2                 -> E_app (subst e1 v ev) (subst e2 v ev)
  | E_ffi 'a 'b a fname b args c  -> E_ffi a fname b (subst_l args v ev) c
  | E_cond e e1 e2              -> E_cond (subst e v ev) (subst e1 v ev) (subst e2 v ev)

and subst_l l v ev = match l with
  | []   -> []
  | e::tl -> (subst e v ev)::(subst_l tl v ev)

val value_to_exp: en:env -> dv:dvalue -> option (env * exp)
let value_to_exp en dv = match D_v.v dv with
  | V_prin p            -> Some (en, E_const (C_prin p))
  | V_eprins eps        -> Some (en, E_const (C_eprins eps))
  | V_unit              -> Some (en, E_const (C_unit ()))
  | V_bool b            -> Some (en, E_const (C_bool b))
  | V_clos en x e       -> Some (en, E_abs x e)
  | V_fix_clos en f x e -> Some (en, E_fix f x e)
  | V_emp_clos x e      -> Some (en, E_empabs x e)
  | _                   -> None

val inline: m:mode{mode_inv m Target} -> en:env -> e:exp -> f:(config -> option config) -> env * exp
val inline_l: m:mode{mode_inv m Target} -> en:env -> l:list exp -> f:(config -> option config) -> list exp
let rec inline m en e f =
  (* if is_inlined e then en, e *)
  (* else *)
    match e with
      | E_aspar _ _
      | E_assec _ _                 -> failwith "Inline of aspar and assec not yet supported"
      | E_box ps e                  -> en, E_box (snd (inline m en ps f)) (snd (inline m en e f))
      | E_unbox e                   -> en, E_unbox (snd (inline m en e f))
      | E_mkwire e1 e2              -> en, E_mkwire (snd (inline m en e1 f)) (snd (inline m en e2 f))
      | E_projwire e1 e2            -> en, E_projwire (snd (inline m en e1 f)) (snd (inline m en e2 f))
      | E_concatwire e1 e2          -> en, E_concatwire (snd (inline m en e1 f)) (snd (inline m en e2 f))
      | E_const _                   -> en, e
      | E_var x                     ->
	let dv_opt = en x in
	if is_None dv_opt then (en, E_var x)
	else
	  let dv = Some.v dv_opt in
	  let e_opt = value_to_exp en dv in
	  if is_None e_opt then en, E_var x
	  else Some.v e_opt
      | E_let x e1 e2               -> en, E_let x (snd (inline m en e1 f)) (snd (inline m en e2 f))
      | E_abs x e                   -> en, E_abs x (snd (inline m en e f))
      | E_fix f' x e                -> en, E_fix f' x (snd (inline m en e f))
      | E_empabs x e                -> en, E_empabs x (snd (inline m en e f))
      | E_app e1 e2                 ->
	let en', e1' = inline m en e1 f in
	(match e1' with
	  | E_abs x e     -> en, snd (inline m en' (subst e x e2) f)
	  | E_fix f' x e  -> en, snd (inline m en' (subst (subst e f' (E_fix f' x e)) x e2) f)
	  | E_empabs x e  -> en, snd (inline m en' (subst e x e2) f)
	  | _             -> FStar.IO.print_string (Print.exp_to_string e1'); failwith "E_app case, inline of e1 is not an abstraction")

      | E_ffi 'a 'b a fname b args c  -> en, E_ffi a fname b (inline_l m en args f) c
      | E_cond e e1 e2              ->
	let conf = Conf Target m [] en (T_exp e) (FStar.Ghost.hide []) in
	let c_opt = f conf in
	match c_opt with
	  | None   -> failwith "step_star does not return None"
	  | Some c ->
	    if is_terminal c then
	      let Conf _ _ _ _ (T_val v) _ = c in
	      if Semantics.is_v_bool v then
		let V_bool b = v in
		if b then (inline m en e1 f) else (inline m en e2 f)
	      else failwith "Cond expr evaluated to something other than bool"
	    else
	      en, E_cond (snd (inline m en e f)) (snd (inline m en e1 f)) (snd (inline m en e2 f))

and inline_l m en l f = match l with
  | []   -> []
  | e::tl -> (snd (inline m en e f))::(inline_l m en tl f)
