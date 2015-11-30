(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.IO --admit_fsi FStar.String;
    other-files:set.fsi heap.fst st.fst all.fst io.fsti string.fsi ghost.fst ordset.fsi ordmap.fsi prins.fst ast.fst
 --*)

module Print

open FStar.String
open FStar.OrdSet
open Prins
open AST

val prin_to_string: prin -> Tot string
let prin_to_string = function
  | Alice   -> "alice"
  | Bob     -> "bob"
  | Charlie -> "charlie"
  | Dave    -> "dave"
  | Evelyn  -> "evelyn"
  | Fred    -> "fred"

val prins_to_string_helper: eps:eprins -> string -> Tot string (decreases (size eps))
let rec prins_to_string_helper eps s =
  if eps = empty then s
  else
    let Some p = choose eps in
    let eps' = remove p eps in
    let s' = strcat (strcat s (prin_to_string p)) ";" in
    prins_to_string_helper eps' s'

val prins_to_string: eprins -> Tot string
let prins_to_string eps = strcat (strcat "{" (prins_to_string_helper eps "")) "}"

val tagged_unary_to_string: string -> string -> Tot string
let tagged_unary_to_string tag e = strcat (strcat (strcat tag " (") e) ")"

val tagged_binary_to_string: string -> string -> string -> Tot string
let tagged_binary_to_string tag e1 e2 =
  strcat (strcat (strcat (strcat  (strcat tag " (") e1) ") (") e2) ")"

val tagged_ternary_to_string: string -> string -> string -> string -> Tot string
let tagged_ternary_to_string tag e1 e2 e3 =
  strcat (strcat (strcat (strcat (strcat (strcat  (strcat tag " (") e1) ") (") e2) ") (") e3) ")"

val const_to_string: const -> Tot string
let const_to_string = function
  | C_prin p       -> tagged_unary_to_string "C_prin" (prin_to_string p)
  | C_eprins eps   -> tagged_unary_to_string "C_eprins" (prins_to_string eps)
  | C_unit _       -> "C_unit"
  | C_bool b       -> tagged_unary_to_string "C_bool" (string_of_bool b)
  | C_opaque 'a _ _ -> "C_opaque"  // TODO: print of opaque values

val exp_to_string: e:exp -> Tot string (decreases e)
val exp_list_to_string_helper: l:list exp -> string -> Tot string (decreases %[l; 0])
val exp_list_to_string: l:list exp -> Tot string (decreases %[l; 1])
let rec exp_to_string = function
  | E_aspar ps e       ->
    tagged_binary_to_string "E_aspar" (exp_to_string ps) (exp_to_string e)
  | E_assec ps e       ->
    tagged_binary_to_string "E_assec" (exp_to_string ps) (exp_to_string e)
  | E_box ps e         ->
    tagged_binary_to_string "E_box" (exp_to_string ps) (exp_to_string e)
  | E_unbox e          ->
    tagged_unary_to_string "E_unbox" (exp_to_string e)
  | E_mkwire e1 e2     ->
    tagged_binary_to_string "E_mkwire" (exp_to_string e1) (exp_to_string e2)
  | E_projwire e1 e2   ->
    tagged_binary_to_string "E_projwire" (exp_to_string e1) (exp_to_string e2)
  | E_concatwire e1 e2 ->
    tagged_binary_to_string "E_concatwire" (exp_to_string e1) (exp_to_string e2)

  | E_const c          -> 
    tagged_unary_to_string "E_const" (const_to_string c)
  | E_var x            ->
    tagged_unary_to_string "E_var" (name_of_var x)
  | E_let x e1 e2      ->
    tagged_ternary_to_string "E_let" (name_of_var x) (exp_to_string e1) (exp_to_string e2)
  | E_abs x e          ->
    tagged_binary_to_string "E_abs" (name_of_var x) (exp_to_string e)
  | E_fix f x e        ->
    tagged_ternary_to_string "E_fix" (name_of_var f) (name_of_var x) (exp_to_string e)
  | E_empabs x e       ->
    tagged_binary_to_string "E_empabs" (name_of_var x) (exp_to_string e)
  | E_app e1 e2        ->
    tagged_binary_to_string "E_app" (exp_to_string e1) (exp_to_string e2)
  | E_ffi 'a 'b n fname _ l _  ->
    tagged_ternary_to_string "E_ffi" (string_of_int n) fname (exp_list_to_string l)
  | E_cond e e1 e2     ->
    tagged_ternary_to_string "E_cond" (exp_to_string e) (exp_to_string e1) (exp_to_string e2)

and exp_list_to_string_helper l s = match l with
  | []    -> s
  | hd::tl ->
    let s' = strcat (strcat s (exp_to_string hd)) "; " in
    exp_list_to_string_helper tl s'

and exp_list_to_string l =
  let s = exp_list_to_string_helper l "" in
  strcat (strcat "[" s) "]"

val v_meta_to_string: v_meta -> Tot string
let v_meta_to_string m =
  let Meta bps cb wps cw = m in
  let scb = if cb = Can_b then "Can_b" else "Cannot_b" in
  let scw = if cw = Can_w then "Can_w" else "Cannot_w" in
  strcat (strcat (strcat (strcat (strcat (strcat (strcat "Meta " scb) " ") (prins_to_string bps)) " ") scw) " ") (prins_to_string wps)

val value_to_string: #meta:v_meta -> v:value meta -> Tot string (decreases v)
val v_wire_to_string_helper: #eps:eprins -> eps':eprins{subset eps' eps} -> m:v_wire eps -> string -> Tot string (decreases %[m; (size eps'); 0])
val v_wire_to_string: #eps:eprins -> m:v_wire eps -> Tot string (decreases %[m; (size eps); 1])
let rec value_to_string #meta v =
  let s =
    match v with
      | V_prin p             ->
	tagged_unary_to_string "V_prin" (prin_to_string p)
      | V_eprins eps         ->
	tagged_unary_to_string "V_eprins" (prins_to_string eps)
      | V_unit               -> "V_unit"
      | V_bool b             ->
        tagged_unary_to_string "V_bool" (string_of_bool b)
      | V_opaque 'a _ _ _ _ _ -> "V_opaque"
      | V_box ps v'          ->
	tagged_binary_to_string "V_box" (prins_to_string ps) (value_to_string v')
      | V_wire all eps m     ->
        tagged_binary_to_string "V_wire" (prins_to_string all) (v_wire_to_string #eps m)
      | V_clos _ x _         ->
	tagged_unary_to_string "V_clos" (name_of_var x)
      | V_fix_clos _ f x e   ->
	tagged_binary_to_string "V_fix_clos" (name_of_var f) (name_of_var x)
      | V_emp_clos x _       ->
        tagged_unary_to_string "V_emp_clos" (name_of_var x)
      | V_emp                -> "V_emp"
  in
  strcat (strcat (strcat s " (") (v_meta_to_string meta)) ")"

and v_wire_to_string_helper #eps eps' m s =
  if eps' = empty then s
  else
    let Some p = choose eps' in
    let eps'' = remove p eps' in
    let Some v = OrdMap.select p m in
    let _ = admitP (v << m) in
    let s' = strcat (strcat (strcat (strcat s (prin_to_string p)) ":") (value_to_string v)) "; " in
    v_wire_to_string_helper #eps eps'' m s'

and v_wire_to_string #eps m = v_wire_to_string_helper #eps eps m ""

val redex_to_string: redex -> Tot string
let redex_to_string = function
  | R_aspar _ _        -> "R_aspar"
  | R_assec _ _        -> "R_assec"
  | R_box _ _          -> "R_box"
  | R_unbox _          -> "R_unbox"
  | R_mkwire _ _       -> "R_mkwire"
  | R_projwire _ _     -> "R_projwire"
  | R_concatwire _ _   -> "R_concatwire"
  | R_let _ _ _        -> "R_let"
  | R_app _ _          -> "R_app"
  | R_ffi 'a 'b _ _ _ _  -> "R_ffi"
  | R_cond _ _ _       -> "R_cond"

val as_mode_to_string: as_mode -> Tot string
let as_mode_to_string = function
  | Par -> "par"
  | Sec -> "sec"

val mode_to_string: mode -> Tot string
let mode_to_string (Mode as_m ps) =
  strcat (strcat (strcat (as_mode_to_string as_m) "(") (prins_to_string ps)) ")"

val frame'_to_string: frame' -> Tot string
let frame'_to_string = function
  | F_aspar_ps _        -> "F_aspar_ps"
  | F_aspar_e _         -> "F_aspar_e"
  | F_aspar_ret _       -> "F_aspar_ret"
  | F_assec_ps _        -> "F_assec_ps"
  | F_assec_e _         -> "F_assec_e"
  | F_assec_ret         -> "F_assec_ret"
  | F_box_ps _          -> "F_box_ps"
  | F_box_e _           -> "F_box_e"
  | F_unbox             -> "F_unbox"
  | F_mkwire_ps _       -> "F_mkwire_ps"
  | F_mkwire_e _        -> "F_mkwire_w"
  | F_projwire_p _      -> "F_projwire_p"
  | F_projwire_e _      -> "F_projwire_e"
  | F_concatwire_e1 _   -> "F_concatwire_e1"
  | F_concatwire_e2 _   -> "F_concatwire_e2"
  | F_let _ _           -> "F_let"
  | F_app_e1 _          -> "F_app_e1"
  | F_app_e2 _          -> "F_app_e2"
  | F_ffi 'a 'b _ _ _ _ _ -> "F_ffi"
  | F_cond _ _          -> "F_cond"

val frame_to_string: frame -> Tot string
let frame_to_string (Frame m _ f _) =
  strcat (strcat (strcat (strcat "Frame (" (mode_to_string m)) ") (") (frame'_to_string f)) ")"

val stack_to_string: stack -> Tot string
let stack_to_string = function
  | []  -> "[]"
  | f::_ -> frame_to_string f

val term_to_string: term -> Tot string
let term_to_string = function
  | T_exp e    ->
    tagged_unary_to_string "T_exp" (exp_to_string e)
  | T_red r    ->
    tagged_unary_to_string "T_red" (redex_to_string r)
  | T_val v    ->
    tagged_unary_to_string "T_val" (value_to_string v)
  | T_sec_wait -> "T_sec_wait"

val config_to_string: config -> Tot string
let config_to_string (Conf _ m s en t _) =
  strcat (strcat (strcat (strcat (strcat (strcat "Conf (" (mode_to_string m)) ") (") (stack_to_string s)) ") (") (term_to_string t)) ")"
