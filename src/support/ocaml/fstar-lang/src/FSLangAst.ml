(* -------------------------------------------------------------------- *)
exception ParseError of Lexing.position

let parse_error (loc : Lexing.position) =
  raise (ParseError loc)

(* -------------------------------------------------------------------- *)
type range = {
  rg_start : Lexing.position;
  rg_stop  : Lexing.position;
}

let mk_rg rg_start rg_stop =
  { rg_start; rg_stop; }

(* -------------------------------------------------------------------- *)
type 'a located = {
  lc_desc  : 'a;
  lc_range : range;
}

let range { lc_range } = lc_range
let desc  { lc_desc  } = lc_desc 

let mk_loc (rg : range) (x : 'a) =
  { lc_desc = x; lc_range = rg; }

(* -------------------------------------------------------------------- *)
type file = unit

let mk_ident (_ : 'a located) = ()

let mk_decl          ?(rg : range option) _ = ignore rg
let mk_module        ?(rg : range option) _ = ignore rg
let mk_monadic       ?(rg : range option) _ = ignore rg
let mk_open          ?(rg : range option) _ = ignore rg
let mk_top_let       ?(rg : range option) _ = ignore rg
let mk_val           ?(rg : range option) _ = ignore rg
let mk_monadlat      ?(rg : range option) _ = ignore rg
let mk_exception     ?(rg : range option) _ = ignore rg
let mk_assume        ?(rg : range option) _ = ignore rg
let mk_tycon         ?(rg : range option) _ = ignore rg
let mk_kind_abbrv    ?(rg : range option) _ = ignore rg
let mk_monad         ?(rg : range option) _ = ignore rg
let mk_monad_abbrv   ?(rg : range option) _ = ignore rg
let mk_lift          ?(rg : range option) _ = ignore rg
let mk_tycon_abs     ?(rg : range option) _ = ignore rg
let mk_tycon_abbrv   ?(rg : range option) _ = ignore rg
let mk_tycon_record  ?(rg : range option) _ = ignore rg
let mk_tycon_variant ?(rg : range option) _ = ignore rg
let mk_op            ?(rg : range option) _ = ignore rg
let mk_pattern       ?(rg : range option) _ = ignore rg
let mk_pat_var       ?(rg : range option) _ = ignore rg
let mk_pat_ascribed  ?(rg : range option) _ = ignore rg
let mk_pat_tuple     ?(rg : range option) _ = ignore rg
let mk_pat_cons      ?(rg : range option) _ = ignore rg
let mk_pat_app       ?(rg : range option) _ = ignore rg
let mk_pat_wild      ?(rg : range option) _ = ignore rg
let mk_pat_const     ?(rg : range option) _ = ignore rg
let mk_pat_tvar      ?(rg : range option) _ = ignore rg
let mk_pat_var       ?(rg : range option) _ = ignore rg
let mk_pat_name      ?(rg : range option) _ = ignore rg
let mk_pat_record    ?(rg : range option) _ = ignore rg
let mk_pat_list      ?(rg : range option) _ = ignore rg
let mk_pat_or        ?(rg : range option) _ = ignore rg
let mk_binder        ?(rg : range option) _ = ignore rg
let mk_bd_var        ?(rg : range option) _ = ignore rg
let mk_bd_tvar       ?(rg : range option) _ = ignore rg
let mk_bd_annot      ?(rg : range option) _ = ignore rg
let mk_bd_tannot     ?(rg : range option) _ = ignore rg
let mk_bd_refined    ?(rg : range option) _ = ignore rg
let mk_bd_anon       ?(rg : range option) _ = ignore rg
let mk_term          ?(rg : range option) _ = ignore rg
let mk_tm_const      ?(rg : range option) _ = ignore rg
let mk_tm_wild       ?(rg : range option) _ = ignore rg
let mk_tm_if         ?(rg : range option) _ = ignore rg
let mk_tm_try        ?(rg : range option) _ = ignore rg
let mk_tm_match      ?(rg : range option) _ = ignore rg
let mk_tm_let        ?(rg : range option) _ = ignore rg
let mk_tm_qforall    ?(rg : range option) _ = ignore rg
let mk_tm_qexists    ?(rg : range option) _ = ignore rg
let mk_tm_function   ?(rg : range option) _ = ignore rg
let mk_tm_app        ?(rg : range option) _ = ignore rg
let mk_tm_abs        ?(rg : range option) _ = ignore rg
let mk_tm_var        ?(rg : range option) _ = ignore rg
let mk_tm_tvar       ?(rg : range option) _ = ignore rg
let mk_tm_tuple      ?(rg : range option) _ = ignore rg
let mk_tm_dtuple     ?(rg : range option) _ = ignore rg
let mk_tm_product    ?(rg : range option) _ = ignore rg
let mk_tm_refine     ?(rg : range option) _ = ignore rg
let mk_tm_seq        ?(rg : range option) _ = ignore rg
let mk_tm_proj       ?(rg : range option) _ = ignore rg
let mk_tm_record     ?(rg : range option) _ = ignore rg
let mk_tm_qname      ?(rg : range option) _ = ignore rg
let mk_tm_list       ?(rg : range option) _ = ignore rg
let mk_tm_array      ?(rg : range option) _ = ignore rg
let mk_tm_parens     ?(rg : range option) _ = ignore rg
let mk_ct_unit       ?(rg : range option) _ = ignore rg
let mk_ct_unit       ?(rg : range option) _ = ignore rg
let mk_ct_int32      ?(rg : range option) _ = ignore rg
let mk_ct_uint8      ?(rg : range option) _ = ignore rg
let mk_ct_char       ?(rg : range option) _ = ignore rg
let mk_ct_string     ?(rg : range option) _ = ignore rg
let mk_ct_bytearray  ?(rg : range option) _ = ignore rg
let mk_ct_true       ?(rg : range option) _ = ignore rg
let mk_ct_false      ?(rg : range option) _ = ignore rg
let mk_ct_ieee64     ?(rg : range option) _ = ignore rg
let mk_ct_int64      ?(rg : range option) _ = ignore rg

let tm_set_level _ _ = ()
let tm_get_level _ = `Expr
