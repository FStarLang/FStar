module Steel.ST.C.Types.Fields
include Steel.ST.C.Types.Base
open Steel.C.Typestring
open Steel.ST.Util

[@@noextract_to "krml"] // tactic
let norm_fields () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%norm_field_attr]; iota; zeta; primops];
  FStar.Tactics.trefl ()

[@@noextract_to "krml"] // primitive
val field_t_nil: Type0
[@@noextract_to "krml"] // primitive
val field_t_cons (fn: Type0) (ft: Type0) (fc: Type0): Type0

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
noeq
type field_description_t (t: Type0) : Type u#1 = {
  fd_def: (string -> GTot bool);
  fd_empty: (fd_empty: bool { fd_empty == true <==> (forall s . fd_def s == false) });
  fd_type: (string -> Type0);
  fd_typedef: ((s: string) -> Pure (typedef (fd_type s)) (requires (fd_def s)) (ensures (fun _ -> True)));
}

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let nonempty_field_description_t (t: Type0) =
  (fd: field_description_t t { fd.fd_empty == false })

[@@noextract_to "krml"] // proof-only
let field_t (#t: Type0) (fd: field_description_t t) : Tot eqtype = (s: string { fd.fd_def s })

inline_for_extraction [@@noextract_to "krml"]
let field_description_nil : field_description_t field_t_nil = {
  fd_def = (fun _ -> false);
  fd_empty = true;
  fd_type = (fun _ -> unit);
  fd_typedef = (fun _ -> false_elim ());
}

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let field_description_cons0
  (fn: Type0) (#ft: Type0) (#fc: Type0) (n: string) (t: typedef ft) (fd: field_description_t fc)
: Tot (nonempty_field_description_t (field_t_cons fn ft fc))
= {
    fd_def = (fun n' -> n = n' || fd.fd_def n');
    fd_empty = false;
    fd_type = (fun n' -> if n = n' then ft else fd.fd_type n');
    fd_typedef = (fun n' -> if n = n' then t else fd.fd_typedef n');
  }

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let field_description_cons (#ft: Type0) (#fc: Type0) (n: string) (#fn: Type0) (# [ solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == fn))) (t: typedef ft) (fd: field_description_t fc) : Tot (nonempty_field_description_t (field_t_cons fn ft fc)) =
  field_description_cons0 fn #ft #fc n t fd
