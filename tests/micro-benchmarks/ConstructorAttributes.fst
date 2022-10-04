module ConstructorAttributes
open FStar.Tactics

let meta_implicit (#[exact (`1)]x: int) = x

let a1 (t: Type u#n) (x: t) = ()

type test0 =
  | [@@@ meta_implicit; 123 + 456] A
  | [@@@ "B"; id 3] B: int -> test0

type test1 = [@@@ a1 u#12] { foo: int; }

[@@ expect_failure [66]]
type test2 = [@@@ id] { bar: int; }

// The attribute [expect_failure] can be used when a failure is
// expected in an attribute
[@@ expect_failure [189]; 1 + ()]
let test3: unit = unit

let lookup_sigelt (name: string): Tac sigelt
  = match lookup_typ (top_env ()) (explode_qn name) with
  | Some se -> se
  | _       -> fail ("lookup_sigelt: sigelt '"^name^"' not found")

let lookup_sigelt_attrs (name: string): Tac (list term) =
  sigelt_attrs (lookup_sigelt name)

open FStar.List.Tot
let terms_eq (x y: list term): bool
  = length x = length y
 && fold_left ( && ) true
              (map (fun (x, y) -> term_eq x y) (FStar.List.Pure.zip x y))

let _ =
  run_tactic (fun _ ->
        let ( ==. ) = terms_eq in
        guard (lookup_sigelt_attrs (`%A) ==. [`(meta_implicit #1); `(123 + 456)]);
        guard (lookup_sigelt_attrs (`%B) ==. [`"B"; `id #int 3]);
        guard (lookup_sigelt_attrs (`%Mktest1) ==. [`(a1 u#12)]);
	// // binders are typechecked, thus [id 3] is actually turned into `id #int 3`.
	// // consequently:
        guard (not (lookup_sigelt_attrs (`%A) ==. [`"B"; `id 3]))
  )
