module Bug4401

(* Masking the effect of a top-level definition with a divergent effect
   is only sound if its type is inhabited. F* therefore requires a proof
   of `Prims.nonempty t` for every top-level `let x : t = e` where `e`
   has an effect other than Tot/GTot. *)

let rec loop (#a:Type) (u:unit) : Div a (requires True) (ensures fun _ -> True) = loop #a u

[@@expect_failure [19]]
let bad : False = loop ()

[@@expect_failure [19]]
let bad2 : (x:int{x <> x}) = loop ()

noeq type wrap (a:Type) = | W of a

[@@expect_failure [19]]
let bad3 : wrap False = loop ()

(* The normalizer discharges the obligation for the handful of types it
   already recognizes as obviously inhabited, and for arrows returning
   one of them. *)

let ok_int : int = loop ()
let ok_bool : bool = loop ()
let ok_string : string = loop ()
let ok_exn : exn = loop ()
let ok_arrow : int -> string = loop ()

(* For anything else, a witness must be supplied. A top-level proof of
   `nonempty t` makes the fact available to the SMT solver. *)

type mytree = | Leaf | Node of mytree & mytree
type myrec = { fx: int; fy: bool }

let _ : nonempty (int & bool) = nonempty_intro (1, true)
let ok_tup : int & bool = loop ()

let _ : nonempty mytree = nonempty_intro Leaf
let ok_tree : mytree = loop ()

let _ : nonempty myrec = nonempty_intro ({ fx = 0; fy = false })
let ok_rec : myrec = loop ()

let _ : nonempty (either int False) = nonempty_intro (Inl 0)
let ok_either : either int False = loop ()

let _ : nonempty (wrap (option False)) = nonempty_intro (W None)
let ok_wrap : wrap (option False) = loop ()

(* The witness may itself be ghost. *)
let _ : nonempty (squash (0 == 0)) = nonempty_intro ()
let ok_squash : squash (0 == 0) = loop ()

(* Everything else needs a witness too, including types that are easy to
   inhabit but that the normalizer does not special-case. *)

let _ : nonempty unit = nonempty_intro ()
let ok_unit : unit = loop ()

let _ : nonempty (list False) = nonempty_intro []
let ok_list : list False = loop ()

let _ : nonempty (option False) = nonempty_intro None
let ok_option : option False = loop ()

let _ : nonempty prop = nonempty_intro True
let ok_prop : prop = loop ()

let _ : nonempty Type = nonempty_intro unit
let ok_type : Type = loop ()
