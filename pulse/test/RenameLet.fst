module RenameLet
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Attributes

(* `rename_let` is implemented by F*'s extraction: it renames the binder of a
   local let-binding in the extracted code, without affecting typechecking.
   These tests check that Pulse propagates the attribute all the way there. *)

fn test_pure (x: UInt32.t)
  returns y : UInt32.t
{
  let [@@@rename_let "pureName"] v = UInt32.add_mod x 1ul;
  UInt32.add_mod v v
}

fn test_mut (x: UInt32.t)
  returns y : UInt32.t
{
  let mut [@@@rename_let "mutName"] r = x;
  let v = !r;
  r := UInt32.add_mod v 1ul;
  !r
}

fn test_stateful (x: UInt32.t)
  returns y : UInt32.t
{
  let mut r = x;
  let [@@@rename_let "statefulName"] v = !r;
  r := v;
  UInt32.add_mod v v
}

(* Two bindings asking for the same name: F* freshens the second one. *)
fn test_dup (x: UInt32.t)
  returns y : UInt32.t
{
  let [@@@rename_let "dupName"] a = UInt32.add_mod x 1ul;
  let [@@@rename_let "dupName"] b = UInt32.add_mod a a;
  UInt32.add_mod a b
}

(* The name need not be a literal in the source, as long as it normalizes to
   one by the time extraction runs. *)
inline_for_extraction noextract
let mk_name (s: string) : string = normalize_term ("computed_" ^ s)

fn test_computed (x: UInt32.t)
  returns y : UInt32.t
{
  let [@@@rename_let (mk_name "name")] v = UInt32.add_mod x 1ul;
  UInt32.add_mod v v
}

fn test_array (x: UInt32.t)
  returns y : UInt32.t
{
  let mut [@@@rename_let "arrayName"] a = [| x; 2sz |];
  a.(0sz) <- UInt32.add_mod x 1ul;
  a.(0sz)
}
