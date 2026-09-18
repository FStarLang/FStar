module RenameLetLib
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Attributes

(* Helpers whose `rename_let` attribute mentions a parameter of the enclosing
   `fn`. The attribute only becomes a string literal once the helper is inlined
   at its call site, which requires the attribute to be substituted along with
   the rest of the body. See RenameLet.fst for the call sites. *)

inline_for_extraction noextract
fn helper_param (name: string) (x: UInt32.t)
  returns y : UInt32.t
{
  let [@@@rename_let name] v = UInt32.add_mod x 1ul;
  UInt32.add_mod v v
}

inline_for_extraction noextract
fn helper_concat (name: string) (x: UInt32.t)
  returns y : UInt32.t
{
  let [@@@rename_let ("positionAfter" ^ name)] v = UInt32.add_mod x 1ul;
  UInt32.add_mod v v
}

inline_for_extraction noextract
fn helper_mut (name: string) (x: UInt32.t)
  returns y : UInt32.t
{
  let mut [@@@rename_let ("ref" ^ name)] r = x;
  let v = !r;
  r := UInt32.add_mod v 1ul;
  !r
}
