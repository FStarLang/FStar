module Externs
open FStar.All
open FStar.IO
open FStar.Attributes

(* Custom extraction rules declared in F* source (section 8 of
   doc/ref/custard.md), rather than hardcoded in the compiler or registered by
   a plugin. *)

(* No F* definition at all: the symbol is realized by hand in the target
   language.  Without the attribute this would extract as a call to
   [Externs.show_int], which nothing defines. *)
[@@custard_extern "Prims.string_of_int"]
assume val show_int (x:int) : string

(* The C header, which the direct-to-C backend needs and the karamel one
   ignores, rides along on a second attribute. *)
[@@custard_extern "Prims.strcat"; custard_c_header "prims.h"]
assume val cat (s1:string) (s2:string) : string

(* A single-constructor, single-field type would normally collapse to its
   field (section 5.2).  [custard_opaque] says its representation is fixed
   elsewhere, so the collapse must not happen. *)
[@@custard_opaque]
type handle = | Handle of int

let peek (h:handle) : int = let Handle n = h in n

let main () : ML unit =
  print_string (cat (show_int (peek (Handle 42))) "!");
  print_string "\n"
