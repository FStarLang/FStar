module EntryEffect

(* [--custard_entry_module] roots whatever of a module is code, and a
   definition whose result is uninformative is code exactly when computing it
   does something.  [check] returns [unit] in [ML], nothing in the module
   calls it, and it is what hand-written OCaml calls -- EverParse's
   [Ast.check_reserved_identifier] is this shape, and it used to be dropped as
   though it were a specification.  [nothing] and [spec] are specifications
   and still are.

   On the OCaml backend a polymorphic helper is rooted too: OCaml has type
   variables, and hand-written code may name [pick] as legitimately as
   [check].

   [report] has no definition.  An external reference to it from inside the
   module being written would name the output file itself, so it becomes a
   stub that fails when called, as it always did under the ML backend. *)

open FStar.All

assume val report : string -> ML unit

let check (n : nat) : ML unit =
  if n > 100 then report "too big"

let nothing (n : nat) : unit = ()

let spec (n : nat) : GTot nat = n + 1

let pick (#a : Type) (b : bool) (x y : a) : a = if b then x else y
