(* A polymorphic *value* (section 5.0).

   'box_empty' has no binders in the source, so generalization gives it one --
   a type binder -- and section 5.0 then deletes it, which would turn the
   definition into a value.  Mono.keep_thunk declines: an OCaml 'let' whose
   right-hand side is not a syntactic value does not generalize, so the binder
   is put back.

   What has to hold is that the two sides then agree.  The binder is kept, but
   what it stands for is a *type*, and a type is not a term: the call site has
   to pass a placeholder rather than the type argument.  Passing the type
   argument happens to work where it is a concrete type -- it prints as
   'Obj.magic ()' -- and emits a reference to a type variable in value position
   where it is not, which does not compile at all. *)
module PolyVal

open FStar.All

type box a = { items : list a; tag : string }

let box_empty = { items = []; tag = "" }

let add (#a:Type) (x:a) (b : box a) : box a = { b with items = x :: b.items }

let rec count (#a:Type) (xs : list a) : int =
  match xs with [] -> 0 | _ :: t -> 1 + count t

(* The call whose type argument is a type *variable*: 'a' is bound by 'use_it',
   not known here. *)
let use_it (#a:Type) (x:a) : int =
  let b = add x box_empty in
  count b.items

(* And one whose type argument is concrete. *)
let use_int () : int = count (add 1 box_empty).items

let main () : ML unit =
  FStar.IO.print_string (string_of_int (use_it 1 + use_it "x" + use_int ()));
  FStar.IO.print_string "\n"
