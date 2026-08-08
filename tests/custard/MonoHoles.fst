module MonoHoles
open FStar.All

(* A dictionary whose *code* is static but whose *data* is not: 'tag' is a
   runtime value, and 'show' is the same function in every instance.  This is
   the shape of FStarC.Syntax.Embeddings.set_type, which builds an embedding
   out of a term it unembedded at runtime. *)
noeq type printer (a:Type) = { tag : int; pr : a -> string }

let set_tag (#a:Type) (t:int) (p:printer a) : printer a = { p with tag = t }

let p_int : printer int = { tag = 0; pr = (fun x -> string_of_int x) }

let render (#a:Type) ([@@@monomorphize] p : printer a) (x:a) : ML string =
  string_of_int p.tag ^ ":" ^ p.pr x

(* 'n' is an honest runtime value, so the dictionary reaching render's
   monomorphized binder mentions it.  Section 3.2c abstracts it out and passes
   it at runtime instead of rejecting the call. *)
let describe (n:int) (x:int) : ML string =
  render (set_tag n p_int) x

(* A closure over a runtime value, which is the same mechanism. *)
let twice ([@@@monomorphize] f : int -> int) (x:int) : int = f (f x)

let bump (k:int) (x:int) : int = twice (fun y -> y + k) x

let main () : ML unit =
  FStar.IO.print_string (describe 7 42);
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_int (bump 3 10));
  FStar.IO.print_string "\n"
