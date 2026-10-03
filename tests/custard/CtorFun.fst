module CtorFun
open FStar.All
open FStar.IO

module U32 = FStar.UInt32

/// A constructor used as a function, of a type that collapses.
///
/// §5.2 collapses a one-constructor, one-field type into its payload, so the
/// constructor is not a name in the emitted code at all.  `Extract` records a
/// constructor reference as an [ECtor] carrying whatever arguments the
/// application node had, so [app W] arrives at the layout pass with none ---
/// and a collapsed constructor with no argument has no payload to collapse
/// to.  It came out as [()], which the higher-order call then applied, and the
/// OCaml compiler reported it about generated code.  The layout pass now
/// eta-expands an under-applied constructor before it rewrites one, so the
/// reference is the identity function it denotes.
///
/// [FStarC.Syntax.Syntax.comp'] is the case that found this: it has one
/// constructor, and [FStarC.Syntax.VisitM] writes [Comp <$> on_sub_comp_typ ct].

type wrap = | W of U32.t

let unwrap (w : wrap) : U32.t = let W x = w in x

let app (f : U32.t -> wrap) (x : U32.t) : U32.t = unwrap (f x)

/// The same use of a constructor whose type does *not* collapse: two
/// constructors, so it is a real function in the output too.
type two = | A of U32.t | B of U32.t

let un2 (t : two) : U32.t = match t with | A x -> x | B x -> x

let app2 (f : U32.t -> two) (x : U32.t) : U32.t = un2 (f x)

/// Partially applied: one argument given, one still missing.  Declared with
/// the arrow syntax, since [| Both of a & b] is one field of pair type
/// (section 5.7) and so cannot be under-applied.
type both = | Both : U32.t -> U32.t -> both

let unboth (b : both) : U32.t = match b with | Both x y -> U32.add_mod x y

let app3 (f : U32.t -> both) (x : U32.t) : U32.t = unboth (f x)

let main () : ML unit =
  print_string (U32.to_string (app W 1ul));
  print_string (U32.to_string (app2 A 2ul));
  print_string (U32.to_string (app2 B 3ul));
  print_string (U32.to_string (app3 (Both 4ul) 5ul));
  print_string "\n"
