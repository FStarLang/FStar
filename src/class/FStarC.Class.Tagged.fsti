module FStarC.Class.Tagged

open FStarC.Effect

(* This class is meant to print the constructor of a term.
It replaces tag_of_term and tag_of_sigelt. *)
class tagged (a:Type) = {
  tag_of : a -> ML string;
}
