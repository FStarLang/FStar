(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Show

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Pulse.Typing
open Pulse.Syntax.Base
open Pulse.Syntax.Printer

instance tac_showable_string : tac_showable string = {
  show = (fun s -> s);
}

instance tac_showable_unit : tac_showable unit = {
  show = (fun () -> "()");
}

instance tac_showable_bool : tac_showable bool = {
  show = (fun b -> string_of_bool b);
}

instance tac_showable_int : tac_showable int = {
  show = (fun b -> string_of_int b);
}

instance tac_showable_option (a:Type) (tac_showable_a : tac_showable a) : tac_showable (option a) = {
  show = (function None -> "None"
                 | Some v -> "Some " ^ show v);
}

instance tac_showable_list (a:Type) (tac_showable_a : tac_showable a) : tac_showable (list a) = {
  show = string_of_list show;
}

instance tac_showable_ctag : tac_showable ctag = {
  show = (fun t -> ctag_to_string t);
}

instance tac_showable_term : tac_showable term = {
  show = term_to_string;
}
instance tac_showable_st_term : tac_showable st_term = {
  show = st_term_to_string;
}
instance tac_showable_universe : tac_showable universe = {
  show = (fun t -> univ_to_string t);
}
instance tac_showable_comp : tac_showable comp = {
  show = comp_to_string;
}
instance tac_showable_env : tac_showable env = {
  show = env_to_string;
}
instance tac_showable_observability : tac_showable observability = {
  show = (fun o -> observability_to_string o)
}
instance tac_showable_effect_annot : tac_showable effect_annot = {
  show = effect_annot_to_string
} 

instance tac_showable_post_hint_t : tac_showable post_hint_t = {
  show = (fun (h:post_hint_t) ->
    "{" ^
      "g = " ^ show h.g ^ "; " ^
      "effect_annot = " ^ show h.effect_annot ^ "; " ^
      "ret_ty = " ^ show h.ret_ty ^ "; " ^
      "u = " ^ show h.u ^ "; " ^
      "post = " ^ show h.post ^ "; " ^
    "}")
}
instance tac_showable_namedv : tac_showable namedv = {
  show = (fun b -> namedv_to_string b);
}

instance tac_showable_r_term : tac_showable Reflection.term = {
  show = Tactics.term_to_string;
}

instance tac_showable_range : tac_showable Range.range = {
  show = Tactics.range_to_string;
}

instance tac_showable_tuple2 (a b : Type) (_ : tac_showable a) (_ : tac_showable b) : tac_showable (a & b) = {
  show = (fun (x, y) -> "(" ^ show x ^ ", " ^ show y ^ ")");
}

instance tac_showable_tuple3 (a b c : Type) (_ : tac_showable a) (_ : tac_showable b) (_ : tac_showable c) : tac_showable (a & b & c) = {
  show = (fun (x, y, z) -> "(" ^ show x ^ ", " ^ show y ^ ", " ^ show z ^ ")");
}

instance tac_showable_tuple4 (a b c d : Type) (_ : tac_showable a) (_ : tac_showable b) (_ : tac_showable c) (_ : tac_showable d) : tac_showable (a & b & c & d) = {
  show = (fun (x, y, z, w) -> "(" ^ show x ^ ", " ^ show y ^ ", " ^ show z ^ ", " ^ show w ^ ")");
}

instance tac_showable_tuple5 (a b c d e : Type) (_ : tac_showable a) (_ : tac_showable b) (_ : tac_showable c) (_ : tac_showable d) (_ : tac_showable e) : tac_showable (a & b & c & d & e) = {
  show = (fun (x, y, z, w, v) -> "(" ^ show x ^ ", " ^ show y ^ ", " ^ show z ^ ", " ^ show w ^ ", " ^ show v ^ ")");
}

instance tac_showable_tuple6 (a b c d e f : Type) (_ : tac_showable a) (_ : tac_showable b) (_ : tac_showable c) (_ : tac_showable d) (_ : tac_showable e) (_ : tac_showable f) : tac_showable (a & b & c & d & e & f) = {
  show = (fun (x, y, z, w, v, u) -> "(" ^ show x ^ ", " ^ show y ^ ", " ^ show z ^ ", " ^ show w ^ ", " ^ show v ^ ", " ^ show u ^ ")");
}

instance tac_showable_tuple7 (a b c d e f g : Type) (_ : tac_showable a) (_ : tac_showable b) (_ : tac_showable c) (_ : tac_showable d) (_ : tac_showable e) (_ : tac_showable f) (_ : tac_showable g) : tac_showable (a & b & c & d & e & f & g) = {
  show = (fun (x, y, z, w, v, u, t) -> "(" ^ show x ^ ", " ^ show y ^ ", " ^ show z ^ ", " ^ show w ^ ", " ^ show v ^ ", " ^ show u ^ ", " ^ show t ^ ")");
}
