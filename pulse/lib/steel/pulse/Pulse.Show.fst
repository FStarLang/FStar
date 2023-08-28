module Pulse.Show

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Pulse.Typing
open Pulse.Syntax.Base
open Pulse.Syntax.Printer

class tac_showable (a:Type) = {
  show : a -> Tac string;
}

instance _ : tac_showable string = {
  show = (fun s -> s);
}

instance _ : tac_showable unit = {
  show = (fun () -> "");
}

instance _ : tac_showable bool = {
  show = (fun b -> string_of_bool b);
}

instance _ : tac_showable int = {
  show = (fun b -> string_of_int b);
}

instance showable_option (a:Type) (_ : tac_showable a) : tac_showable (option a) = {
  show = (function None -> "None"
                 | Some v -> "Some " ^ show v);
}

instance showable_list (a:Type) (_ : tac_showable a) : tac_showable (list a) = {
  show = string_of_list show;
}

instance _ : tac_showable ctag = {
  show = (fun t -> ctag_to_string t);
}

instance _ : tac_showable term = {
  show = term_to_string;
}
instance _ : tac_showable universe = {
  show = (fun t -> univ_to_string t);
}
instance _ : tac_showable comp = {
  show = comp_to_string;
}
instance _ : tac_showable env = {
  show = env_to_string;
}

instance _ : tac_showable post_hint_t = {
  show = (fun (h:post_hint_t) ->
    "{" ^
      "g = " ^ show h.g ^ "; " ^
      "ctag_hint = " ^ show h.ctag_hint ^ "; " ^
      "ret_ty = " ^ show h.ret_ty ^ "; " ^
      "u = " ^ show h.u ^ "; " ^
      "post = " ^ show h.post ^ "; " ^
    "}")
}
