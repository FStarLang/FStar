(*  OCaml Format module ported to F#
 *
 *   Copyright (c) 1996--2014 INRIA
 *
 *   This code is distributed under the terms of the
 *   GNU Lesser General Public License (LGPL) v2.1.
 *   See the LICENSE file for details. *)

(* -------------------------------------------------------------------- *)
module FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
type size = int

let inline size_of_int (n : int ) : size = n
let inline int_of_size (s : size) : int  = s

(* -------------------------------------------------------------------- *)
type pp_token =
  | Pp_text of string
  | Pp_break of int * int
  | Pp_begin of int * block_type
  | Pp_end
  | Pp_newline
  | Pp_if_newline

and block_type =
  | Pp_hbox
  | Pp_vbox
  | Pp_hvbox
  | Pp_hovbox
  | Pp_box
  | Pp_fits

type pp_queue_elem = {
  mutable elem_size : size;
  (*---*) token     : pp_token;
  (*---*) length    : int;
}

type pp_scan_elem =
  | Scan_elem of int * pp_queue_elem

type pp_format_elem =
  | Format_elem of block_type * int

(* -------------------------------------------------------------------- *)
type 'a queue_elem =
  | Nil
  | Cons of 'a queue_cell

and 'a queue_cell = {
  mutable head : 'a;
  mutable tail : 'a queue_elem;
}

type 'a queue = {
  mutable insert : 'a queue_elem;
  mutable body   : 'a queue_elem;
}

(* -------------------------------------------------------------------- *)
type formatter = {
  mutable pp_scan_stack : pp_scan_elem list;
  mutable pp_format_stack : pp_format_elem list;
  mutable pp_margin : int;
  mutable pp_min_space_left : int;
  mutable pp_max_indent : int;
  mutable pp_space_left : int;
  mutable pp_current_indent : int;
  mutable pp_is_new_line : bool;
  mutable pp_left_total : int;
  mutable pp_right_total : int;
  mutable pp_curr_depth : int;
  mutable pp_max_boxes : int;
  mutable pp_ellipsis : string;
  mutable pp_out_string : string -> int -> int -> unit;
  mutable pp_out_flush : unit -> unit;
  mutable pp_out_newline : unit -> unit;
  mutable pp_out_spaces : int -> unit;
  mutable pp_queue : pp_queue_elem queue;
}

(* -------------------------------------------------------------------- *)
exception Empty_queue

let make_queue () = { insert = Nil; body = Nil; }

let clear_queue q =
    q.insert <- Nil
    q.body   <- Nil

let add_queue x q =
    let c = Cons { head = x; tail = Nil; }
    match q with
    | { insert = Cons cell; body = _ } ->
        (q.insert <- c; cell.tail <- c)
    | { insert = Nil; body = _ } -> (q.insert <- c; q.body <- c)

let peek_queue =
  function
  | { body = Cons { head = x; tail = _ }; insert = _ } -> x
  | { body = Nil; insert = _ } -> raise Empty_queue

let take_queue = function
  | ({ body = Cons { head = x; tail = tl }; insert = _ } as q) ->
      q.body <- tl;
      if tl = Nil then q.insert <- Nil else ();
      x

  | { body = Nil; insert = _ } ->
      raise Empty_queue

let pp_enqueue state (({ length = len; elem_size = _; token = _ } as token)) =
    state.pp_right_total <- state.pp_right_total + len
    add_queue token state.pp_queue

let pp_clear_queue state =
    state.pp_left_total <- 1
    state.pp_right_total <- 1
    clear_queue state.pp_queue

(* -------------------------------------------------------------------- *)
let pp_infinity = 1000000010

let pp_output_string  state s = state.pp_out_string s 0 (String.length s)
let pp_output_newline state   = state.pp_out_newline ()
let pp_output_spaces  state n = state.pp_out_spaces n

let break_new_line state offset width =
  pp_output_newline state
  state.pp_is_new_line <- true

  let indent      = (state.pp_margin - width) + offset
  let real_indent = min state.pp_max_indent indent

  state.pp_current_indent <- real_indent
  state.pp_space_left <- state.pp_margin - state.pp_current_indent
  pp_output_spaces state state.pp_current_indent

let break_line state width = break_new_line state 0 width

let break_same_line state width =
  state.pp_space_left <- state.pp_space_left - width
  pp_output_spaces state width

let pp_force_break_line state =
  match state.pp_format_stack with
  | Format_elem (bl_ty, width) :: _ ->
      if width > state.pp_space_left then
        match bl_ty with
        | Pp_fits -> ()
        | Pp_hbox -> ()
        | Pp_vbox | Pp_hvbox | Pp_hovbox | Pp_box -> break_line state width

  | [] -> pp_output_newline state

let pp_skip_token state =
  match take_queue state.pp_queue with
  | { elem_size = size; length = len; token = _ } ->
       state.pp_left_total <- state.pp_left_total - len
       state.pp_space_left <- state.pp_space_left + (int_of_size size)

(* -------------------------------------------------------------------- *)
let format_pp_token state size tk =
  match tk with
  | Pp_text s ->
      state.pp_space_left <- state.pp_space_left - size
      pp_output_string state s
      state.pp_is_new_line <- false

  | Pp_begin (off, ty) ->
      let insertion_point = state.pp_margin - state.pp_space_left

      if insertion_point > state.pp_max_indent then
        pp_force_break_line state;

      let offset = state.pp_space_left - off 
      let bl_type =
        match ty with
        | Pp_vbox -> Pp_vbox
        | Pp_hbox | Pp_hvbox | Pp_hovbox | Pp_box | Pp_fits ->
            if size > state.pp_space_left then ty else Pp_fits
      state.pp_format_stack <- (Format_elem (bl_type, offset)) :: state.pp_format_stack

  | Pp_end ->
      match state.pp_format_stack with
      | _ :: ls -> state.pp_format_stack <- ls
      | [] -> ()

  | Pp_newline ->
      match state.pp_format_stack with
      | Format_elem (_, width) :: _ -> break_line state width
      | [] -> pp_output_newline state

  | Pp_if_newline ->
      if state.pp_current_indent <> (state.pp_margin - state.pp_space_left) then
        pp_skip_token state

  | Pp_break (n, off) ->
      match state.pp_format_stack with
      | Format_elem (ty, width) :: _ ->
          match ty with
          | Pp_hovbox ->
              if size > state.pp_space_left
              then break_new_line state off width
              else break_same_line state n

          | Pp_box ->
              if state.pp_is_new_line then
                break_same_line state n
              elif size > state.pp_space_left then
                break_new_line state off width
              elif state.pp_current_indent > ((state.pp_margin - width) + off) then
                break_new_line state off width
              else
                break_same_line state n

          | Pp_hvbox -> break_new_line state off width
          | Pp_fits -> break_same_line state n
          | Pp_vbox -> break_new_line state off width
          | Pp_hbox -> break_same_line state n
  
      | [] -> ()

(* -------------------------------------------------------------------- *)
let rec advance_loop state =
  match peek_queue state.pp_queue with
  | { elem_size = size; token = tok; length = len } ->
      let size = int_of_size size

      if
        not
          (size < 0 && state.pp_right_total - state.pp_left_total < state.pp_space_left)
      then
        ignore (take_queue state.pp_queue)
        format_pp_token state (if size < 0 then pp_infinity else size) tok
        state.pp_left_total <- len + state.pp_left_total
        advance_loop state

let advance_left state =
  try advance_loop state with Empty_queue -> ()

let enqueue_advance state tok = (pp_enqueue state tok; advance_left state)

let make_queue_elem size tok len =
  { elem_size = size; token = tok; length = len; }

let enqueue_string_as state size s =
  let len = int_of_size size
  enqueue_advance state (make_queue_elem size (Pp_text s) len)

let enqueue_string state s =
  let len = String.length s
  enqueue_string_as state (size_of_int len) s

let scan_stack_bottom =
  let q_elem = make_queue_elem (size_of_int (-1)) (Pp_text "") 0
  [ Scan_elem ((-1), q_elem) ]

let clear_scan_stack state = state.pp_scan_stack <- scan_stack_bottom

let set_size state ty =
  match state.pp_scan_stack with
  | Scan_elem (left_tot, (({ elem_size = size; token = tok; length = _ } as queue_elem))) :: t ->
      let size = int_of_size size

      if left_tot < state.pp_left_total then
        clear_scan_stack state
      else
        match tok with
        | Pp_break (_, _) ->
          if ty then
            queue_elem.elem_size <- size_of_int (state.pp_right_total + size)
            state.pp_scan_stack <- t

        | Pp_begin (_, _) ->
          if not ty then
            queue_elem.elem_size <- size_of_int (state.pp_right_total + size);
            state.pp_scan_stack <- t

        | Pp_text _ | Pp_end | Pp_newline | Pp_if_newline -> ()

  | [] -> ()

let scan_push state b tok =
  pp_enqueue state tok
  if b then set_size state true else ()
  state.pp_scan_stack <- (Scan_elem (state.pp_right_total, tok)) :: state.pp_scan_stack

(* -------------------------------------------------------------------- *)
let pp_open_box_gen state indent br_ty =
  state.pp_curr_depth <- state.pp_curr_depth + 1
  if state.pp_curr_depth < state.pp_max_boxes then
    let elem =
      make_queue_elem (size_of_int (- state.pp_right_total))
        (Pp_begin (indent, br_ty)) 0
    scan_push state false elem
  else
     if state.pp_curr_depth = state.pp_max_boxes then
       enqueue_string state state.pp_ellipsis

let pp_open_sys_box state = pp_open_box_gen state 0 Pp_hovbox

(* -------------------------------------------------------------------- *)
let pp_close_box state () =
  if state.pp_curr_depth > 1 then
    if state.pp_curr_depth < state.pp_max_boxes then
      pp_enqueue state { elem_size = size_of_int 0; token = Pp_end; length = 0; }
      set_size state true
      set_size state false
    state.pp_curr_depth <- state.pp_curr_depth - 1

(* -------------------------------------------------------------------- *)
let pp_rinit state =
  pp_clear_queue state
  clear_scan_stack state
  state.pp_format_stack <- []
  state.pp_current_indent <- 0
  state.pp_curr_depth <- 0
  state.pp_space_left <- state.pp_margin
  pp_open_sys_box state

let pp_flush_queue state b =
  while state.pp_curr_depth > 1 do pp_close_box state () done
  state.pp_right_total <- pp_infinity
  advance_left state
  if b then pp_output_newline state else ()
  pp_rinit state

(* -------------------------------------------------------------------- *)
let pp_print_as_size state size s =
  if state.pp_curr_depth < state.pp_max_boxes then
    enqueue_string_as state size s

let pp_print_as state isize s =
  pp_print_as_size state (size_of_int isize) s

let pp_print_string state s =
  pp_print_as state (String.length s) s

let pp_print_int state (i : int) =
  pp_print_string state (i.ToString ())

let pp_print_float state (f : float) =
  pp_print_string state (f.ToString ())

let pp_print_char state (c : char) =
    pp_print_as state 1 (string c)

(* -------------------------------------------------------------------- *)
let pp_open_hbox   state ()     = pp_open_box_gen state 0 Pp_hbox
let pp_open_vbox   state indent = pp_open_box_gen state indent Pp_vbox
let pp_open_hvbox  state indent = pp_open_box_gen state indent Pp_hvbox
let pp_open_hovbox state indent = pp_open_box_gen state indent Pp_hovbox
let pp_open_box    state indent = pp_open_box_gen state indent Pp_box

(* -------------------------------------------------------------------- *)
let pp_print_newline state () =
  pp_flush_queue state true
  state.pp_out_flush ()

let pp_print_flush state () =
  pp_flush_queue state false
  state.pp_out_flush ()

(* -------------------------------------------------------------------- *)
let pp_force_newline state () =
  if state.pp_curr_depth < state.pp_max_boxes then
    enqueue_advance state (make_queue_elem (size_of_int 0) Pp_newline 0)

(* -------------------------------------------------------------------- *)
let pp_print_if_newline state () =
  if state.pp_curr_depth < state.pp_max_boxes then
    enqueue_advance state (make_queue_elem (size_of_int 0) Pp_if_newline 0)

(* -------------------------------------------------------------------- *)
let pp_print_break state width offset =
  if state.pp_curr_depth < state.pp_max_boxes then
    let elem =
       make_queue_elem (size_of_int (- state.pp_right_total))
         (Pp_break (width, offset)) width
    scan_push state true elem

(* -------------------------------------------------------------------- *)
let pp_print_space state () = pp_print_break state 1 0
let pp_print_cut   state () = pp_print_break state 0 0

(* -------------------------------------------------------------------- *)
let pp_set_max_boxes  state n  = if n > 1 then state.pp_max_boxes <- n else ()
let pp_get_max_boxes  state () = state.pp_max_boxes
let pp_over_max_boxes state () = state.pp_curr_depth = state.pp_max_boxes

(* -------------------------------------------------------------------- *)
let pp_set_ellipsis_text state s  = state.pp_ellipsis <- s
let pp_get_ellipsis_text state () = state.pp_ellipsis

(* -------------------------------------------------------------------- *)
let pp_limit n = if n < pp_infinity then n else pp_infinity-1

let pp_set_min_space_left state n =
  if n >= 1 then
    let n = pp_limit n
    state.pp_min_space_left <- n
    state.pp_max_indent <- state.pp_margin - state.pp_min_space_left
    pp_rinit state

(* -------------------------------------------------------------------- *)
let pp_set_max_indent state n =
  pp_set_min_space_left state (state.pp_margin - n)

let pp_get_max_indent state () = state.pp_max_indent

(* -------------------------------------------------------------------- *)
let pp_set_margin state n =
  if n >= 1 then
    let n = pp_limit n
    state.pp_margin <- n
    let new_max_indent =
      if state.pp_max_indent <= state.pp_margin then
        state.pp_max_indent
      else
        max 1
          (max (state.pp_margin - state.pp_min_space_left)
            (state.pp_margin / 2))
    pp_set_max_indent state new_max_indent

let pp_get_margin state () = state.pp_margin

(* -------------------------------------------------------------------- *)
type formatter_out_functions = {
  out_string  : string -> int -> int -> unit;
  out_flush   : unit -> unit;
  out_newline : unit -> unit;
  out_spaces  : int -> unit
}

(* -------------------------------------------------------------------- *)
let display_newline state () = state.pp_out_string "\n" 0 1

let blank_line = System.String (' ', 80)

let rec display_blanks state n =
  if n > 0 then
    if n <= 80 then
      state.pp_out_string blank_line 0 n
    else
      state.pp_out_string blank_line 0 80
      display_blanks state (n - 80)

(* -------------------------------------------------------------------- *)
let pp_make_formatter f g h i =
  let pp_q    = make_queue ()
  let sys_tok = make_queue_elem (size_of_int (-1)) (Pp_begin (0, Pp_hovbox)) 0

  add_queue sys_tok pp_q
  
  let sys_scan_stack = (Scan_elem (1, sys_tok)) :: scan_stack_bottom

  { pp_scan_stack = sys_scan_stack;
    pp_format_stack = [];
    pp_margin = 78;
    pp_min_space_left = 10;
    pp_max_indent = 78 - 10;
    pp_space_left = 78;
    pp_current_indent = 0;
    pp_is_new_line = true;
    pp_left_total = 1;
    pp_right_total = 1;
    pp_curr_depth = 1;
    pp_max_boxes = System.Int32.MaxValue;
    pp_ellipsis = ".";
    pp_out_string = f;
    pp_out_flush = g;
    pp_out_newline = h;
    pp_out_spaces = i;
    pp_queue = pp_q; }

(* -------------------------------------------------------------------- *)
let make_formatter output flush =
  let ppf = pp_make_formatter output flush ignore ignore
  ppf.pp_out_newline <- display_newline ppf
  ppf.pp_out_spaces  <- display_blanks ppf
  ppf

let formatter_of_text_writter (oc: System.IO.TextWriter)  =
  let output (s : string) i j = oc.Write (s.Substring (i, j)) in
  make_formatter output oc.Flush

(* -------------------------------------------------------------------- *)
let open_box    fmt i = pp_open_box    fmt i
let open_hbox   fmt   = pp_open_hbox   fmt ()
let open_vbox   fmt i = pp_open_vbox   fmt i
let open_hvbox  fmt i = pp_open_hvbox  fmt i
let open_hovbox fmt i = pp_open_hovbox fmt i

let closebox fmt = pp_close_box fmt ()

let print_space   fmt     = pp_print_space   fmt ()
let print_cut     fmt     = pp_print_cut     fmt ()
let print_brk     fmt i j = pp_print_break   fmt i j
let print_flush   fmt     = pp_print_flush   fmt ()
let print_newline fmt     = pp_print_newline fmt ()

(* -------------------------------------------------------------------- *)
type value = Char of char | String of string | Int of int | Float of float

let (<<) fmt = function
  | Char   c -> pp_print_char   fmt c
  | String s -> pp_print_string fmt s
  | Int    i -> pp_print_int    fmt i
  | Float  d -> pp_print_float  fmt d
