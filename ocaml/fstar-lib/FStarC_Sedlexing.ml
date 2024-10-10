(**
A custom version of Sedlexing enhanced with
lc, bol and fname position tracking and
specialized for UTF-8 string inputs
(the parser driver always reads whole files)
**)

exception Error

module L = Lexing
type pos = L.position

type lexbuf = {
  buf: int array;
  len: int;

  mutable cur: int;
  mutable cur_p: pos;
  mutable start: int;
  mutable start_p: pos;

  mutable mark: int;
  mutable mark_p: pos;
  mutable mark_val: int;
}

let get_buf lb = lb.buf
let get_cur lb = lb.cur
let get_start lb = lb.start

(* N.B. the offsets are for interactive mode
   we want to ble able to interpret a fragment as if it was part
   of a larger file and report absolute error positions *)
let create (s:string) fn loffset coffset =
  let a = FStarC_Parser_Utf8.to_int_array s 0 (String.length s) in
  let start_p = {
    L.pos_fname = fn;
    L.pos_cnum = coffset;
    L.pos_bol  = 0;
    L.pos_lnum = loffset; }
  in {
    buf = a;
    len = Array.length a;

    cur = 0;
    cur_p = start_p;

    start = 0;
    start_p = start_p;

    mark = 0;
    mark_p = start_p;
    mark_val = 0;
  }

let current_pos b = b.cur_p
  
let start b =
  b.mark <- b.cur;
  b.mark_val <- (-1);
  b.mark_p <- b.cur_p;
  b.start <- b.cur;
  b.start_p <- b.cur_p

let mark b i =
  b.mark <- b.cur;
  b.mark_p <- b.cur_p;
  b.mark_val <- i

let backtrack b =
  b.cur <- b.mark;
  b.cur_p <- b.mark_p;
  b.mark_val

type snap = int * pos

let snapshot b = b.start, b.start_p
let restore_snapshot b (cur, cur_p) =
  b.cur <- cur;
  b.cur_p <- cur_p

let next b =
  if b.cur = b.len then None
  else
    let c = b.buf.(b.cur) in
    (b.cur <- b.cur + 1;
    b.cur_p <- {b.cur_p with L.pos_cnum = b.cur_p.L.pos_cnum + 1}; Some (Uchar.of_int c))

let new_line b =
  b.cur_p <- { b.cur_p with
    L.pos_lnum = b.cur_p.L.pos_lnum + 1;
    L.pos_bol = b.cur_p.L.pos_cnum;
  }

let range b = (b.start_p, b.cur_p)

let ulexeme lexbuf =
  Array.sub lexbuf.buf lexbuf.start (lexbuf.cur - lexbuf.start)

let rollback b =
  b.cur <- b.start;
  b.cur_p <- b.start_p

let lexeme lexbuf =
  FStarC_Parser_Utf8.from_int_array lexbuf.buf lexbuf.start (lexbuf.cur - lexbuf.start)

let lookahead b pos =
  if b.len <= pos then ""
  else FStarC_Parser_Utf8.from_int_array b.buf pos (b.len - pos)

let source_file b =
  b.cur_p.L.pos_fname

let current_line b =
  b.cur_p.Lexing.pos_lnum

(* Since sedlex 2.4, we need to expose Sedlexing.__private_next_int
   (see #2343)

   From https://github.com/ocaml-communi-ty/sedlex/blob/268c553f474457574e22701679d68f66aa771551/src/lib/sedlexing.mli#L154-L161
   [next] and [__private__next_int] have the same doc description,
   the only difference is the return type *)
let __private__next_int b =
  match next b with
  | Some v -> Uchar.to_int v
  | None -> -1
