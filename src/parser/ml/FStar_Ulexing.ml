// A custom version of Ulexing enhanced with
// lc, bol and fname position tracking
// and specialized for UTF-8 string inputs
// (the parser driver aloways reads whole files)

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

// N.B. the offsets are for interactive mode
// we want to ble able to interpret a fragment as if it was part
// of a larger file and report absolute error positions
let create (s:string) fn loffset coffset =
  let a = Utf8.to_int_array s 0 (String.length s) in
  let start_p = {
    L.pos_fname = FStar_Range.encode_file fn;
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

let next b =
  if b.pos = b.len then -1
  else
    let c = b.buf.(b.pos) in
    (lexbuf.pos <- lexbuf.pos + 1; c)

let new_line b =
  b.cur_p <- { b.cur_p with
    pos_lnum = pos_lnum + 1;
    pos_bol = pos_cnum;
    pos_cnum = 0 }

let range b = (b.start_p, b.cur_p)

let lexeme lexbuf = 
  Utf8.from_int_array lexbuf.buf lexbuf.start (lexbuf.pos - lexbuf.start)

let lookahead b pos =
  if b.len <= pos then ""
  else Utf8.from_int_array b.buf pos (b.len - pos)

let source_file b =
  b.cur_p.Lexing.pos_fname

let current_line b =
  b.cur_p.Lexing.pos_lnum