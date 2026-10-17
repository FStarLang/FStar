(* Model implementation of FStar.Range: verified, but never extracted (the real implementation is native). *)
module FStar.Range

type range : eqtype = {
  file : string;
  from_line : int;
  from_col : int;
  to_line : int;
  to_col : int;
}

let range_0 = { file = "dummy"; from_line = 0; from_col = 0; to_line = 0; to_col = 0 }

let mk_range file from_line from_col to_line to_col =
  { file; from_line; from_col; to_line; to_col }

let pos_leq (l1 c1 l2 c2 : int) : bool = l1 < l2 || (l1 = l2 && c1 <= c2)

let join_range r1 r2 =
  if r1.file <> r2.file then r2
  else
    let (fl, fc) = if pos_leq r1.from_line r1.from_col r2.from_line r2.from_col
                   then (r1.from_line, r1.from_col) else (r2.from_line, r2.from_col) in
    let (tl, tc) = if pos_leq r1.to_line r1.to_col r2.to_line r2.to_col
                   then (r2.to_line, r2.to_col) else (r1.to_line, r1.to_col) in
    mk_range r1.file fl fc tl tc

let explode r = (r.file, r.from_line, r.from_col, r.to_line, r.to_col)
