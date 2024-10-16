module LowStar.Comment
open FStar.HyperStack.ST

/// `comment_gen before body after` extracts to KaRaMeL AST
/// `EComment (before, body', after)` (where `body` extracts
/// to `body'`), and so ultimately extracts to the
/// corresponding C implementation of `body` enclosed with
/// two comments `/* before */` and `/* after */`.
/// `before` and `after` *must be* string literals.
/// However, `comment_gen` is not enough to produce
/// standalone comments, because if `body` is a pure unit
/// expression, then F\*, not KaRaMeL, will erase it at
/// extraction.

val comment_gen: #t: Type -> before: string -> body: t -> after: string -> Pure t
  (requires (True))
  (ensures (fun res -> res == body))

/// `comment s` extracts to KaRaMeL AST
/// `EStandaloneComment s`, and so ultimately extracts to
/// the standalone C comment `/* s */`.  `s` *must be*
/// a string literal.

val comment
  (s: string)
: Stack unit
  (requires (fun _ -> True))
  (ensures (fun h _ h' -> h == h'))
