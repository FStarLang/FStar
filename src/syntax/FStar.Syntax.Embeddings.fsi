﻿#light "off"
module FStar.Syntax.Embeddings

open FStar.All
open FStar.Syntax.Syntax

val embed_unit   : unit -> term
val unembed_unit : term -> unit

val embed_bool   : bool -> term
val unembed_bool : term -> bool

val embed_int   : int -> term
val unembed_int : term -> int

val embed_string   : string -> term
val unembed_string : term -> string

val embed_pair   : ('a -> term) -> term -> ('b -> term) -> term -> ('a*'b) -> term
val unembed_pair : (term -> 'a) -> (term -> 'b) -> term -> 'a*'b

val embed_option   : ('a -> term) -> term -> option<'a> -> term
val unembed_option : (term -> 'a) -> term -> option<'a>

val embed_list   : ('a -> term) -> term -> list<'a> -> term
val unembed_list : (term -> 'a) -> term -> list<'a>

val embed_string_list   : list<string> -> term
val unembed_string_list : term -> list<string>