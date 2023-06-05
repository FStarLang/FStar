open Prims
let mk_emb :
  'uuuuu .
    (FStar_Compiler_Range_Type.range -> 'uuuuu -> FStar_Syntax_Syntax.term)
      ->
      (FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option) ->
        FStar_Syntax_Syntax.term ->
          'uuuuu FStar_Syntax_Embeddings_Base.embedding
  =
  fun f ->
    fun g ->
      fun t ->
        let uu___ = FStar_Syntax_Embeddings_Base.term_as_fv t in
        FStar_Syntax_Embeddings_Base.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> f r x)
          (fun x -> fun _norm -> g x) uu___
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range -> 'uuuuu -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings_Base.embed e x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings_Base.id_norm_cb
let unembed' :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun e ->
    fun x ->
      FStar_Syntax_Embeddings_Base.unembed e x
        FStar_Syntax_Embeddings_Base.id_norm_cb
type 'a arg_unembedder =
  FStar_Syntax_Syntax.args ->
    ('a * FStar_Syntax_Syntax.args) FStar_Pervasives_Native.option
let one : 'a . 'a FStar_Syntax_Embeddings_Base.embedding -> 'a arg_unembedder
  =
  fun e ->
    fun args ->
      match args with
      | (t, uu___)::xs ->
          let uu___1 = unembed' e t in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some v ->
               FStar_Pervasives_Native.Some (v, xs))
let op_let_Question :
  'uuuuu 'uuuuu1 .
    'uuuuu FStar_Pervasives_Native.option ->
      ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
        'uuuuu1 FStar_Pervasives_Native.option
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some v -> f v
let op_Less_Star_Greater :
  'a 'b . ('a -> 'b) arg_unembedder -> 'a arg_unembedder -> 'b arg_unembedder
  =
  fun u1 ->
    fun u2 ->
      fun args ->
        let uu___ = u1 args in
        op_let_Question uu___
          (fun uu___1 ->
             match uu___1 with
             | (f, args') ->
                 let uu___2 = u2 args' in
                 op_let_Question uu___2
                   (fun uu___3 ->
                      match uu___3 with
                      | (v, args'') ->
                          let uu___4 = let uu___5 = f v in (uu___5, args'') in
                          FStar_Pervasives_Native.Some uu___4))
let op_Less_Star_Star_Greater :
  'a 'b .
    ('a -> 'b) arg_unembedder ->
      'a FStar_Syntax_Embeddings_Base.embedding -> 'b arg_unembedder
  = fun u1 -> fun u2 -> let uu___ = one u2 in op_Less_Star_Greater u1 uu___
let pure : 'a . 'a -> 'a arg_unembedder =
  fun x -> fun args -> FStar_Pervasives_Native.Some (x, args)
let op_Less_Dollar_Greater :
  'a 'b . ('a -> 'b) -> 'a arg_unembedder -> 'b arg_unembedder =
  fun u1 -> fun u2 -> let uu___ = pure u1 in op_Less_Star_Greater uu___ u2
let op_Less_Dollar_Dollar_Greater :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Syntax_Embeddings_Base.embedding -> 'b arg_unembedder
  =
  fun u1 ->
    fun u2 ->
      let uu___ = pure u1 in
      let uu___1 = one u2 in op_Less_Star_Greater uu___ uu___1
let run :
  'a .
    FStar_Syntax_Syntax.args ->
      'a arg_unembedder -> 'a FStar_Pervasives_Native.option
  =
  fun args ->
    fun u ->
      let uu___ = u args in
      match uu___ with
      | FStar_Pervasives_Native.Some (r, []) ->
          FStar_Pervasives_Native.Some r
      | uu___1 -> FStar_Pervasives_Native.None
let wrap :
  'a .
    (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
      'a arg_unembedder
  =
  fun f ->
    fun args ->
      match args with
      | (t, uu___)::xs ->
          let uu___1 = f t in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some v ->
               FStar_Pervasives_Native.Some (v, xs))