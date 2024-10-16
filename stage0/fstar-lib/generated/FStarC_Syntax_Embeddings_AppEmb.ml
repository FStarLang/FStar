open Prims
type 'a appemb =
  FStarC_Syntax_Syntax.args ->
    ('a * FStarC_Syntax_Syntax.args) FStar_Pervasives_Native.option
let one : 'a . 'a FStarC_Syntax_Embeddings_Base.embedding -> 'a appemb =
  fun e ->
    fun args ->
      match args with
      | (t, uu___)::xs ->
          let uu___1 =
            FStarC_Syntax_Embeddings_Base.try_unembed e t
              FStarC_Syntax_Embeddings_Base.id_norm_cb in
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
  'a 'b . ('a -> 'b) appemb -> 'a appemb -> 'b appemb =
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
    ('a -> 'b) appemb ->
      'a FStarC_Syntax_Embeddings_Base.embedding -> 'b appemb
  = fun u1 -> fun u2 -> let uu___ = one u2 in op_Less_Star_Greater u1 uu___
let pure : 'a . 'a -> 'a appemb =
  fun x -> fun args -> FStar_Pervasives_Native.Some (x, args)
let op_Less_Dollar_Greater : 'a 'b . ('a -> 'b) -> 'a appemb -> 'b appemb =
  fun u1 -> fun u2 -> let uu___ = pure u1 in op_Less_Star_Greater uu___ u2
let op_Less_Dollar_Dollar_Greater :
  'a 'b .
    ('a -> 'b) -> 'a FStarC_Syntax_Embeddings_Base.embedding -> 'b appemb
  =
  fun u1 ->
    fun u2 ->
      let uu___ = pure u1 in
      let uu___1 = one u2 in op_Less_Star_Greater uu___ uu___1
let run :
  'a .
    FStarC_Syntax_Syntax.args ->
      'a appemb -> 'a FStar_Pervasives_Native.option
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
    (FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
      'a appemb
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