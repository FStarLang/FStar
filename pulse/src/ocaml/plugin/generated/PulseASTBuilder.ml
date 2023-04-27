open Prims
let extension_parser :
  'uuuuu .
    'uuuuu ->
      Prims.string ->
        FStar_Compiler_Range.range ->
          (FStar_Parser_AST_Util.error_message, FStar_Parser_AST.decl')
            FStar_Pervasives.either
  =
  fun ctx ->
    fun contents ->
      fun rng ->
        let uu___ = Pulse_Parser.parse contents rng in
        match uu___ with
        | FStar_Pervasives.Inr (err, r) ->
            FStar_Pervasives.Inl
              {
                FStar_Parser_AST_Util.message = err;
                FStar_Parser_AST_Util.range = r
              }
        | FStar_Pervasives.Inl pulse_ast ->
            FStar_Pervasives.Inr (pulse_ast.FStar_Parser_AST.d)
let (uu___9 : unit) =
  FStar_Parser_AST_Util.register_extension_parser "pulse" extension_parser