open Prims
let int1 m f ua em r args =
  match args with
  | (a,uu____61)::[] ->
      let uu____86 =
        let uu____87 = let uu____88 = ua a in f uu____88 in em uu____87 in
      FStar_Pervasives_Native.Some uu____86
  | uu____89 -> FStar_Pervasives_Native.None
let int2 m f ua ub em r args =
  match args with
  | (a,uu____169)::(b,uu____171)::[] ->
      let uu____212 =
        let uu____213 =
          let uu____214 = ua a in
          let uu____215 = ub b in f uu____214 uu____215 in
        em uu____213 in
      FStar_Pervasives_Native.Some uu____212
  | uu____216 -> FStar_Pervasives_Native.None
let reflection_primops: FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  let mklid nm = FStar_Reflection_Data.fstar_refl_syntax_lid nm in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    } in
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____346 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____347 =
    let uu____350 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____351 =
      let uu____354 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Reflection_Basic.embed_string_list in
      let uu____357 =
        let uu____360 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____363 =
          let uu____366 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string in
          let uu____367 =
            let uu____370 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order in
            let uu____371 =
              let uu____374 =
                mk11 "__type_of_binder"
                  (fun uu____386  ->
                     match uu____386 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term in
              let uu____397 =
                let uu____400 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_bool in
                let uu____401 =
                  let uu____404 =
                    mk11 "__fresh_binder"
                      (fun t  ->
                         let uu____414 =
                           FStar_Syntax_Syntax.gen_bv "__refl"
                             FStar_Pervasives_Native.None t in
                         (uu____414, FStar_Pervasives_Native.None))
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder in
                  let uu____417 =
                    let uu____420 =
                      mk2 "__term_eq" FStar_Syntax_Util.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_bool in
                    let uu____429 =
                      let uu____432 =
                        mk11 "__term_to_string"
                          FStar_Syntax_Print.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_string in
                      let uu____433 =
                        let uu____436 =
                          mk11 "__binders_of_env"
                            FStar_TypeChecker_Env.all_binders
                            FStar_Reflection_Basic.unembed_env
                            FStar_Reflection_Basic.embed_binders in
                        let uu____437 =
                          let uu____440 =
                            mk2 "__lookup_typ"
                              FStar_Reflection_Basic.lookup_typ
                              FStar_Reflection_Basic.unembed_env
                              FStar_Reflection_Basic.unembed_string_list
                              FStar_Reflection_Basic.embed_sigelt_view in
                          [uu____440] in
                        uu____436 :: uu____437 in
                      uu____432 :: uu____433 in
                    uu____420 :: uu____429 in
                  uu____404 :: uu____417 in
                uu____400 :: uu____401 in
              uu____374 :: uu____397 in
            uu____370 :: uu____371 in
          uu____366 :: uu____367 in
        uu____360 :: uu____363 in
      uu____354 :: uu____357 in
    uu____350 :: uu____351 in
  uu____346 :: uu____347