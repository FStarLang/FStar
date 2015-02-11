module Microsoft.FStar.Absyn.SSyntax

open Microsoft.FStar.Absyn.Syntax

let deserialize_modul_ext (f:string) :Syntax.modul =
    { name = Syntax.lid_of_path [] Syntax.dummyRange;
      declarations = [];
      exports = [];
      is_interface = false;
      is_deserialized = false }

let serialize_modul_ext (f:string) (m:Syntax.modul) :unit = ()
