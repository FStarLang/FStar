module DocsImportsInterface

open Interface

[@@doc ["This module depends on a module literally named Interface."]]
let documented (x:int) : int = x
