(* -------------------------------------------------------------------- *)
%token EOF

%type <unit> entry

%start entry

%%
entry:
| EOF
{};
