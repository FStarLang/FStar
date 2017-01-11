%{

%}

%token EOL
%token PUSH LAX POP
%token <string * string> DONE
%token<string> LINE
%token<int> INT

%start<FStar_Interactive.input_chunks> line
%%

line:
  | PUSH l=INT c=INT lax=boption(LAX) EOL
    { Push (l, c, b) }
  | POP msg=LINE EOL
    { Pop ("#pop " ^ msg) }
  | lines=list(s=LINE EOL {s}) DONE ans=LINE EOL
    {
      let ans =
        match FStar_String.split ' ' (FStar_Util.trim_string ans)
        | [ ok ; nok ] -> ok, nok
        | _ -> failwith "Invalid answers after done"
      in
      Code (FStar_String.concat "\n" lines ^ "\n", ans)
    }
