{
    open PolyParse        (* The type token is defined in parser.mli *)
    exception Eof
}
rule token = parse
    [' ' '\t']     { token lexbuf }     (* skip blanks *)
    | ['\n' ]        { EOL }
    | ['0'-'9']+ as lxm { INT(lxm) }
    | ['a'-'z']"\'"?  as lxm { VAR(lxm) }
    | '+'            { PLUS }
    | '-'            { MINUS }
    | '*'            { TIMES }
    | '^'            { POWER }
    | eof            { EOL }