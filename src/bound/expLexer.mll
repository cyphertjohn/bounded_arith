{
    open ExpParse        (* The type token is defined in parser.mli *)
    exception Eof
    let keyword_table = Hashtbl.create 53
    let _ = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
                      [ "floor", FLOOR ]
}
rule token = parse
    [' ' '\t']     { token lexbuf }     (* skip blanks *)
    | ['\n' ]        { EOL }
    | ['0'-'9']+ as lxm { INT(lxm) }
    | ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '_' '0'-'9']*  as lxm { try
                                                                Hashtbl.find keyword_table lxm
                                                                with Not_found -> VAR lxm }
    | '+'            { PLUS }
    | '-'            { MINUS }
    | '*'            { TIMES }
    | '/'            { DIV }
    | '^'            { POWER }
    | '('            { LPAREN }
    | ')'            { RPAREN }
    | eof            { EOL }