/* File parser.mly */   
        %token <string> INT
        %token <string> VAR
        %token PLUS MINUS TIMES POWER DIV LPAREN RPAREN FLOOR
        %token EOL
        %left PLUS MINUS
        %left TIMES DIV
        %right POWER
        %nonassoc UMINUS
        %start main             /* the entry point */
        %type <string Sigs.Expr.expr> main
        %%
        main:
            expr EOL                { $1 }
        ;
        expr :
          | FLOOR LPAREN expr RPAREN        { Sigs.Expr.Floor ($3) }
          | expr POWER INT %prec POWER      { Sigs.Expr.Pow ($1, int_of_string $3) }
          | expr DIV expr %prec DIV         { Sigs.Expr.Div ($1, $3) }
          | expr TIMES expr %prec TIMES     { Sigs.Expr.Mult [$1; $3] }
          | expr PLUS expr %prec PLUS       { Sigs.Expr.Add [$1; $3] }
          | expr MINUS expr %prec MINUS     { Sigs.Expr.Add [$1; Sigs.Expr.Mult[Sigs.Expr.Coe ("-1"); $3]]}
          | MINUS expr %prec UMINUS         { Sigs.Expr.Mult[Sigs.Expr.Coe ("-1"); $2] }
          | LPAREN expr RPAREN              { $2 }
          | expr expr %prec TIMES           { Sigs.Expr.Mult [$1; $2] }
          | INT                             { Sigs.Expr.Coe $1}
          | VAR                             { Sigs.Expr.Var $1}
        ;