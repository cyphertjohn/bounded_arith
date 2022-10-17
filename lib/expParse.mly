/* File parser.mly */   
        %token <string> INT
        %token <string> VAR
        %token PLUS MINUS TIMES POWER DIV LPAREN RPAREN FLOOR
        %token EOL
        %left PLUS MINUS
        %left TIMES /*DIV*/
        /*%right POWER*/
        %nonassoc UMINUS
        %start main             /* the entry point */
        %type <string Sigs.Expr.expr> main
        %%
        main:
            expr EOL                { $1 }
        ;
        expr :
          | expr PLUS expr %prec PLUS       { Sigs.Expr.Add [$1; $3] }
          | expr MINUS expr %prec MINUS     { Sigs.Expr.Add [$1; Sigs.Expr.Mult[Sigs.Expr.Coe ("-1"); $3]]}
          | MINUS expr %prec UMINUS         { Sigs.Expr.Mult[Sigs.Expr.Coe ("-1"); $2] }
          | term                            { $1 }
        ;
        term :
          | FLOOR LPAREN expr RPAREN        { Sigs.Expr.Func ("floor", $3) }
          | LPAREN expr RPAREN              { $2 }
          | LPAREN expr RPAREN POWER INT    { Sigs.Expr.Pow ($2, Sigs.Expr.Coe $5) }
          | term DIV INT /*%prec DIV */         { Sigs.Expr.Div ($1, Sigs.Expr.Coe $3) }
          | term DIV VAR /*%prec DIV*/          { Sigs.Expr.Div ($1, Sigs.Expr.Var $3) }
          | term DIV LPAREN expr RPAREN     { Sigs.Expr.Div ($1, $4) }
          | LPAREN expr RPAREN DIV LPAREN expr RPAREN { Sigs.Expr.Div ($2, $6) }
          | term TIMES term %prec TIMES     { Sigs.Expr.Mult [$1; $3] }
          | term term %prec TIMES           { Sigs.Expr.Mult [$1; $2] }
          | varpow                          { $1 }
        ;
        varpow :
          | VAR POWER INT                     { Sigs.Expr.Pow (Sigs.Expr.Var $1, Sigs.Expr.Coe $3) }
          | INT POWER INT                     { Sigs.Expr.Pow (Sigs.Expr.Coe $1, Sigs.Expr.Coe $3) }
          | VAR                             { Sigs.Expr.Var $1 }
          | INT                             { Sigs.Expr.Coe $1 }
        ;