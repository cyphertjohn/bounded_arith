/* File parser.mly */
        %{
            let negate_mon (Sigs.Polynomial.Coef c, x) = 
              (Sigs.Polynomial.Coef ("-" ^ c), x)

            let negate_first l =
              match l with
              | (mon :: rest) -> (negate_mon mon) :: rest
              | [] -> failwith "This can't happen"
              
        %}        
        %token <string> INT
        %token <string> VAR
        %token PLUS MINUS TIMES POWER
        %token EOL
        /*%left PLUS MINUS      
        %left TIMES             
        %right POWER
        %nonassoc UMINUS        */
        %start main             /* the entry point */
        %type <string Sigs.Polynomial.polynomial> main
        %%
        main:
            poly EOL                { Sigs.Polynomial.Sum $1 }
        ;
        poly:
            monomial PLUS poly              { $1 :: $3 }
          | monomial MINUS poly             { $1 :: (negate_first $3) }
          | MINUS monomial                  { [negate_mon $2] }
          | monomial                        { [$1] }
        ;
        monomial:
            INT TIMES monic_mon             { (Sigs.Polynomial.Coef ($1), Sigs.Polynomial.Prod $3) }
          | INT monic_mon                   { (Sigs.Polynomial.Coef ($1), Sigs.Polynomial.Prod $2) }
          | monic_mon                       { (Sigs.Polynomial.Coef ("1"), Sigs.Polynomial.Prod $1)}
          | INT                             { (Sigs.Polynomial.Coef ($1), Sigs.Polynomial.Prod []) }
        ;
        monic_mon:
            var_power TIMES monic_mon       { $1 :: $3 }
          | var_power monic_mon             { $1 :: $2 }
          | var_power                       { [$1] }
        ;
        var_power:
            VAR POWER INT                   { Sigs.Polynomial.Exp ( $1, int_of_string $3) }
          | VAR                             { Sigs.Polynomial.Exp ( $1, 1) } 
        ;