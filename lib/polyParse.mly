/* File parser.mly */
        %parameter<P : sig
          type poly
          val from_var : string -> poly
          val from_const_s : string -> poly
          val from_var_pow : string -> int -> poly
          val negate : poly -> poly
          val mul : poly -> poly -> poly
          val add : poly -> poly -> poly
       end>


        %{
            
            let negate_first l =
              match l with
              | (mon :: rest) -> (P.negate mon) :: rest
              | [] -> failwith "This can't happen"
              
        %}        
        %start <P.poly> main             /* the entry point */

        %%
        main:
            poly EOL                { let res = $1 in List.fold_left (P.add) (List.hd res) (List.tl res)}
        ;
        poly:
            monomial PLUS poly              { $1 :: $3 }
          | monomial MINUS poly             { $1 :: (negate_first $3) }
          | MINUS monomial                  { [P.negate $2] }
          | monomial                        { [$1] }
        ;
        monomial:
            INT TIMES monic_mon             { P.mul (P.from_const_s $1) ($3) }
          | INT monic_mon                   { P.mul (P.from_const_s $1) ($2) }
          | monic_mon                       { $1 }
          | INT                             { P.from_const_s $1 }
        ;
        monic_mon:
            var_power TIMES monic_mon       { P.mul $1 $3 }
          | var_power monic_mon             { P.mul $1 $2 }
          | var_power                       { $1 }
        ;
        var_power:
            VAR POWER INT                   { P.from_var_pow $1 (int_of_string $3) }
          | VAR                             { P.from_var $1 } 
        ;
