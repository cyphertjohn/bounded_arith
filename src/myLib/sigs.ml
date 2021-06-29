type var_power = Exp of string * int

type monic_mon = Prod of var_power list

type 'a coef = Coef of 'a 

type 'a monomial = ('a coef) * monic_mon

type 'a polynomial = Sum of ('a monomial) list

type q = Mpqf.t coef

module type Coefficient = sig 
    type coef 
    val addc : coef -> coef -> coef 
    val mulc : coef -> coef -> coef
    val divc : coef -> coef -> coef 
    val is_zero : coef -> bool
    val is_one :coef -> bool
    val from_string_c : string -> coef
    val to_string_c : coef -> string
    val cmp : coef -> coef -> int
end
