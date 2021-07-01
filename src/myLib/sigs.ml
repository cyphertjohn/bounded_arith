module Polynomial = struct
    type var_power = Exp of string * int

    type monic_mon = Prod of var_power list

    type 'a coef = Coef of 'a 

    type 'a monomial = ('a coef) * monic_mon

    type 'a polynomial = Sum of ('a monomial) list
end 


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
    val floor : coef -> coef
end

module Q : Coefficient = struct 
    type coef = Mpqf.t
    let addc = Mpqf.add 
    let mulc = Mpqf.mul
    let divc = Mpqf.div
    let is_zero c = (Mpqf.cmp_int c 0) = 0
    let is_one c = (Mpqf.cmp_int c 1) = 0
    let to_string_c = Mpqf.to_string
    let from_string_c = Mpqf.of_string
    let cmp = Mpqf.cmp
    let floor x = Mpqf.of_mpz (Mpqf.get_num x)
end

module Expr = struct
    type 'a expr = 
    | Coe of 'a
    | Var of string
    | Add of ('a expr) list
    | Mult of ('a expr) list
    | Div of ('a expr) * ('a expr)
    | Pow of ('a expr) * int 
    | Floor of ('a expr)
end