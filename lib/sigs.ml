module type Coefficient = sig 
    type coef 
    val addc : coef -> coef -> coef 
    val mulc : coef -> coef -> coef
    val divc : coef -> coef -> coef 
    val is_zero : coef -> bool
    val is_one : coef -> bool
    val sgn : coef -> int
    val from_string_c : string -> coef
    val to_string_c : coef -> string
    val cmp : coef -> coef -> int
    val floor : coef -> coef
    val to_float : coef -> float
    val of_float : float -> coef
end


module Q : Coefficient = struct 
    type coef = Q.t
    let addc = Q.add 
    let mulc = Q.mul
    let divc = Q.div
    let is_zero c = (Q.compare c (Q.of_string "0")) = 0
    let is_one c = (Q.compare c (Q.of_string "1")) = 0
    let sgn = Q.sign
    let to_string_c = Q.to_string
    let from_string_c = Q.of_string
    let cmp = Q.compare
    let floor x = Q.of_bigint (Q.num x)
    let to_float = Q.to_float
    let of_float = Q.of_float
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