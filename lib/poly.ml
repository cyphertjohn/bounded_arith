module type Polynomial = sig

  module C : Sigs.Coefficient

  module V : Sigs.Var

  type monic_mon

  type mon = C.coef * monic_mon

  type poly

  type sorted_poly

  val mon_to_id : monic_mon -> int

  val id_to_mon : int -> monic_mon
  
  val fresh_dim : unit -> int

  val divide_mon : mon -> mon -> mon option

  val lcm_of_mon : monic_mon -> monic_mon -> monic_mon

  val mult_mon : mon -> mon -> mon

  val zero_mon : mon

  val make_mon_from_coef : C.coef -> mon

  val make_mon_from_var : V.t -> int -> mon

  val make_mon_from_faugere_mon : V.t list -> Z.t * int list -> mon

  val get_mons : poly -> mon list

  val get_degree : V.t -> monic_mon -> int

  val get_vars_m : monic_mon -> V.S.set
  
  val lex_ord : monic_mon -> monic_mon -> int

  val grlex_ord : monic_mon -> monic_mon -> int

  val add :
    poly -> poly -> poly

  val addi :
    poly -> poly -> unit

  val subtract : poly -> poly -> poly

  val subtracti : poly -> poly -> unit

  val mult_mon_poly : mon -> poly -> poly

  val mul :
    poly -> poly -> poly
    
  val exp_poly : poly -> int -> poly

  val substitute :
    V.t * poly -> poly -> poly

  val is_zero : poly -> bool

  val is_one : poly -> bool

  val is_const : poly -> C.coef option

  val compare : poly -> poly -> int

  val equal : poly -> poly -> bool

  val from_var : V.t -> poly

  val from_var_s : string -> poly

  val from_const_s : string -> poly

  val from_var_pow : V.t -> int -> poly

  val from_var_s_pow : string -> int -> poly

  val from_mon_list : mon list -> poly

  val ppmm : Format.formatter -> monic_mon -> unit

  val ppm : Format.formatter -> mon -> unit

  val pp : ?ord:(monic_mon -> monic_mon -> int) -> Format.formatter -> poly -> unit

  val negate : poly -> poly

  val to_string : poly -> string

  val get_vars : poly -> V.S.set

  val from_const : C.coef -> poly

  val make_sorted_poly : (monic_mon -> monic_mon -> int) -> poly -> sorted_poly

  val get_poly : sorted_poly -> poly

  val lt : sorted_poly -> mon

  val lc : sorted_poly -> C.coef

  val division : (monic_mon -> monic_mon -> int) -> sorted_poly list -> sorted_poly -> bool * (poly list * sorted_poly)

  val make_monic : sorted_poly -> sorted_poly

  val equal_sorted_sets : sorted_poly list -> sorted_poly list -> bool

  val from_string : string -> poly

end


module Make (Co : Sigs.Coefficient)(Va : Sigs.Var) : (Polynomial with module C = Co and module V = Va) = struct

  module PP = PrePoly.Make(Co)(Va)

  module P = PolyParse.Make(PP)

  let from_string s = (P.main PolyLexer.token (Lexing.from_string s))


  include PP

end