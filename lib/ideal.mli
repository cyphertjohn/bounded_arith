
module Make (P : Poly.Polynomial) : (
  sig 
    type poly = P.poly

    type monic_mon = P.monic_mon

    type ideal
    
    val from_string : string -> poly 

    val ppi : Format.formatter -> ideal -> unit

    val reduce : poly -> ideal -> poly * bool

    val make_ideal_f : P.V.Mi.map -> bool P.V.M.map -> (int * P.V.t) list -> poly list -> ideal

    val make_ideal : (monic_mon -> monic_mon -> int) -> poly list -> ideal

    val equal : ideal -> ideal -> bool

    val mem : poly -> ideal -> bool

    val get_generators : ideal -> poly list

    val add_eqs : ideal -> poly list -> ideal

    val get_ord : ideal -> monic_mon -> monic_mon -> int

    val get_implementation : ideal -> [> `buch | `fgb ]

  end)