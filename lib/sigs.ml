module type Coefficient = sig 
    type coef 
    val addc : coef -> coef -> coef 
    val mulc : coef -> coef -> coef
    val divc : coef -> coef -> coef
    val exp : coef -> int -> coef
    val is_zero : coef -> bool
    val is_one : coef -> bool
    val sgn : coef -> int
    val from_string_c : string -> coef
    val to_string_c : coef -> string
    val cmp : coef -> coef -> int
    val floor : coef -> coef
    val to_float : coef -> float
    val of_float : float -> coef
    val to_zarith : coef -> Q.t
    val of_zarith : Z.t -> coef
    val of_zarith_q : Q.t -> coef
    val one : coef
    val zero : coef
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
    let to_zarith (x : coef) : Q.t = x
    let of_zarith (x : Z.t) : coef = Q.make x Z.one
    let of_zarith_q (x : Q.t) : coef = x
    let exp c n = 
      let rec aux acc x e = 
        if e < 0 then aux acc (Q.inv x) (-e)
        else if e = 0 then acc
        else if e mod 2 = 0 then aux acc (Q.mul x x) (e/2)
        else aux (Q.mul acc x) (Q.mul x x) ((e-1)/2)
      in
      aux (Q.one) c n
    let one = Q.one
    let zero = Q.zero
end

module type Var = sig
    type t
    
    val of_string : string -> t

    val fresh_var : unit -> t

    val to_string : t -> string

    val equal : t -> t -> bool

    val compare : t -> t -> int

    val hash : t -> int

    module S : sig
      type set
      val empty : set

      val add : t -> set -> set

      val union : set -> set -> set

      val mem : t -> set -> bool

      val diff : set -> set -> set

      val fold : (t  -> 'a -> 'a) -> set -> 'a -> 'a
    end

    module M : sig
      type 'a map
      val empty : 'a map

      val is_empty : 'a map -> bool

      val add : t -> 'a -> 'a map -> 'a map

      val find : t -> 'a map -> 'a

      val bindings : 'a map -> (t * 'a) list

      val fold : (t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b

      val mem : t -> 'a map -> bool

      val remove : t -> 'a map -> 'a map

      val modify_def : 'a -> t -> ('a -> 'a) -> 'a map -> 'a map

      val merge : (t -> 'a option -> 'b option -> 'c option) -> 'a map -> 'b map -> 'c map

      val domain : 'a map -> S.set
    end

    module Mi : sig
      type map
      val empty : map

      val is_empty : map -> bool

      val add : t -> int -> map -> map

      val find : t -> map -> int

      val fold : (t -> int -> 'b -> 'b) -> map -> 'b -> 'b

      val mem : t -> map -> bool

      val remove : t -> map -> map

      val modify_def : int -> t -> (int -> int) -> map -> map

      val domain : map -> S.set
    end
end

module V : Var = struct
  let int_to_string = BatHashtbl.create 20
  let string_to_int = BatHashtbl.create 20
  let dummy_vars = ref BatISet.empty

  let curr_num = ref 0
  type t = int

  let of_string (s : string) : t = 
    try BatHashtbl.find string_to_int s
    with Not_found ->
      BatHashtbl.add int_to_string !curr_num s;
      BatHashtbl.add string_to_int s !curr_num;
      curr_num := !curr_num + 1;
      !curr_num - 1
    
  let to_string v = 
    if BatISet.mem v !dummy_vars then "x" ^ (string_of_int v)
    else BatHashtbl.find int_to_string v

  let fresh_var () = 
    dummy_vars := BatISet.add !curr_num !dummy_vars;
    curr_num := !curr_num + 1;
    !curr_num - 1

  let equal = (=)

  let compare = compare

  let hash i = i

  module S = struct type set = BatISet.t include BatISet end

  module M = struct 
    module B = BatMap.Make(struct type t = int let compare = compare end)
    type 'a map = 'a B.t
    include B
    let domain m = BatISet.of_enum (BatEnum.map (fun (a, _) -> (a, a)) (B.enum m))
  end

  module Mi = struct 
    type map = int BatIMap.t 
    include BatIMap 
    let empty = BatIMap.empty ~eq:(=)
    (*let bindings m = 
      let dset = BatIMap.domain m in
      BatISet.fold (fun v acc -> (v, BatIMap.find v m) :: acc) dset []*)
  end

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