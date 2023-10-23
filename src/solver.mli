(** Signature for a SAT solver. *)
module type SOLVER = sig

  (** solve takes a cnf formula and returns either None if it is unsatisfiable or
      a model that satisfies the formula. *)
  val solve : Ast.t -> Ast.model option

end
