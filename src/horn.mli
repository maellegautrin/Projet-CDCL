module Horn : sig
  val is_horn : Ast.t -> bool

  val solve : Ast.t -> Ast.model option
end
