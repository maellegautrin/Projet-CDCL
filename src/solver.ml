module type SOLVER = sig
  val solve : Ast.t -> Ast.model option
end
