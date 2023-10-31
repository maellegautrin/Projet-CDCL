
module TWL : sig
  val is_2wl : Ast.t -> bool

  val solve : Ast.t -> Ast.model option
end
