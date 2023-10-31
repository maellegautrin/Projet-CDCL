
module TWL = struct
  let is_2wl (f:Ast.t) : bool =
    Ast.Cnf.for_all (fun cl ->
      Ast.Clause.cardinal cl <= 2 ) f.cnf

  let solve (f:Ast.t) : Ast.model option = None

end
