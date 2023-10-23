(** Signature module to choose a variable on which the DPLL algorithm will branch. *)
module type CHOICE = sig
  val choice : Ast.Cnf.t -> Ast.var
end


(** Implement a choice by Default. More choices can be implemented. *)
module DefaultChoice : CHOICE
