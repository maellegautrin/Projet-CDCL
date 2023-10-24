open Solver;;
open Choice;;
open Graph;;


module Vertex = struct
  type t = Ast.lit * int

  let compare (a,b) (c,d) =
    let co = compare a c in
    if co = 0 then compare b d
    else co
end

module Edge = struct
  type t = Vertex.t * Vertex.t

  let compare a b = Vertex.compare a b

  let default = ((0,0),(0,0))

end

module ImplicationGraph = Graph.Persistent.Digraph.AbstractLabeled(Vertex)(Edge)


module CDCL(C:CHOICE) : SOLVER =
  struct
  module LitSet = Set.Make(struct type t = int let compare = compare end)

  exception Unsat

  type instance = {
    ast: Ast.t;
    assignment: Ast.model;
    unbound: LitSet.t;
    learned_clauses : Ast.Cnf.t
  }

  let assign_literal (instance: instance) (literal: Ast.var): instance =
    (* Construct a new CNF without the literal *)
    let cnf =
      let assign_clause (clause: Ast.Clause.t) (cnf: Ast.Cnf.t) =
        if Ast.Clause.mem literal clause then cnf
        else Ast.Cnf.add (Ast.Clause.remove (Ast.neg literal) clause) cnf
      in Ast.Cnf.fold assign_clause instance.ast.cnf Ast.Cnf.empty in
    { ast = { instance.ast with cnf };
      assignment = literal :: instance.assignment;
      unbound = LitSet.remove (abs literal) instance.unbound;
      learned_clauses = instance.learned_clauses
    }

  let rec unit_propagate (instance: instance): Ast.model =
    let unit_clause = Ast.Clause.fold (fun x y -> x :: y)
    in Ast.Cnf.fold unit_clause (Ast.Cnf.filter (fun clause -> (Ast.Clause.cardinal clause) == 1) instance.ast.cnf) []

  let pure_literal (instance: instance): Ast.model =
    let rec filter_pure_literal list =
      match list with
      | x :: y :: xs -> if x == -y then filter_pure_literal xs else x :: filter_pure_literal (y :: xs)
      | _ -> list
    in filter_pure_literal (Ast.Clause.elements (Ast.Cnf.fold Ast.Clause.union instance.ast.cnf Ast.Clause.empty))

  let rec simplify (instance: instance): instance =
    (* Check if there is a unit clause in formula or pure: Unit Propagation *)
    match unit_propagate instance with
    | [] -> begin
        (* Check if there is a literal that occurs pure in formula *)
        match pure_literal instance with
        | [] -> instance
        | literals -> simplify (List.fold_left assign_literal instance (pure_literal instance))
      end
    | literals -> simplify (List.fold_left assign_literal instance literals)

  let rec solve_sat (instance: instance): Ast.model option =
    (* Simplify formula *)
    let instance = simplify instance in

    (* Check if the formula is empty: SAT *)
    if Ast.Cnf.is_empty instance.ast.cnf then Some instance.assignment else

    (* Check if the formula contains an empty clause: UNSAT *)
    if Ast.Cnf.exists Ast.Clause.is_empty instance.ast.cnf then None else

    (* Choose a literal *)
    let literal = LitSet.choose instance.unbound in

    (* Call recursively the algorithm *)
    match solve_sat (assign_literal instance (Ast.neg literal)) with
    | Some list -> Some list
    | None -> begin
      (* Conflict detected, analyze and learn *)
      let conflict_clause = analyze_conflict instance in
      let new_instance = {
        ast = {
          instance.ast with cnf = Ast.Cnf.add conflict_clause instance.ast.cnf
        };
        assignment = instance.assignment;
        unbound = instance.unbound;
        learned_clauses = Ast.Cnf.add conflict_clause instance.learned_clauses;
      } in
      match backtrack_and_learn new_instance with
      | None -> None
      | Some new_instance' -> solve_sat new_instance'
    end

 and analyze_conflict (instance: instance): Ast.Clause.t =
   failwith "todo"


 and backtrack_and_learn (instance: instance): instance option =
    let rec backtrack (assignment: Ast.model) (learned_clause: Ast.Clause.t): Ast.model =
    match assignment with
    | [] -> raise Unsat (* Conflict propagated to the top level, formula is unsatisfiable *)
    | literal :: rest_assignment ->
      if Ast.Clause.mem literal learned_clause then
        backtrack rest_assignment learned_clause
      else
        backtrack rest_assignment learned_clause @ [Ast.neg literal]
  in
  try
    let learned_clause = analyze_conflict instance in
    let new_assignment = backtrack instance.assignment learned_clause in
    let new_instance = {
      ast = { instance.ast with cnf = Ast.Cnf.add learned_clause instance.ast.cnf };
      assignment = new_assignment;
      unbound = instance.unbound;
      learned_clauses = Ast.Cnf.add learned_clause instance.learned_clauses;
    }
    in
    Some new_instance
  with
  | Unsat -> (* No further backtracking possible, the formula is unsatisfiable *)
    None



  let solve (f: Ast.t): Ast.model option =
    if Horn.Horn.is_horn f then Horn.Horn.solve f
    else (
    let range = List.init f.nb_var (fun x -> x + 1) in
    let unbound_vars = List.fold_left (fun set x -> LitSet.add x set) LitSet.empty range in
    let initial_instance = {ast = f; assignment = []; unbound = unbound_vars; learned_clauses = Ast.Cnf.empty} in
    solve_sat initial_instance)


  end
(*
open Printf

(* Enumération pour stocker les états de sortie de certaines fonctions du solveur *)
type ret_val =
  | R_satisfied   (* la formule a été satisfaite *)
  | R_unsatisfied (* la formule n'a pas été satisfaite *)
  | R_normal      (* la formule n'est pas encore résolue *)

(* Structure pour stocker l'état du solveur SAT *)
type sat_solver_cdcl = {
  mutable literals : int list;                  (* État de chaque variable *)
  mutable literal_list_per_clause : int list list; (* Liste de littéraux pour chaque clause *)
  mutable literal_frequency : int list;         (* Occurrences totales de chaque variable dans la formule *)
  mutable literal_polarity : int list;          (* Différence entre le nombre d'occurrences positives et négatives de chaque variable *)
  mutable original_literal_frequency : int list; (* Copie de sauvegarde des fréquences *)
  mutable literal_count : int;                  (* Nombre de variables dans la formule *)
  mutable clause_count : int;                   (* Nombre de clauses dans la formule *)
  mutable kappa_antecedent : int;               (* Antécédent du conflit, kappa *)
  mutable literal_decision_level : int list;     (* Niveau de décision de chaque variable *)
  mutable literal_antecedent : int list;        (* Antécédent de chaque variable *)
  mutable assigned_literal_count : int;         (* Nombre de variables assignées jusqu'à présent *)
  mutable already_unsatisfied : bool;           (* Si la formule contient une clause vide initialement *)
  mutable pick_counter : int;                   (* Nombre de fois où une variable a été choisie librement en fonction de la fréquence *)
  mutable generator : Random.State.t;
}

(* Fonction pour effectuer la propagation unitaire *)
let unit_propagate solver decision_level =
  let unit_clause_found = ref false in
  let false_count = ref 0 in
  let unset_count = ref 0 in
  let satisfied_flag = ref false in
  let last_unset_literal = ref (-1) in

  let resolve input_clause resolver_literal =
    let second_input = List.nth solver.literal_list_per_clause solver.literal_antecedent.(resolver_literal) in
    let input_clause = List.append input_clause second_input in
    let rec remove_literal lst lit =
      match lst with
      | [] -> []
      | hd :: tl -> if hd = lit + 1 || hd = -lit - 1 then remove_literal tl lit else hd :: remove_literal tl lit
    in
    let input_clause = remove_literal input_clause (resolver_literal + 1) in
    let sorted_clause = List.sort compare input_clause in
    let deduplicated_clause = List.sort_uniq compare sorted_clause in
    deduplicated_clause
  in

  let rec conflict_analysis_and_backtrack decision_level =
    let learnt_clause = ref (List.nth solver.literal_list_per_clause solver.kappa_antecedent) in
    let conflict_decision_level = ref decision_level in
    let this_level_count = ref 0 in
    let resolver_literal = ref 0 in
    let literal = ref 0 in

    let rec find_uip clause decision_level =
      match clause with
      | [] -> !resolver_literal
      | hd :: tl ->
        let lit = solver.literal_to_variable_index hd in
        if solver.literal_decision_level.(lit) = decision_level then this_level_count := !this_level_count + 1;
        if solver.literal_decision_level.(lit) = decision_level && solver.literal_antecedent.(lit) <> -1 then resolver_literal := lit;
        find_uip tl decision_level
    in

    let uip = find_uip !learnt_clause decision_level in

    if !this_level_count = 1 then
      !conflict_decision_level
    else
      begin
        learnt_clause := resolve !learnt_clause !resolver_literal;
        conflict_analysis_and_backtrack decision_level
      end
  in

  let assign_literal variable decision_level antecedent =
    let literal = solver.literal_to_variable_index variable in
    let value = if variable > 0 then 1 else 0 in
    solver.literals.(literal) <- value;
    solver.literal_decision_level.(literal) <- decision_level;
    solver.literal_antecedent.(literal) <- antecedent;
    solver.literal_frequency.(literal) <- -1;
    solver.assigned_literal_count <- solver.assigned_literal_count + 1
  in

  let unassign_literal literal_index =
    solver.literals.(literal_index) <- -1;
    solver.literal_decision_level.(literal_index) <- -1;
    solver.literal_antecedent.(literal_index) <- -1;
    solver.literal_frequency.(literal_index) <- solver.original_literal_frequency.(literal_index);
    solver.assigned_literal_count <- solver.assigned_literal_count - 1
  in

  let literal_to_variable_index variable =
    if variable > 0 then variable - 1 else -variable - 1
  in

  let rec resolve input_clause resolver_literal =
    let second_input = List.nth solver.literal_list_per_clause solver.literal_antecedent.(resolver_literal) in
    let input_clause = List.append input_clause second_input in
    let rec remove_literal lst lit =
      match lst with
      | [] -> []
      | hd :: tl -> if hd = lit + 1 || hd = -lit - 1 then remove_literal tl lit else hd :: remove_literal tl lit
    in
    let input_clause = remove_literal input_clause (resolver_literal + 1) in
    let sorted_clause = List.sort compare input_clause in
    let deduplicated_clause = List.sort_uniq compare sorted_clause in
    deduplicated_clause
  in

  let conflict_analysis_and_backtrack decision_level =
    let learnt_clause = ref (List.nth solver.literal_list_per_clause solver.kappa_antecedent) in
    let conflict_decision_level = ref decision_level in
    let this_level_count = ref 0 in
    let resolver_literal = ref 0 in
    let literal = ref 0 in

    let rec find_uip clause decision_level =
      match clause with
      | [] -> !resolver_literal
      | hd :: tl ->
        let lit = solver.literal_to_variable_index hd in
        if solver.literal_decision_level.(lit) = decision_level then this_level_count := !this_level_count + 1;
        if solver.literal_decision_level.(lit) = decision_level && solver.literal_antecedent.(lit) <> -1 then resolver_literal := lit;
        find_uip tl decision_level
    in

    let uip = find_uip !learnt_clause decision_level in
    if !this_level_count = 1 then
      !conflict_decision_level
    else
      begin
        learnt_clause := resolve !learnt_clause !resolver_literal;
        conflict_analysis_and_backtrack decision_level
      end
      *)
