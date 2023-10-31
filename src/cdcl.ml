open Solver;;
open Choice;;
open Graph;;


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

(* Structure pour stocker l'état du solveur SAT *)
type sat_solver_cdcl = {
  mutable literals : int array;                  (* État de chaque variable *)
  mutable literal_list_per_clause : int list list; (* Liste de littéraux pour chaque clause *)
  mutable literal_frequency : int array;         (* Occurrences totales de chaque variable dans la formule *)
  mutable literal_polarity : int list;          (* Différence entre le nombre d'occurrences positives et négatives de chaque variable *)
  mutable original_literal_frequency : int array; (* Copie de sauvegarde des fréquences *)
  mutable literal_count : int;                  (* Nombre de variables dans la formule *)
  mutable clause_count : int;                   (* Nombre de clauses dans la formule *)
  mutable kappa_antecedent : int;               (* Antécédent du conflit, kappa *)
  mutable literal_decision_level : int array;     (* Niveau de décision de chaque variable *)
  mutable literal_antecedent : int array;        (* Antécédent de chaque variable *)
  mutable assigned_literal_count : int;         (* Nombre de variables assignées jusqu'à présent *)
  mutable already_unsatisfied : bool;           (* Si la formule contient une clause vide initialement *)
  mutable pick_counter : int;                   (* Nombre de fois où une variable a été choisie librement en fonction de la fréquence *)
  mutable generator : Random.State.t;
}



  let solver = {
    literals = Array.make 100 (-1);                  (* État de chaque variable *)
    literal_list_per_clause = []; (* Liste de littéraux pour chaque clause *)
    literal_frequency = Array.make 100 0;         (* Occurrences totales de chaque variable dans la formule *)
    literal_polarity = [];          (* Différence entre le nombre d'occurrences positives et négatives de chaque variable *)
    original_literal_frequency = Array.make 100 0; (* Copie de sauvegarde des fréquences *)
    literal_count = 0;                  (* Nombre de variables dans la formule *)
    clause_count = 0;                   (* Nombre de clauses dans la formule *)
    kappa_antecedent = 0;               (* Antécédent du conflit, kappa *)
    literal_decision_level = Array.make 100 (-1);     (* Niveau de décision de chaque variable *)
    literal_antecedent = Array.make 100 (-1);        (* Antécédent de chaque variable *)
    assigned_literal_count = 0;         (* Nombre de variables assignées jusqu'à présent *)
    already_unsatisfied = false;           (* Si la formule contient une clause vide initialement *)
    pick_counter = 0;                   (* Nombre de fois où une variable a été choisie librement en fonction de la fréquence *)
    generator = Random.State.make_self_init ();
  }

(* Fonction pour effectuer la propagation unitaire *)
  let rec find_uip clause decision_level resolver_literal this_level_count =
      match clause with
      | [] -> !resolver_literal
      | hd :: tl ->
        let lit = literal_to_variable_index hd in
        if solver.literal_decision_level.(lit) = decision_level then this_level_count := !this_level_count + 1;
        if solver.literal_decision_level.(lit) = decision_level && solver.literal_antecedent.(lit) <> -1 then resolver_literal := lit;
        find_uip tl decision_level resolver_literal this_level_count

  and resolve input_clause resolver_literal =
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

  and conflict_analysis_and_backtrack decision_level =
    let learnt_clause = ref (List.nth solver.literal_list_per_clause solver.kappa_antecedent) in
    let conflict_decision_level = ref decision_level in
    let this_level_count = ref 0 in
    let resolver_literal = ref 0 in
    let literal = ref 0 in
    let uip = find_uip !learnt_clause decision_level resolver_literal this_level_count in

    if !this_level_count = 1 then
      !conflict_decision_level
    else
      begin
        learnt_clause := resolve !learnt_clause !resolver_literal;
        conflict_analysis_and_backtrack decision_level
      end



  and assign_literal variable decision_level antecedent =
    let literal = literal_to_variable_index variable in
    let value = if variable > 0 then 1 else 0 in
    solver.literals.(literal) <- value;
    solver.literal_decision_level.(literal) <- decision_level;
    solver.literal_antecedent.(literal) <- antecedent;
    solver.literal_frequency.(literal) <- -1;
    solver.assigned_literal_count <- solver.assigned_literal_count + 1

  and unassign_literal literal_index =
      solver.literals.(literal_index) <- -1;
      solver.literal_decision_level.(literal_index) <- -1;
      solver.literal_antecedent.(literal_index) <- -1;
      solver.literal_frequency.(literal_index) <- solver.original_literal_frequency.(literal_index);
      solver.assigned_literal_count <- solver.assigned_literal_count - 1
  and literal_to_variable_index variable =
      if variable > 0 then variable - 1 else -variable - 1


(*
  let solve (f: Ast.t): Ast.model option =
    if Horn.Horn.is_horn f then Horn.Horn.solve f
    else (
    let range = List.init f.nb_var (fun x -> x + 1) in
    let unbound_vars = List.fold_left (fun set x -> LitSet.add x set) LitSet.empty range in
    let initial_instance = {ast = f; assignment = []; unbound = unbound_vars; learned_clauses = Ast.Cnf.empty} in
    None)
*)
  let solve (f:Ast.t): Ast.model option =
    if Horn.Horn.is_horn f then Horn.Horn.solve f
    else Some (resolve [] 0)

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
