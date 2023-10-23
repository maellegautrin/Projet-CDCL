open Solver;;
open Choice;;

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
    let range = List.init f.nb_var (fun x -> x + 1) in
    let unbound_vars = List.fold_left (fun set x -> LitSet.add x set) LitSet.empty range in
    let initial_instance = {ast = f; assignment = []; unbound = unbound_vars; learned_clauses = Ast.Cnf.empty} in
    solve_sat initial_instance


  end

