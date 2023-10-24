

module Horn = struct
  let is_horn (formula:Ast.t) : bool =
    Ast.Cnf.for_all (fun cl ->
          snd
            (Ast.Clause.fold (fun v (as_positive,cond) ->
                if v > 0 then (true, not as_positive)
                else
                  (as_positive,cond)
              ) cl (false, true))
      )  formula.cnf

  let get_positive_literal cl =
    Ast.Clause.find_first_opt (fun v -> v > 0) cl


  let transform_to_solution (e:Ast.Clause.t) (f:Ast.t) =
    let l = ref [] in
    for i = 1 to f.nb_var do
      if not (List.mem i !l) then
        l := (-i) :: !l
      else
        l := i :: !l
    done;
    !l

  let solve (formula:Ast.t) : Ast.model option =
    let e = ref Ast.Clause.empty in
    let e' = ref Ast.Clause.empty in

      e := Ast.Clause.union !e !e';
      e' := Ast.Clause.empty;
      Ast.Cnf.iter (fun cl ->
          match get_positive_literal cl with
          | Some p -> if Ast.Clause.mem p !e && Ast.Clause.for_all
           (fun v -> if v < 0 then (Ast.Clause.mem v !e) else true) cl
            then e' := Ast.Clause.add p !e'
            else ()
          | None -> ()
        ) formula.cnf;
    while not (Ast.Clause.is_empty !e') do
      e := Ast.Clause.union !e !e';
      e' := Ast.Clause.empty;
      Ast.Cnf.iter (fun cl ->
          match get_positive_literal cl with
          | Some p -> if Ast.Clause.mem p !e && Ast.Clause.for_all
           (fun v -> if v < 0 then (Ast.Clause.mem v !e) else true) cl
            then e' := Ast.Clause.add p !e'
            else ()
          | None -> ()
        ) formula.cnf;
    done;
    (* check e is correct *)
    if Ast.Cnf.for_all (fun cl ->
        let p = get_positive_literal cl in
        if (match p with
        | Some p -> not (Ast.Clause.mem p !e)
        | None -> true) then Ast.Clause.for_all (fun v -> if v < 0 then not (Ast.Clause.mem v !e) else true) cl
        else true
    ) formula.cnf then Some (transform_to_solution !e formula)
    else None

end
