
module CDCL(C:Choice.CHOICE) : Solver.SOLVER =
  struct


    type annoted_literal =
      | Decision of Ast.lit * int
      | UnitPropagation of Ast.lit * Ast.Clause.t * int


    module ClauseMap = Map.Make(Ast.Clause)


    type instance = {
      mutable trail : annoted_literal list;
      initial_clauses : Ast.t ;
      mutable learned_clauses : Ast.Cnf.t ;
      mutable decision_level : int;
      mutable model_state : Ast.Clause.t ;
      variable_clauses : Ast.Cnf.t array;
      level_var : int array;
      reason : Ast.Clause.t array
    }

  let find_value v m =
    List.exists (fun e ->
      match e with
        | Decision (a,_) -> a = v
        | UnitPropagation (a,_,_) -> a = v
      ) m


  let print_trail t =
    List.iter (fun e ->
      match e with
        | Decision (a,dl) -> print_string ("D("^string_of_int a^","^string_of_int dl ^") ")
        | UnitPropagation (a,cl,dl) -> print_string ("U("^string_of_int a^","^
                                                 Ast.Clause.fold (fun e s -> s ^" "^string_of_int e) cl ""^
                                                     ","^string_of_int dl
                                                 ^") ")
      ) t;
    print_endline ""

  let print_state ?(show = true) s =
    print_endline ("dl : "^string_of_int s.decision_level);
    print_string "trail : "; print_trail s.trail;
    if show then (print_string "initial_clause : "; Ast.pp Format.std_formatter s.initial_clauses)
    else ()

  let find_literal v m =
    List.exists (fun e ->
      match e with
        | Decision (a,_) -> a = v || a = -v
        | UnitPropagation (a,_,_) -> a = v || a = -v
      ) m

  let get_literal l =
    match l with
        | Decision (a,_) -> a
        | UnitPropagation (a,_,_) -> a

  let get_level l s =
    match List.find_opt (fun v -> get_literal v = l) s with
    | Some (Decision (_,p)) -> p
    | Some (UnitPropagation (_,_,p)) -> p
    | None -> -1




  let get_elem m =
    List.fold_left (fun s e ->
         Ast.Clause.add (-(get_literal e)) s  ) Ast.Clause.empty m

  let rec unit_propagate state =
    let unit_prop = ref true in
    let m = ref (get_elem state.trail) in
    while !unit_prop do
      (*print_endline "unit propagation";*)
      unit_prop := false;
(*
      Ast.Clause.iter (fun l ->
          Ast.Cnf.iter (fun cl ->
              let simpl = Ast.Clause.diff cl !m in
              if Ast.Clause.cardinal simpl = 1 then
                (
                  let l = List.hd (Ast.Clause.elements simpl) in
                  if not (Ast.Clause.mem (-l) !m) then (
                    print_endline ("learn : "^string_of_int l);
                    unit_prop := true;
                    state.trail <- (UnitPropagation (l , cl)) :: state.trail);
                    m := Ast.Clause.add (-l) !m;
                )
            )
            state.variable_clauses.(abs l)
        ) !m
*)
      Ast.Cnf.iter (fun cl ->
          let simpl = Ast.Clause.diff cl !m in
          if Ast.Clause.cardinal simpl = 1 then
            (
              let l = List.hd (Ast.Clause.elements simpl) in
              if not (Ast.Clause.mem (-l) !m) then (
                (*print_endline ("learn : "^string_of_int l);*)
                unit_prop := true;
                state.trail <- (UnitPropagation (l , cl, state.decision_level )) :: state.trail;
                state.level_var.(abs l) <- state.decision_level ;
                state.reason.(abs l) <- cl;
                m := Ast.Clause.add (-l) !m;
              )
            )
        ) state.initial_clauses.cnf;

      done;

  exception Output of Ast.model option

  let falsifies instance =
    let l = Ast.Cnf.filter (fun cl ->
        (Ast.Clause.for_all (fun l -> find_value (-l) instance.trail) cl)
      )
      instance.initial_clauses.cnf in
    (*print_string "falsifies find : ";
      Ast.pp_cnf Format.std_formatter l;*)
    if Ast.Cnf.is_empty l then None
    else Some (List.hd (Ast.Cnf.elements l))

  let analyze_conflict state f =
    let temp = ref 0 in

    let uip c =
      let m = ref ( state.trail) in
      let reason = ref c in
      let seen = ref Ast.Clause.empty in
      let learnt = ref Ast.Clause.empty in
      let ncurr = ref (0) in
      let l = ref 0 in
      let first = ref true in

      let rec get_next_l () =
        let l' = match !m with
          | t::q -> m := q; get_literal t
          | [] -> failwith "not more trail"
          in
          if Ast.Clause.mem (abs l') !seen then l'
          else get_next_l ()
      in

      while !ncurr > 0 || !first do
        first:= false;
        Ast.Clause.iter ( fun p ->
          if (not (Ast.Clause.mem (abs p) !seen)) &&
             (abs p) <> (abs !l)
          then
            begin
              seen := Ast.Clause.add (abs p) !seen;
              if state.level_var.(abs p) = state.decision_level then
                incr ncurr
              else
                learnt := Ast.Clause.add p !learnt
            end
          ) !reason;

        let l' = get_next_l()
        in
        l := l';
        reason := state.reason.(abs l');
        decr ncurr;
      done;

      if !l <> 0 then
        Ast.Clause.add ( - !l) !learnt
      else !learnt


    in

    let get_level_back l =
      let lv = ref 0 in
      Ast.Clause.iter (fun v ->
          let vlv = state.level_var.(abs v) in
          lv := max !lv (if vlv <> state.decision_level then vlv else 0)
        ) l;
      !lv
    in
    let learn = uip f in
    learn, get_level_back learn
(*
    let rec get_clause li s =
      match li with
      | (Decision (l,dl))::q ->
        temp := l;
        state.trail <- q;
        state.decision_level <- dl - 1;
        Ast.Clause.remove l (Ast.Clause.add (-l) s)
      | (UnitPropagation(l,cl,_))::q ->
        print_endline ("remove literal : "^string_of_int l);
        get_clause q (Ast.Clause.filter (fun e -> e <> -l && e <> l)
        (Ast.Clause.union s (Ast.Clause.map (fun e -> -e) cl)))
      | [] -> state.trail <- []; state.decision_level <- 0 ; s
    in
    let map a =
      Ast.Clause.map (fun e ->
          if find_value e state.trail || e = !temp then -e
          else e
        ) a
    in
    map (get_clause state.trail Ast.Clause.empty), 0
*)
  let add_learned_clause instance c =
    { instance with initial_clauses = {
          instance.initial_clauses with cnf = Ast.Cnf.add c instance.initial_clauses.cnf
        }
    }

  let backjump level state =
    state.decision_level <- level;
    let rec cut l = match l with
        | Decision (_,p)::q -> if p = level then q else cut q
        | UnitPropagation (_,_,_)::q -> cut q
        | [] -> []
    in
    state.trail <- cut state.trail

  let all_values state =
    state.initial_clauses.nb_var = List.length state.trail

  let new_decision_level state =
    state.decision_level <- state.decision_level + 1


  let choice state =
    let i = ref 1 in
    while find_literal !i state.trail do
      incr i;
    done;
    !i


  let cdcl state =
    let s = ref state in
    try
      while true do (*
        print_endline "new loop";
        print_state !s; *)
        unit_propagate !s; (*
        print_endline "after unit prop";
        print_state !s;*)
        match falsifies !s with
        | Some f -> begin
            (*print_endline "falsifies";*)
          if !s.decision_level = 0 then raise (Output None);
          let c,lv = analyze_conflict !s f in
          (*print_string ("clause add "^string_of_int (Ast.Clause.cardinal c) ^" : ");
          Ast.Clause.iter (fun v -> print_int v; print_string " ") c;
          print_endline ";";
            flush_all ();*)
          s := add_learned_clause !s c;
          backjump lv !s;
          end
        | None -> begin
          if all_values !s then raise (Output (Some []));
          (*print_endline "else";*)
          new_decision_level !s;
          let l = - (choice !s) in
          state.reason.(abs l) <- Ast.Clause.empty;
          state.level_var.(abs l) <- (!s.decision_level + 1) - 1;
          !s.trail <- (Decision (l,!s.decision_level)) :: !s.trail;
        end
      done;
      None
    with Output a -> a



    let solve (f:Ast.t): Ast.model option =
      if Horn.Horn.is_horn f then Horn.Horn.solve f
      else (
        let initial_state = {
          trail = [];
          initial_clauses = f;
          learned_clauses = Ast.Cnf.empty;
          decision_level = 0;
          model_state = Ast.Clause.empty;
          variable_clauses = Array.make (f.nb_var + 1) Ast.Cnf.empty;
          level_var = Array.make (f.nb_var + 1) (-1);
          reason = Array.make (f.nb_var + 1) Ast.Clause.empty;
        }
        in
        Ast.Cnf.iter (fun cl -> Ast.Clause.iter(fun v ->
            initial_state.variable_clauses.(abs v) <- Ast.Cnf.add cl initial_state.variable_clauses.(abs v);
          ) cl ) f.cnf;
        cdcl initial_state
      )
  end
