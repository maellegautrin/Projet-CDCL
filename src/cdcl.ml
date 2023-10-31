module CDCL : Solver.SOLVER =
  struct


    type annoted_literal =
      | Decision of Ast.lit * int
      | UnitPropagation of Ast.lit * int list ref * int


    module ClauseMap = Map.Make(Ast.Clause)


    type instance = {
      mutable trail : annoted_literal list;
      mutable initial_clauses : Ast.t ;
      mutable decision_level : int;
      nb_var : int;
      variable : int array;
      level_var : int array;
      reason : int list ref array;
      mutable clause_list : int list ref list;
      watched_literal : int list ref list array;
      mutable literal_change : int list;
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
                                                 List.fold_right (fun e s -> s ^" "^string_of_int e) !cl ""^
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






  let get_elem_2wl m =
    List.fold_left (fun s e ->
         Ast.Clause.add ((get_literal e)) s  ) Ast.Clause.empty m


  exception UnitProp of int list ref


  let swap l i j state=
    let a = Array.of_list !l in
    let t = a.(i) in
    let i,j = if j > i then i,j else j,i in

    if i <= 1 && j <= 1 then ()
    else (
      if i <= 1 then
        (state.watched_literal.(abs a.(i)) <-
          List.filter (fun cl -> cl <> l) state.watched_literal.(abs a.(i));
         state.watched_literal.(abs a.(j)) <- l::state.watched_literal.(abs a.(j));
        )
      else ()
    );

    a.(i) <- a.(j);
    a.(j) <- t;

    l := Array.to_list a


  let rec unit_propagate_2wl state =
    let unit_prop = ref true in
    try
    while !unit_prop do
      unit_prop := false;

      let temp = state.literal_change in
      state.literal_change <- [];
      List.iter (fun v ->
          List.iter ( fun cl ->
          match !cl with
          | [] -> failwith "empty cl"
          | [l] -> if state.variable.(abs l) * l > 0 then ()
                   else if state.variable.(abs l) * l  < 0 then raise (UnitProp cl)
                   else (
                     unit_prop := true;
                     state.trail <- (UnitPropagation (l , cl , state.decision_level )) :: state.trail;
                     state.variable.(abs l) <- if l > 0 then 1 else -1;
                     state.level_var.(abs l) <- state.decision_level ;
                     state.reason.(abs l) <- cl;
                     state.literal_change <- l :: state.literal_change;
                   )
          | w1::w2::q -> begin
              let w1p = state.variable.(abs w1) * w1 > 0 and
              w2p = state.variable.(abs w2) * w2 > 0 in
              if w1p || w2p then () (* clause is true *)
              else
                let w1n = state.variable.(abs w1) * w1 < 0  and
                    w2n = state.variable.(abs w2) * w2 < 0 in
              (* undef w1 and w2 *)
              if not (w1p || w2p || w1n || w2n )  then ()
              else begin
                let first_ok = ref (not (w1p || w1n)) in (* w1 is undef *)
                if not (w2p || w2n) then (
                  swap cl 0 1 state;
                  first_ok := true
                );

                let rec new_watch l j = match l with
                  | [] ->
                    let w1' = List.hd !cl in
                    let w1p' = state.variable.(abs w1') * w1' > 0  and
                    w1n' = state.variable.(abs w1') * w1' < 0 in
                    if w1p' || w1n' then raise (UnitProp cl)
                        else (
                          let l = w1' in
                          unit_prop := true;
                          state.trail <- (UnitPropagation (l , cl , state.decision_level )) :: state.trail;
                          state.level_var.(abs l) <- state.decision_level ;
                          state.reason.(abs l) <- cl;
                          state.variable.(abs l) <- if l > 0 then 1 else -1;
                          state.literal_change <- l :: state.literal_change;
                        )
                  | t::q -> (
                      let avp = state.variable.(abs t) * t > 0 in
                      let avn = state.variable.(abs t) * t < 0  in
                      if not (avp || avn) then
                        if !first_ok then
                          swap cl 1 j state
                        else(
                          swap cl 0 j state;
                          first_ok := true;
                          new_watch q (j+1)
                        )
                      else if avp then
                        (
                          swap cl 0 j state
                        )
                        else new_watch q (j+1)
                    )
                in new_watch (match !cl with  _::_::q -> q | _ -> []) 2
              end
            end
        ) state.watched_literal.(abs v)
        )
        temp;
      done;
      None
      with UnitProp cl -> Some cl


  exception Output of Ast.model option

  let falsifies instance =
    let l = Ast.Cnf.filter (fun cl ->
        (Ast.Clause.for_all (fun l -> instance.variable.(abs l) * l < 0 ) cl)
      )
      instance.initial_clauses.cnf in
    if Ast.Cnf.is_empty l then None
    else Some (List.hd (Ast.Cnf.elements l))

  let analyze_conflict state (f:int list ref) =
    let uip (c:int list ref) =
      let m = ref ( state.trail) in
      let reason = ref !c in
      let seen = ref Ast.Clause.empty in
      let learnt = ref [] in
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
        List.iter ( fun p ->
          if (not (Ast.Clause.mem (abs p) !seen)) &&
             (abs p) <> (abs !l)
          then
            begin
              seen := Ast.Clause.add (abs p) !seen;
              if state.level_var.(abs p) = state.decision_level then
                incr ncurr
              else
                learnt := p :: !learnt
            end
          ) !reason;

        let l' = get_next_l()
        in
        l := l';
        reason := !(state.reason.(abs l'));
        decr ncurr;
      done;

      if !l <> 0 then
        ( - !l) :: !learnt
      else !learnt


    in

    let get_level_back l =
      let lv = ref 0 in
      List.iter (fun v ->
          let vlv = state.level_var.(abs v) in
          lv := max !lv (if vlv <> state.decision_level then vlv else 0)
        ) l;
      !lv
    in
    let learn = uip f in
    learn, get_level_back learn

  let get_2watcher cl state =
    let w1 = ref 0 and w2 = ref 0 in
    List.iter ( fun l ->
        if !w1 = 0 || !w2 = 0 then
        if not (state.variable.(abs l) <> 0)
              then if !w1 = 0 then w1 := l else w2 := l) cl;
    if !w1 <> 0 && !w2 <> 0 then !w1,!w2,false
    else if !w1 = 0 && !w2 = 0 then List.hd cl,List.hd (List.tl cl),false
    else if !w2 = 0 then (w2 := List.find (fun x -> x <> !w1) cl;
                          !w1,!w2,true)
    else (!w1,!w2,false)

  let add_learned_clause instance c =
    instance.initial_clauses <-
      { instance.initial_clauses with
      cnf = Ast.Cnf.add (Ast.Clause.of_list c) instance.initial_clauses.cnf;
    };
    let cl = ref c in
    instance.clause_list <- cl :: instance.clause_list;
    match !cl with
    | [] -> ()
    | [l] -> (
      instance.literal_change <- l:: instance.literal_change;
      instance.watched_literal.(abs l) <- cl :: instance.watched_literal.(abs l);
    )
    | t::q::_ ->(
        let w1,w2,update = get_2watcher !cl instance in
        instance.watched_literal.(abs w1) <- cl :: instance.watched_literal.(abs w1);
        instance.watched_literal.(abs w2) <- cl :: instance.watched_literal.(abs w2);
        if update then instance.literal_change <- w1:: instance.literal_change;
      )


  let backjump level state =
    state.decision_level <- level;
    let rec cut l = match l with
        | Decision (v,p)::q -> if p = level then
            ((*state.variable.(abs v) <- 0;*) state.literal_change <- v::state.literal_change;l)
          else (state.variable.(abs v) <- 0; state.literal_change <- v::state.literal_change; cut q)
        | UnitPropagation (v,_,_)::q -> state.variable.(abs v)<- 0 ; cut q
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


  let print_arrr a =
    Array.iteri (fun i e -> print_string (string_of_int i ^":"^ string_of_int e^" ")) a;
    print_endline ""


  let cdcl state =
    try
      while true do
        let fals = unit_propagate_2wl state in
        match fals with
        | Some f -> begin
          if state.decision_level = 0 then raise (Output None);
          let c,lv = analyze_conflict state f in
          backjump lv state;
          add_learned_clause state c;
          end
        | None -> begin
          if all_values state then raise (Output (Some (Array.to_list state.variable)));
          new_decision_level state;
          let l = (choice state) in
          state.reason.(abs l) <- ref [];
          state.level_var.(abs l) <- state.decision_level ;
          state.variable.(abs l) <- if l > 0 then 1 else -1;
          state.trail <- (Decision (l,state.decision_level)) :: state.trail;
          state.literal_change <- l :: state.literal_change;
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
          decision_level = 0;
          nb_var = f.nb_var;
          level_var = Array.make (f.nb_var + 1) (-1);
          reason = Array.make (f.nb_var + 1) (ref []);
          variable = Array.make (f.nb_var +1) 0;
          clause_list = Ast.Cnf.fold (fun v l -> ref (Ast.Clause.elements v) ::l ) f.cnf [];
          watched_literal = Array.make (f.nb_var + 1) [];
          literal_change = List.init f.nb_var (fun i -> i+1) ;
        }
        in

        List.iter (fun cl ->
            match !cl with
            | [] -> ()
            | [l] -> initial_state.watched_literal.(abs l) <- cl :: initial_state.watched_literal.(abs l)
            | t::q::_ ->(
              initial_state.watched_literal.(abs t) <- cl :: initial_state.watched_literal.(abs t);
              initial_state.watched_literal.(abs q) <- cl :: initial_state.watched_literal.(abs q))
          ) initial_state.clause_list;

        cdcl initial_state
      )
  end
