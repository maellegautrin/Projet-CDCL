(*1. Sélectionner une variable et lui attribuer une valeur (True ou False). Cela crée un état de décision. Il est généralement préférable de choisir une variable basée sur une heuristique, comme la variable la plus fréquemment utilisée ou la variable la moins attribuée.
2. Appliquer la propagation des contraintes booléennes (unit propagation). Cela signifie que vous vérifiez quelles clauses sont maintenant satisfaites ou insatisfaites en raison de la nouvelle attribution, et vous mettez à jour les valeurs des autres variables en conséquence. Par exemple, si une clause devient satisfaite, vous pouvez marquer certaines variables comme vraies, et si une clause devient insatisfaite, vous pouvez détecter un conflit.
3. Construire le graphe d'implication. Cela consiste à suivre les dépendances entre les variables en fonction des clauses satisfaites ou insatisfaites. Le graphe d'implication vous aide à suivre pourquoi certaines valeurs ont été attribuées.
4. En cas de conflit, vous devez résoudre ce conflit. Pour ce faire, vous devez :
Trouver le "cut" (coupure) dans le graphe d'implication qui a conduit au conflit. Le "cut" est une séparation dans le graphe où la contradiction a été introduite.
Dériver une nouvelle clause qui est la négation des attributions qui ont conduit au conflit. Cette clause sera ajoutée aux clauses existantes pour aider à éviter de futurs conflits similaires.
5. Non-chronologiquement "backtrack" (retour en arrière) jusqu'au niveau de décision approprié, où la première variable attribuée impliquée dans le conflit a été attribuée. Cela signifie annuler certaines attributions et revenir à un état antérieur où des décisions différentes peuvent être prises.
6. Sinon, si aucun conflit n'est détecté, vous pouvez continuer à partir de l'étape 1 avec une nouvelle décision.
L'algorithme CDCL se répète jusqu'à ce que toutes les variables aient été attribuées ou qu'il soit déterminé qu'aucune attribution ne permet de satisfaire toutes les contraintes. Cet algorithme est très efficace pour résoudre des problèmes CSP, y compris le problème SAT, et est utilisé dans de nombreux solveurs SAT modernes.*)

type clause = int list
type implication_graph = (int * int) list

(* Sélection de la prochaine variable à attribuer *)
let select_variable assignment clauses =
  let rec find_unassigned_var vars =
    match vars with
    | [] -> raise Not_found (* Toutes les variables sont attribuées *)
    | x :: xs ->
        if List.mem x assignment then find_unassigned_var xs
        else x
  in
  find_unassigned_var clauses

(* Application la propagation des contraintes *)
let rec propagate assignment clauses =
  match clauses with
  | [] -> assignment (* Toutes les clauses sont satisfaites, renvoyer l'attribution *)
  | c :: rest ->
      (* Vérifier si la clause est satisfaite *)
      let satisfied = List.exists (fun x -> List.mem x assignment) c in
      if satisfied then
        propagate assignment rest
      else
        (* Trouver une variable non attribuée dans la clause *)
        let unassigned_var =
          try List.find (fun x -> not (List.mem x assignment)) c with
          | Not_found -> raise (Conflict c) (* Il y a un conflit dans la clause *)
        in
        (* Attribuer la variable à true *)
        let new_assignment = unassigned_var :: assignment in
        propagate new_assignment clauses
