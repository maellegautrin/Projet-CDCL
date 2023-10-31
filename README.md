# Projet CDCL

## Prérequis :
Le projet utilise les mêmes dépendances que l'archive dpll donné :
    - dune
    - ocaml (>= 4.04.0)
    - menhir (2.0)

## Compilation 
Pour compiler exécutez la commande : `make`
Cela créer un éxécutable nommé `cdcl`

## Tests
Pour lancer les tests effectuez : `make tests`



# Projet :

Si la formule passé est sous forme de formule de horn, alors un solveur
pour les formules de horn est exécuté. Ce solveur utilise l'algorithme n^2.


L'algorithme CDCL, utilise 2wl. 

Cependant, après son implémentation le nombre de tests qui passent ne
semble pas avoir augmenter ou très peu (pas plus de 5 tests).

Le nombre maximal de tests fourni dans l'achive dpll qui passent n'a jamais dépassé 35 tests.
Même en essayant de tester différentes structures de données (list, Set, tableau pour sauvegarder la valuation...).
