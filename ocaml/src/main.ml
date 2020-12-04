(* Auteurs  : Elias El Yandouzi & Amad Salmon*)
open Config;;
open While;;
open Printf;;

(** Exercice 4 :
L'instruction If nécessite l'évaluation d'une expression bexp qui permet de déterminer la suite du programme à exécuter.
Les règles de transition de If sont donc :
  eval(bexp) = true
    E, ((if bexp) then P else Q) -> E, P
  eval(bexp) = false
    E, ((if bexp) then P else Q) -> E, Q
**)

let assert_ps = fun ps -> 
    let (ast, tab) = ps in 
      match tab with
      | nil -> true
      | _ -> false
    ;;

let print_bool = fun b -> match b with
| true ->  printf("  true \n")
| false -> printf("  false \n")
;;

(** Exercice 7 **)
printf("\n  ************  EXERCICE 7 : Test de l'analyseur  ************  \n")
let t1 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
printf("\n--> Test de l'instruction While");;
printf("\n    list_of_string \"a:=1;b:=1;w(a){b:=1}\"");;
printf("\n    Retourne un AST plein et un tableau vide ? ");;
let assert1 = assert_ps (p_S t1) in print_bool assert1;;

let t2 = list_of_string "  a:=1;b:=1;i(1){b:=1}{c:=0}";;
printf("\n--> Test de l'instruction If");;
printf("\n    list_of_string \"a:=1;b:=1;i(1){b:=1}{c:=0}\"");;
printf("\n    Retourne un AST plein et un tableau vide ? ");;
let assert2 = assert_ps (p_S t2) in print_bool assert2;;

let t3 = list_of_string "  a:=1;b:=1;a:=#;i(1){b:=1}{c:=0}";;
printf("\n--> Test de #");;
printf("\n    list_of_string \"a:=1;b:=1;a:=#;i(1){b:=1}{c:=0}\"");;
printf("\n    Retourne un AST plein et un tableau vide ? ");;
let assert3 = assert_ps (p_S t3) in print_bool assert3;;

let t4 = list_of_string
"a:=1;
c:=1;
i(0)
  {b:=1}
  {c:=0}";; 
printf("\n--> Test de l'instruction If avec blancs arbitraires");;
printf("\n    list_of_string \"\n    a:=1;\n    c:=1;\n    i(0)\n      {b:=1}\n      {c:=0}\"");;
printf("\n    Retourne un AST plein et un tableau vide ? ");;
let assert4 = assert_ps (p_S t4) in print_bool assert4;;


printf("\n\n  ************  EXERCICE 11  : Intérpréteur SOS pas à pas  ************  \n")

let instr = let (i, _) = p_S t4 in i;; 
let _ = faire_un_pas instr (init 4);;
let _ = executer instr (init 4);;

printf("\n--> Test de l'exécution interactive :\n");;
printf("\n    Liste des différentes commande exécutables :");;
printf("\n      | 'n' ou 'next' : faire un pas.");;
printf("\n      | 'q' ou 'quit' : quitte l'exécution du programme.");;
printf("\n      | 'p' ou 'print' : affiche la valeur de l'état courant.");;
printf("\n      | 'c' ou 'continue' : continuer l'exécution du programme.");;
printf("\n");;
let _ = executer_interactif instr (init 4);;