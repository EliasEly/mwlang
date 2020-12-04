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

let t3 = list_of_string
"a:=1;
c:=1;
i(0)
  {b:=1}
  {c:=0}";; 
                          
let instr = let (i, _) = p_S t3 in i;; 

let _ = faire_un_pas instr (init 4);;
let _ = executer instr (init 4);;
let _ = executer_interactif instr (init 4);;