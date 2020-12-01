(*Auteur : Elias El Yandouzi & Amad Salmon*)

(* Page 19 Section 6 du poly de TP

On veut définir une grammaire qui reconnaît des programmes comme celui-ci :

a:=1;
b:=1;
c:=1;
w(a){
 i(c){
  c:=0;
  a:=b
 }{
  b:=0;
  c:=a
 }
}

Une grammaire qui convient pourrait s'écrire naturellement ainsi :

V pour variable
C pour constante
E pour expression
I pour instruction

  V ::= a | b | c | d
  C ::= 0 | 1
  E ::= V | C
  I ::= I;I | V:=E | i.E{I}{I} | w.E{I} | ε


Mais elle est récursive à gauche.

On peut cependant réécrire I ainsi :

S pour axiome (tradition dans les grammaires)
L pour liste d'instructions

  S ::= IL | ε
  L ::= ;S | ε
  I ::= V:=E | i.E{S}{S} | w.E{S} | ε

Travail à effectuer :
- écrire en ocaml une fonction de type : string -> bool
  qui rend true ssi la string fait partie du langage défini par cette grammaire.
- Si pas fait lors de la séance précédente:
  écrire en ocaml un type d'AST pour les programmes visés et
  fonction de type : string -> ast qui rend l'AST correspondant
  si la string fait partie du langage défini par cette grammaire.
- Écrivez une autre version de vos fonctions qui utilisent des combinateurs,
  comme cela est fait dans
    https://ltpf.gricad-pages.univ-grenoble-alpes.fr/PF/anacomb.ml
- Écrivez une autre version de anacomb.ml (anacomblazy.ml), qui utilise
  des listes paresseuses
- Écrivez une autre version de vos fonctions qui utilisent les listes paresseuses
- facultatif (pas pour les paresseux donc):
  Écrivez une autre version de vos fonctions qui utilisent le type
  Stream.t (https://caml.inria.fr/pub/docs/manual-ocaml/libref/Stream.html)


Pour cela pour pourrez (devrez) vous inspirer de ce qui est fait dans
https://ltpf.gricad-pages.univ-grenoble-alpes.fr/PF/analist.ml
  *)

exception Erreur
type mwhile = char list -> char list

type var = A | B | C | D ;;
type const = Un | Zero ;;
type exp = V of var | C of const ;;
type instr = V of var | E of exp | W of exp | Vide ;;

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
in boucle s 0 (String.length s)


let terminal c : mwhile = fun l ->
  match l with
  | x::l when x = c -> l
  | _ -> raise Erreur

let (+>) (a: mwhile) (b : mwhile) : mwhile =
  fun l -> b (a l)

let (+|) (a: mwhile) (b : mwhile) : mwhile =
  fun l -> try a l with Erreur -> b l


(**Terminal fin de ligne ; *)
let term_eol : mwhile = terminal ';';;

(**Terminal pour les variables allant de a à d *)
let term_a : mwhile = terminal 'a';;
let term_b : mwhile = terminal 'b';;
let term_c : mwhile = terminal 'c';;
let term_d : mwhile = terminal 'd';;


(**Terminal pour les variables allant de 0 à 1 *)
let term_0 : mwhile = terminal '0';;
let term_1 : mwhile = terminal '1';;


(**Terminal pour le while et le if *)
let term_w : mwhile = terminal 'w';;
let term_if : mwhile = terminal 'i';;

(**Terminal pour les paranthèses et les acccolades *)
let term_pg : mwhile = terminal '(';;
let term_pd : mwhile = terminal ')';;
let term_ag : mwhile = terminal '{';;
let term_ad : mwhile = terminal '}';;

let epsilon =  fun l -> l;;

let rec p_Blanc : mwhile = 
  fun l -> (
      ((terminal ' ') +| (terminal '\n') +| (terminal '\t') +> (p_Blanc))
      +|
      (epsilon)
  ) l;;

let p_Var : mwhile = 
  fun l -> (
    (term_a +| term_b +| term_c +| term_d)
  ) l;;

let p_Cst : mwhile = 
  fun l -> (
    (term_0 +| term_1)
  ) l;;

let p_Affectation : mwhile =
  fun l -> (
      (p_Var)
    +>
      (p_Blanc +| epsilon)
    +>
      (terminal ':')
    +>
      (p_Blanc +| epsilon)
    +> 
      (terminal '=')
    +>
      (p_Blanc +| epsilon)
    +>
      (term_0 +| term_1 +| term_a +| term_b +| term_c +| term_d)
  ) l;;

 
let rec p_S : mwhile = 
  let p_L l = ((term_eol +> p_S) +| epsilon) l
  and p_I l =  ( p_Affectation 
               +| (term_w +> term_pg +> (p_Var +| p_Cst) +> term_pd +> term_ag +> p_S +> term_ad) 
               +| (term_if +> term_pg +> (p_Var +| p_Cst) +> term_pd +> term_ag +> p_S +> term_ad +> term_ag +> p_S +> term_ad) 
               +| epsilon) l
  in fun l -> ((p_I +> p_L) +| epsilon) l
  
  
let t1 = list_of_string "a:=1;";;
let _ = p_S t1;;

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string "a:=1;b:=1;i(1){b:=1}{c:=0}";;
let res = p_S t3;;

let t4 = list_of_string "i(1){b:=a}{c:=0}";;
let res = p_S t4;;

let isWhileLanguage = fun l -> let l = p_S l in
  match l with
  | [] -> true
  | _ -> false
;;

isWhileLanguage t1;;
isWhileLanguage t2;;
isWhileLanguage t3;;
isWhileLanguage t4;;
