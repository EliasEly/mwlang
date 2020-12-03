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

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
in boucle s 0 (String.length s)


let terminal c : mwhile = fun l ->
  match l with
  | x::l when x = c -> l
  | _ -> raise Erreur

(* a suivi de b *)  
let (+>) (a: mwhile) (b: mwhile) : mwhile =
  fun l -> b (a l)

(* a ou b *)
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

(**Terminal pour la négation d'une variable *)
let term_neg : mwhile = terminal '#';;

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
      (p_Blanc)
    +>
      (p_Var)
    +>
      (p_Blanc)
    +>
      (terminal ':')
    +>
      (p_Blanc)
    +> 
      (terminal '=')
    +>
      (p_Blanc)
    +>
      (term_0 +| term_1 +| term_a +| term_b +| term_c +| term_d +| term_neg)
    +>
      (p_Blanc)  
  ) l;;

 
let rec p_S : mwhile = 
  let p_L l = ((term_eol +> p_Blanc +> p_S) +| epsilon) l
  and p_I l =  (p_Affectation 
               +| (term_w +> p_Blanc
                  +> term_pg +> p_Blanc +> (p_Var +| p_Cst) +> p_Blanc +> term_pd +> p_Blanc
                  +> term_ag +> p_Blanc +> p_S +> p_Blanc +> term_ad) 
               +| (term_if +> p_Blanc
                  +> 
                  term_pg +> p_Blanc +> (p_Var +| p_Cst) +> p_Blanc +> term_pd +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S +> term_ad +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S +> term_ad) 
               +| epsilon) l
  in fun l -> ((p_I +> p_L)+| epsilon) l
  
  
let t1 = list_of_string "a:=1;";;
let _ = p_S t1;;

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string "  a:=1;b:=1;i(1){b:=1}{c:=0}";;
let res = p_S t3;;

let t4 = list_of_string "i(1){b:=a}{c:=0}";;
let res = p_S t4;;

let isWhileLanguage = fun l -> let l = p_S l in
  match l with
  | [] -> true
  | _ -> false;;

isWhileLanguage t1;;
isWhileLanguage t2;;
isWhileLanguage t3;;
isWhileLanguage t4;;

(* Début de l'analyse syntaxique avec AST *)
      
type var = A | B | C | D;;
type const = Un | Zero | Opposite;;
type exp = V of var | Cst of const;;

type winstr = Vide | While of __while | If of __if | Assign of assign | Seq of sequence
and __while = exp * winstr
and __if = exp * winstr * winstr
and sequence = winstr * winstr
and assign = var * exp;;

(* Définition du type lazy list *)
type 'a lazylist = unit -> 'a contentsll
and 'a contentsll = Nil | Cons of 'a * 'a lazylist;;

(* Type pour fonctions qui épluchent une list de terminaux *)
type 'term analist = 'term lazylist -> 'term lazylist;;

(* Type pour fonctions qui épluchent une list de terminaux et retournent un résultat *)
type ('r, 'term) ranalist = 'term lazylist -> 'r * 'term lazylist;;

type ('x, 't) st = 't lazylist -> 'x

let list_of_string s =
  let rec boucle s i n = fun () ->
    if i = n then Nil else Cons(s.[i], boucle s (i+1) n)
in boucle s 0 (String.length s)

let terminal (c : 'a) : 'a analist = fun l -> 
  match l () with
  | Cons(x, l) when x = c -> l
  | _ -> raise Erreur;;

let (+>) (a: 't analist) (b: ('x, 't) st) : ( 'x, 't) st = 
  fun l -> let l = a l in b l;;

let (++>) (a: ('r, 't) ranalist) (b: 'r ->('x, 't) st) : ('x, 't) st = 
  fun l -> let (x, l) = a l in b x l;;

let (+|) (a: ('x, 't) st) (b: ('x, 't) st) : ('x, 't) st =
  fun l -> try a l with Erreur -> b l;;
  
let return : 'r -> ('r, 't) ranalist =
  fun x l -> (x, l);;

  
(**Terminal fin de ligne ; *)
let term_eol : char analist = terminal ';';;

(**Terminal pour les variables allant de a à d *)
let term_a : (var, char) ranalist = terminal 'a' +> return A;;
let term_b : (var, char) ranalist = terminal 'b' +> return B;;
let term_c : (var, char) ranalist = terminal 'c' +> return C;;
let term_d : (var, char) ranalist = terminal 'd' +> return D;;

(**Terminal pour les variables allant de 0 à 1 *)
let term_0 : (const, char) ranalist = terminal '0' +> return Zero;;
let term_1 : (const, char) ranalist  = terminal '1' +> return Un;;

(**Terminal pour la négation d'une variable *)
let term_neg : (const, char) ranalist  = terminal '#' +> return Opposite;;

(**Terminal pour les paranthèses et les acccolades *)
let term_pg : char analist = terminal '(';;
let term_pd : char analist = terminal ')';;
let term_ag : char analist = terminal '{';;
let term_ad : char analist = terminal '}';;

let epsilon =  fun l -> l;;

let rec p_Blanc : char analist = 
  fun l -> (
      ((terminal ' ') +| (terminal '\n') +| (terminal '\t') +> (p_Blanc))
      +|
      (epsilon)
  ) l;;

let p_Var : (var, char) ranalist = 
  fun l -> (
    (term_a +| term_b +| term_c +| term_d)
  ) l;;

let p_Cst : (const, char) ranalist = 
  fun l -> (
    (term_0 +| term_1 +| term_neg)
  ) l;;

let p_Expression : (exp, char) ranalist =
  fun l -> (
    (p_Var ++> fun v -> return (V v)) +| (p_Cst ++> fun c -> return (Cst c))
  ) l;;

(* Le type (assign, char) ne marche pas winstr est obligatoire pouruqoi ?*)
let p_Affectation : (winstr, char) ranalist =
  fun l -> (
      (p_Blanc)
    +>
      (p_Var) ++> fun var -> p_Blanc
    +>
      (terminal ':')
    +>
      (p_Blanc)
    +> 
      (terminal '=')
    +>
      (p_Blanc)
    +>
      (p_Expression) ++> fun value -> p_Blanc
    +> return (Assign (var, value))
  ) l;;


let rec p_S : (winstr, char) ranalist = 
  let p_L l = ((term_eol +> p_Blanc +> p_S ++> fun a -> return a) +| (epsilon +> return Vide)) l
  and p_I l =  (p_Affectation 
                +| (terminal 'w' +> p_Blanc
                  +> term_pg +> p_Blanc +> p_Expression ++> fun a -> p_Blanc +> term_pd +> p_Blanc
                  +> term_ag +> p_Blanc +> p_S ++> fun b -> p_Blanc +> term_ad +> return (While (a, b))) 
                +| (terminal 'i' +> p_Blanc
                  +> 
                  term_pg +> p_Blanc +> p_Expression ++> fun a -> p_Blanc +> term_pd +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S ++> fun b -> term_ad +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S ++> fun c -> term_ad +> return (If (a, b, c))) 
                +| (epsilon +> return Vide)) l
  in fun l -> ((p_I ++> fun a -> p_L ++> fun b -> 
  match a, b with
  | Vide, Vide -> return Vide
  | x, Vide -> return x
  | _ -> return (Seq (a, b))
  )+| (epsilon +> return Vide)) l

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string "  a:=1;b:=1;i(1){b:=1}{c:=0}";;
let _ = p_S t3;;

let t4 = list_of_string "  a:=1;b:=1;a:=#;i(1){b:=1}{c:=0}";;
let _ = p_S t4;;

(* Fin de l'analyse syntaxique avec AST *) 

type state = int list;;

type config =
  | Inter of winstr * state
  | Final of state;;

let init n  =
  let rec aux n s =
  match n with
  | 0 -> s
  | n -> aux (n-1) (0::s) in
  aux n [];;

let rec get x s = 
  match x with
  | 0 -> (match s with
          | [] -> 0
          | v::_ -> v)
  | x -> (match s with
          | [] -> 0
          | _::l -> get (x-1) l);;

let rec update s v n =
  match v with
  | 0 -> (match s with
        | [] -> [n]
        | _::l -> n::l)
  | v ->
    (match s with
      | [] -> 0::(update [] (v-1) n)
      | a::l -> a::(update l (v-1) n));;    

  
let index_var = fun e ->
  match e with
  | V A -> 0
  | V B -> 1
  | V C -> 2
  | V D -> 3
  | _ -> raise Erreur;;

let value_exp(e: exp) (s: state) : int =
  match e with
  | Cst Opposite -> (-1)
  | Cst Zero -> 0
  | Cst Un -> 1
  | _ -> get (index_var e) s;;

let eval(e: exp) (s: state) : bool =
  match e with
  | Cst Zero -> false
  | Cst Un -> true
  | Cst Opposite -> raise Erreur 
  | _ -> let v = get (index_var e) s in if v = 1 then true else false;;


let rec faire_un_pas = fun instr s -> 
  match instr with
 | Vide -> Final(s)
 | Assign(x, v) -> Final(update s (index_var (V x)) (let v = (value_exp v s) in if v = (-1) then ((-1) * (get (index_var (V x)) s) + 1) else v))
 | Seq(e1, e2) -> (match (faire_un_pas e1 s) with
                  | Inter(e1_bis, s_bis) -> Inter(Seq(e1_bis, e2), s_bis)
                  | Final(s_bis) -> Inter(e2, s_bis))
 | If(cond, e1, e2) -> (match (eval cond s) with
                      | true -> Inter(e1, s)
                      | false -> Inter(e2, s))
 | While(cond, e) -> (match (eval cond s) with
                      | true -> Inter(Seq(e, While(cond, e)), s)
                      | false -> Inter(Vide, s))
;;

let rec executer = fun instr s ->
  match (faire_un_pas instr s) with
  | Final(s) -> true
  | Inter(i1, s1) -> executer i1 s1;;

open Printf;;

let print_state = fun s ->
  let rec __print_state (s: int list)  = 
    match s with
    | x::l -> printf " %d" x; if l != [] then printf " ;" else printf " " ; __print_state l
    | [] -> ()
    in printf "["; __print_state s; printf "]";;

let rec executer_interactif = fun instr s ->
  printf "> ";
  let input = read_line() in match input with
                             | "n" | "next"  -> (match (faire_un_pas instr s) with
                                          | Final(s) -> true
                                          | Inter(i1, s1) -> executer_interactif i1 s1)
                             | "q" | "quit"  -> false
                             | "p" | "print" -> printf "L'état s vaut : "; print_state s; printf "\n" ;executer_interactif instr s
                             | "c" | "continue" -> executer instr s
                             | _ -> executer_interactif instr s;;

let t3 = list_of_string "  a:=1;c:=1;i(0){b:=1}{c:=0}";; 
let instr = let (i, _) = p_S t3 in i;; 
let _ = faire_un_pas instr (init 4);;
let _ = executer_interactif instr (init 4);;
let _ = executer instr (init 4);;
