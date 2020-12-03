exception Erreur
type var
type const
type exp

type winstr
type __while
type __if
type sequence
type assign

(** Définition du type lazy list *)
type 'a lazylist
type 'a contentsll

(** Type pour fonctions qui épluchent une list de terminaux *)
type 'term analist

(** Type pour fonctions qui épluchent une list de terminaux et retournent un résultat *)
type ('r, 'term) ranalist

type ('x, 't) st

val list_of_string : string -> 'term analist

val terminal : 'a -> 'a analist

val (+>) : 't analist -> ('x, 't) st -> ('x, 't) st


val (++>) : ('r, 't) ranalist -> ('r ->('x, 't) st) -> ('x, 't) st

val (+|) : ('x, 't) st -> (('x, 't) st) -> ('x, 't) st
  
val return : 'r -> ('r, 't) ranalist

  
(**Terminal fin de ligne ; *)
val term_eol : char analist

(**Terminal pour les variables allant de a à d *)
val term_a : (var, char) ranalist
val term_b : (var, char) ranalist
val term_c : (var, char) ranalist
val term_d : (var, char) ranalist

(**Terminal pour les variables allant de 0 à 1 *)
val term_0 : (const, char) ranalist
val term_1 : (const, char) ranalist 

(**Terminal pour la négation d'une variable *)
val term_neg : (const, char) ranalist 

(**Terminal pour les paranthèses et les acccolades *)
val term_pg : char analist
val term_pd : char analist
val term_ag : char analist
val term_ad : char analist

val epsilon : ('r, 'term) ranalist

val p_Blanc : char analist

val p_Var : (var, char) ranalist

val p_Cst : (const, char) ranalist

val p_Expression : (exp, char) ranalist

(** Le type (assign, char) ne marche pas winstr est obligatoire pouruqoi ?*)
val p_Affectation : (winstr, char) ranalist


val p_S : (winstr, char) ranalist

val p_L : (winstr, char) ranalist

val p_I : (winstr, char) ranalist

(** Fin de l'analyse syntaxique avec AST *) 
