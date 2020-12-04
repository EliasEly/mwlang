# LTPF - Projet commun

## Coq

Le fichier se trouve dans le répertoire coq.
Il contient l'intégralité des questions de la partie principale.
Les extensions concernant Pcarre et les preuves de f_SOS_1_corr et f_SOS_1_compl ont été aussi prouvées.

## Ocaml

Idem pour la partie principale.
Concernant les extenions, LazyList et Interpreteur ont été traitées.
Il y a deux fois le même programme, dans le fichier while_emacs.ml et dans les dossiers src et include.

- Le fichier while_emacs.ml permettent une execution via l'interpreteur dans emacs.
- Les fichiers dans src et include permettent de générer un executable main via la commande make.

        > make
        > ./main