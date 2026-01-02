(*----------------------------------------------------------------------------*
 # 2. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 V domači nalogi bomo preučevali _končne avtomate_, enostavne matematične modele
 računanja. Končni avtomati sicer ne morejo opisati vseh možnih izračunov, so pa
 zelo uporabni za prepoznavanje vzorcev v nizih.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ## Deterministični končni avtomati
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 _Deterministični končni avtomat_ (_deterministic finite automaton_ oz. DFA) nad
 _abecedo_ $\Sigma$ je sestavljen iz _množice stanj_ $Q$ ter _prehodne funkcije_
 $\delta : Q \times \Sigma \rightharpoonup Q$ med njimi. Avtomat začne v enem
 izmed možnih stanj $q_0$, nato pa glede na trenutno stanje in trenutni simbol
 pizrazide v neko novo stanje in od tam nadaljuje z naslednjim znakom. Če ob
 pregledu celotnega niza konča v enem od _sprejemnih stanj_ $F \subseteq Q$, je
 niz sprejet, sicer pa ni. Prehodna funkcija $\delta$ je delno definirana. Če za
 trenutno stanje in simbol prehod ne obstaja, avtomat niz zavrne.

 Za primer si oglejmo avtomat, ki sprejema nize, sestavljene iz ničel in enic, v
 katerih je število enic deljivo s tri. Tak avtomat predstavimo z naslednjim
 diagramom, na katerem je začetno stanje označeno s puščico, sprejemna stanja pa
 so dvojno obkrožena.

 ![DFA](slike/dfa.png)

 V tem avtomatu je abeceda $\Sigma = \{ 0, 1\}$, potrebujemo pa tri stanja, za
 vsak ostanek enega, zato je $Q = \{ q_0, q_1, q_2 \}$. Začetno stanje je $q_0$,
 ki je hkrati tudi edino sprejemno stanje. Prehodna funkcija je definirana kot:

 | $\delta$ | $0$   | $1$   |
 | -------- | ----- | ----- |
 | $q_0$    | $q_0$ | $q_1$ |
 | $q_1$    | $q_1$ | $q_2$ |
 | $q_2$    | $q_2$ | $q_0$ |

 Če avtomat na primer prejme niz $10011$, bo prehajal skozi stanja:
 - Začetno stanje: $q_0$
 - Prebere $1$: prehod v $q_1$
 - Prebere $0$: stanje ostane $q_1$
 - Prebere $0$: stanje ostane $q_1$
 - Prebere $1$: prehod v $q_2$
 - Prebere $1$: prehod v $q_0$

 Ker je stanje $q_0$ sprejemno, avtomat niz sprejme.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Modul `DFA`
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri implementaciji se bomo omejili na avtomate, ki delujejo nad znaki angleške
 abecede, stanja pa bomo zaradi preglednosti predstavili kar z nizi. Take
 avtomate predstavimo s signaturo `DFA_SIG`:
[*----------------------------------------------------------------------------*)

module type DFA_SIG = sig
  type stanje = string
  type t

  (* Funkcije za grajenje *)
  (* Argument tipa [bool] pove, ali naj bo dodano stanje sprejemno *)
  val ustvari : stanje -> bool -> t
  val dodaj_stanje : stanje -> bool -> t -> t
  val dodaj_prehod : stanje -> char -> stanje -> t -> t

  (* Funkcije za poizvedovanje *)
  val seznam_stanj : t -> stanje list
  val zacetno_stanje : t -> stanje
  val je_sprejemno_stanje : t -> stanje -> bool
  val prehodna_funkcija : t -> stanje -> char -> stanje option
  val seznam_prehodov : t -> (stanje * char * stanje) list
end

(*----------------------------------------------------------------------------*
 Napišite modul `DFA`, ki zadošča zgornji signaturi.
[*----------------------------------------------------------------------------*)

module DFA : DFA_SIG = struct
  type stanje = string
  type t = {
    zacetno : stanje;
    stanja : (stanje * bool) list;
    prehodi : (stanje * char * stanje) list;
  }

  let ustvari zacetno sprejemno =
    { zacetno; stanja = [(zacetno, sprejemno)]; prehodi = [] }

  let dodaj_stanje s sprejemno a =
    if List.exists (fun (x, _) -> x = s) a.stanja then a
    else {a with stanja = (s, sprejemno) :: a.stanja}

  let dodaj_prehod s1 znak s2 a =
    {a with prehodi = (s1, znak, s2) :: a.prehodi}

  let seznam_stanj a =
    List.map fst a.stanja

  let zacetno_stanje a =
    a.zacetno

  let je_sprejemno_stanje a s =
    match List.assoc_opt s a.stanja with
    | Some b -> b
    | None -> false

  let prehodna_funkcija a s znak =
    match List.find_opt (fun (x, ch, _) -> x = s && ch = znak) a.prehodi with
    | Some (_, _, s2) -> Some s2
    | None -> None

  let seznam_prehodov a =
    a.prehodi
end

(*----------------------------------------------------------------------------*
 Primer zgornjega avtomata bi lahko zapisali kot:
[*----------------------------------------------------------------------------*)

let enke_deljive_s_3 = DFA.(
    ustvari "q0" true
    |> dodaj_stanje "q1" false
    |> dodaj_stanje "q2" false
    |> dodaj_prehod "q0" '0' "q0"
    |> dodaj_prehod "q1" '0' "q1"
    |> dodaj_prehod "q2" '0' "q2"
    |> dodaj_prehod "q0" '1' "q1"
    |> dodaj_prehod "q1" '1' "q2"
    |> dodaj_prehod "q2" '1' "q0"
)
(* val enke_deljive_s_3 : DFA.t = <abstr> *)

(*----------------------------------------------------------------------------*
 ### Izpis avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `dot_of_dfa : DFA.t -> string`, ki vrne zapis avtomata v
 formatu `dot`. Na ta način si lahko avtomat ogledate s programom
 [GraphViz](https://graphviz.org) ali kar v [spletnem
 pregledovalniku](https://www.devtoolsdaily.com/graphviz/).
[*----------------------------------------------------------------------------*)

let dot_of_dfa dfa =
  let besedilo = Buffer.create 256 in
  
  Buffer.add_string besedilo "digraph DFA {\n";
  Buffer.add_string besedilo "  rankdir=LR;\n";
  Buffer.add_string besedilo "  size=\"8,5\"\n";
  
  let sprejemna_stanja = 
    DFA.seznam_stanj dfa 
    |> List.filter (DFA.je_sprejemno_stanje dfa)
  in
  if sprejemna_stanja <> [] then
    Printf.bprintf besedilo "  node [shape = doublecircle]; %s;\n" 
      (String.concat " " sprejemna_stanja);
  
  let ostala_stanja = 
    DFA.seznam_stanj dfa 
    |> List.filter (fun s -> not (DFA.je_sprejemno_stanje dfa s))
    |> List.rev
  in
  if ostala_stanja <> [] then
    Printf.bprintf besedilo "  node [shape = circle]; %s;\n" 
      (String.concat " " ostala_stanja);
  
  let zacetno = DFA.zacetno_stanje dfa in
  Buffer.add_string besedilo "  \"\" [shape=none];\n";
  Printf.bprintf besedilo "  \"\" -> %s;\n" zacetno;
  
  let prehodi = DFA.seznam_prehodov dfa in
  List.iter (fun (s1, znak, s2) ->
    Printf.bprintf besedilo "  %s -> %s [label=\"%c\"];\n" s1 s2 znak
  ) prehodi;
  
  Buffer.add_string besedilo "}\n";
  Buffer.contents besedilo

let () = enke_deljive_s_3 |> dot_of_dfa |> print_endline

(*----------------------------------------------------------------------------*
 ### Sprejemanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite funkcijo `dfa_sprejema : DFA.t -> string -> bool`, ki preveri, ali
 avtomat sprejme podani niz.
[*----------------------------------------------------------------------------*)

let dfa_sprejema dfa niz =
  let rec preveri trenutno_stanje preostanek_niza =
    match preostanek_niza with
    | [] -> DFA.je_sprejemno_stanje dfa trenutno_stanje
    | znak :: preostanek ->
        match DFA.prehodna_funkcija dfa trenutno_stanje znak with
        | Some naslednje_stanje -> preveri naslednje_stanje preostanek
        | None -> false
  in
  preveri (DFA.zacetno_stanje dfa) (List.of_seq (String.to_seq niz))

let nizi =
  let razsiri nizi = List.map ((^) "0") nizi @ List.map ((^) "1") nizi in
  let razsiri_zadnjega =
    function
    | [] -> []
    | (zadnji :: _) as vsi -> razsiri zadnji :: vsi
  in
  let rec loop n vsi =
    if n = 0 then
      vsi |> List.rev |> List.flatten
    else
      loop (n - 1) (razsiri_zadnjega vsi)
  in
  loop 5 [[""]]
(* val nizi : string list =
  [""; "0"; "1"; "00"; "01"; "10"; "11"; "000"; "001"; "010"; "011"; "100";
   "101"; "110"; "111"; "0000"; "0001"; "0010"; "0011"; "0100"; "0101"; "0110";
   "0111"; "1000"; "1001"; "1010"; "1011"; "1100"; "1101"; "1110"; "1111"; 
   "00000"; "00001"; "00010"; "00011"; "00100"; "00101"; "00110"; "00111"; 
   "01000"; "01001"; "01010"; "01011"; "01100"; "01101"; "01110"; "01111"; 
   "10000"; "10001"; "10010"; "10011"; "10100"; "10101"; "10110"; "10111"; 
   "11000"; "11001"; "11010"; "11011"; "11100"; "11101"; "11110"; "11111"] *)

let primer_dfa = List.filter (dfa_sprejema enke_deljive_s_3) nizi
(* val primer_dfa : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)

(*----------------------------------------------------------------------------*
 ## Nedeterministični končni avtomati
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Nedeterministični končni avtomati (_nondeterministic finite automaton_ oz. NFA)
 se od determinističnih razlikujejo v dveh pogledih:
 - dopuščajo prazne prehode med stanji, torej prehode, ki se zgodijo brez branja
 simbola iz niza,
 - iz enega stanja lahko obstaja več prehodov za isti simbol.

 Prehodno funkcijo $\delta$ tako definiramo kot $\delta : Q \times (\Sigma \cup
 \{ \varepsilon \}) \rightarrow \mathcal{P}(Q)$, kjer simbol $\varepsilon$
 predstavlja prazen prehod, $\mathcal{P}(Q)$ pa je potenčna množica množice
 stanj $Q$. Vsak deterministični končni avtomat je tudi nedeterminističen končni
 avtomat, velja pa tudi obratno. Za vsak nedeterministični končni avtomat lahko
 ustvarimo ustrezen deterministični končni avtomat, ki sprejema iste nize
 (namig: za stanja ustreznega DFA vzamemo podmnožice stanj NFA).

 Avtomat sprejme niz, če obstaja pot, ki ji sledimo po prehodih z zaporednimi
 znaki niza ali praznih prehodih, tako da začnemo v začetnem stanju in končamo v
 enem od sprejemnih stanj.

 Na primer, vzemimo avtomat, ki sprejema nize, sestavljene iz ničel in enic, v
 katerih je ali število enic ali število ničel deljivo s 3. Tak avtomat je
 sestavljen iz začetnega stanja, s praznim prehodom v eno kopijo prejšnjega
 avtomata ter še enim praznim prehodom v drugo kopijo, v kateri zamenjamo vlogi
 znakov.

 ![NFA](slike/nfa.png)

 Kot pri primeru za deterministični avtomat je avtomat definiran nad abecedo
 $\Sigma = \{ 0, 1\}$, stanj je tokrat sedem, poleg začetnega še po tri v vsaki
 _kopiji_ avtomata iz prvega primera. Tako je $Q = \{ q_0, q_{00}, q_{01},
 q_{02}, q_{10}, q_{11}, q_{12} \}$. Začetno stanje je $q_0$, sprejemni pa sta
 $q_{00}$ in $q_{10}$. Prehodna funkcija je definirana kot:

 | $\delta$   | `0`          | `1`          | $\varepsilon$ |
 | ---------- | ------------ | ------------ | ------------- |
 | $q_0$      | $\emptyset$  | $\emptyset$  | $\{q_{00}\}$  |
 | $q_0$      | $\emptyset$  | $\emptyset$  | $\{q_{10}\}$  |
 | $q_{00}$   | $\{q_{01}\}$ | $\{q_{00}\}$ | $\emptyset$   |
 | $q_{01}$   | $\{q_{02}\}$ | $\{q_{01}\}$ | $\emptyset$   |
 | $q_{02}$   | $\{q_{00}\}$ | $\{q_{02}\}$ | $\emptyset$   |
 | $q_{10}$   | $\{q_{10}\}$ | $\{q_{11}\}$ | $\emptyset$   |
 | $q_{11}$   | $\{q_{11}\}$ | $\{q_{12}\}$ | $\emptyset$   |
 | $q_{12}$   | $\{q_{12}\}$ | $\{q_{10}\}$ | $\emptyset$   |

 Če avtomat prejme niz `10011`, bo prehajal skozi stanja:
 - Začetno stanje: $q_0$
 - Pred branjem znaka `1` se lahko po praznih prehodih premakne v stanji
 $q_{00}$ in $q_{10}$, tako da so njegova možna stanja $\{q_0, q_{00}, q_{10}\}$
 - Prebere `1`: vsa tri možna stanja se premaknejo, če se lahko (stanje $q_0$
 nima možnega premika), tako so možna stanja $\{q_{01}, q_{10}\}$
 - Pred branjem novega znaka se zopet lahko vsa možna stanja premaknejo po
 praznih prehodih, a ker teh ni, ostaneta možni stanji $\{q_{01}, q_{10}\}$
 - Prebere `0`: po prehodih so možna stanja $\{q_{01}, q_{11}\}$
 - Prazni premiki in branje `0`: možna stanja $\{q_{02}, q_{11}\}$
 - Prazni premiki in branje `1`: možna stanja $\{q_{02}, q_{12}\}$
 - Prazni premiki in branje `1`: možna stanja $\{q_{02}, q_{10}\}$
 - Prazni premiki: možna stanja ostanejo $\{q_{02}, q_{10}\}$

 Ker je stanje $q_{10}$ sprejemno, avtomat niz sprejme.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Modul `NFA`
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Nedeterministične avtomate predstavimo s signaturo `NFA_SIG`, podobno zgornji:
[*----------------------------------------------------------------------------*)

module type NFA_SIG = sig
  type stanje = string
  type t

  (* Funkcije za grajenje *)
  val ustvari : stanje -> bool -> t
  val dodaj_stanje : stanje -> bool -> t -> t
  val dodaj_prehod : stanje -> char -> stanje -> t -> t
  val dodaj_prazen_prehod : stanje -> stanje -> t -> t

  (* Funkcije za poizvedovanje *)
  val seznam_stanj : t -> stanje list
  val zacetno_stanje : t -> stanje
  val je_sprejemno_stanje : t -> stanje -> bool
  val prehodna_funkcija : t -> stanje -> char option -> stanje list
  val seznam_prehodov : t -> (stanje * char option * stanje) list
end

(*----------------------------------------------------------------------------*
 Napišite modul `NFA`, ki zadošča zgornji signaturi.
[*----------------------------------------------------------------------------*)

module NFA : NFA_SIG = struct
  type stanje = string
  type t = {
    zacetno : stanje;
    stanja : (stanje * bool) list;
    prehodi : (stanje * char option * stanje) list;
  }

  let ustvari zacetno sprejemno =
    {zacetno; stanja = [(zacetno, sprejemno)]; prehodi = []}

  let dodaj_stanje s sprejemno a =
    if List.exists (fun (x, _) -> x = s) a.stanja then a
    else {a with stanja = (s, sprejemno) :: a.stanja}

  let dodaj_prehod s1 znak s2 a =
    {a with prehodi = (s1, Some znak, s2) :: a.prehodi}

  let dodaj_prazen_prehod s1 s2 a =
    {a with prehodi = (s1, None, s2) :: a.prehodi}

  let seznam_stanj a =
    List.map fst a.stanja

  let zacetno_stanje a =
    a.zacetno

  let je_sprejemno_stanje a s =
    match List.assoc_opt s a.stanja with
    | Some b -> b
    | None -> false

  let prehodna_funkcija a s simbol =
    a.prehodi
    |> List.filter (fun (s1, znak, s2) -> s1 = s && znak = simbol)
    |> List.map (fun (_, _, s2) -> s2)

  let seznam_prehodov a =
    a.prehodi
end

(*----------------------------------------------------------------------------*
 Primer zgornjega avtomata bi lahko zapisali kot:
[*----------------------------------------------------------------------------*)

let enke_ali_nicle_deljive_s_3 = NFA.(
    ustvari "q0" false
    |> dodaj_stanje "q00" true
    |> dodaj_stanje "q01" false
    |> dodaj_stanje "q02" false
    |> dodaj_prehod "q00" '0' "q01"
    |> dodaj_prehod "q01" '0' "q02"
    |> dodaj_prehod "q02" '0' "q00"
    |> dodaj_prehod "q00" '1' "q00"
    |> dodaj_prehod "q01" '1' "q01"
    |> dodaj_prehod "q02" '1' "q02"
    |> dodaj_stanje "q10" true
    |> dodaj_stanje "q11" false
    |> dodaj_stanje "q12" false
    |> dodaj_prehod "q10" '1' "q11"
    |> dodaj_prehod "q11" '1' "q12"
    |> dodaj_prehod "q12" '1' "q10"
    |> dodaj_prehod "q10" '0' "q10"
    |> dodaj_prehod "q11" '0' "q11"
    |> dodaj_prehod "q12" '0' "q12"
    |> dodaj_prazen_prehod "q0" "q00"
    |> dodaj_prazen_prehod "q0" "q10"
)
(* val enke_ali_nicle_deljive_s_3 : NFA.t = <abstr> *)

(*----------------------------------------------------------------------------*
 ### Izpis avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `dot_of_nfa : NFA.t -> string`, ki vrne zapis avtomata v
 formatu `dot`.
[*----------------------------------------------------------------------------*)

let dot_of_nfa nfa =
  let besedilo = Buffer.create 256 in
  Buffer.add_string besedilo "digraph NFA {\n";
  Buffer.add_string besedilo "  rankdir=LR;\n";
  Buffer.add_string besedilo "  size=\"8,5\"\n";

  let sprejemna_stanja = 
    NFA.seznam_stanj nfa 
    |> List.filter (NFA.je_sprejemno_stanje nfa)
    |> List.rev
  in
  if sprejemna_stanja <> [] then
    Printf.bprintf besedilo "  node [shape = doublecircle]; %s;\n" 
      (String.concat " " sprejemna_stanja);
  
  let ostala_stanja = 
    NFA.seznam_stanj nfa 
    |> List.filter (fun s -> not (NFA.je_sprejemno_stanje nfa s))
    |> List.rev
  in
  if ostala_stanja <> [] then
    Printf.bprintf besedilo "  node [shape = circle]; %s;\n" 
      (String.concat " " ostala_stanja);
  
  let zacetno = NFA.zacetno_stanje nfa in
  Buffer.add_string besedilo "  \"\" [shape=none];\n";
  Printf.bprintf besedilo "  \"\" -> %s;\n" zacetno;
  
  let prehodi = NFA.seznam_prehodov nfa in
  List.iter (fun (s1, znak_opt, s2) ->
    match znak_opt with
    | Some znak -> Printf.bprintf besedilo "  %s -> %s [label=\"%c\"];\n" s1 s2 znak
    | None -> Printf.bprintf besedilo "  %s -> %s [label=\"ɛ\"];\n" s1 s2
  ) prehodi;
  
  Buffer.add_string besedilo "}\n";
  Buffer.contents besedilo

let () = enke_ali_nicle_deljive_s_3 |> dot_of_nfa |> print_endline

(*----------------------------------------------------------------------------*
 ### Sprejemanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite funkcijo `nfa_sprejema : NFA.t -> string -> bool`, ki preveri, ali
 avtomat sprejme podani niz.
[*----------------------------------------------------------------------------*)

let nfa_sprejema nfa niz =
  let rec najdi_mozna_stanja stanja =
    let povezana_stanja =
      stanja
      |> List.map (fun stanje -> NFA.prehodna_funkcija nfa stanje None)
      |> List.flatten
      |> List.sort_uniq compare
    in
    let nova = (stanja @ povezana_stanja) |> List.sort_uniq compare
    in
    if List.length nova = List.length stanja then stanja
    else najdi_mozna_stanja nova
  in
  let rec preveri trenutna_stanja preostali_znaki =
    match preostali_znaki with
    | [] -> List.exists (NFA.je_sprejemno_stanje nfa) trenutna_stanja
    | znak :: rep ->
        let vsa_stanja = najdi_mozna_stanja trenutna_stanja in
        let nova_stanja =
          vsa_stanja
          |> List.map (fun stanje -> NFA.prehodna_funkcija nfa stanje (Some znak))
          |> List.flatten
          |> List.sort_uniq compare
        in
        if nova_stanja = [] then false
        else preveri nova_stanja rep
  in
  let zacetna_stanja = najdi_mozna_stanja [NFA.zacetno_stanje nfa] in
  let znaki = List.of_seq (String.to_seq niz) in
  preveri zacetna_stanja znaki

let primer_nfa = List.filter (nfa_sprejema enke_ali_nicle_deljive_s_3) nizi
(* val primer_nfa : string list =
  [""; "0"; "1"; "00"; "11"; "000"; "111"; "0000"; "0001"; "0010"; "0100";
   "0111"; "1000"; "1011"; "1101"; "1110"; "1111"; "00000"; "00011"; "00101";
   "00110"; "00111"; "01001"; "01010"; "01011"; "01100"; "01101"; "01110";
   "10001"; "10010"; "10011"; "10100"; "10101"; "10110"; "11000"; "11001";
   "11010"; "11100"; "11111"] *)

(*----------------------------------------------------------------------------*
 ## Regularni izrazi
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Regularni izrazi so formalni opisi jezikov (množic nizov) nad abecedo $\Sigma$.
 Uporabljajo se za kompaktno opisovanje vzorcev, ki jim morajo nizi ustrezati.
 Rečemo, da niz *ustreza* regularnemu izrazu, če ga lahko zgradimo z
 upoštevanjem pravil, ki jih določa ta re.

 Regularni izrazi so sestavljeni iz osnovnih elementov in operacij:

 - $\emptyset$ ne ustreza nobenemu jeziku,
 - $\varepsilon$ ustreza prazen niz,
 - za vsak znak $a \in \Sigma$, izrazu $a$ ustreza natanko natanko niz dolžine
 1, sestavljenem le iz znaka $a$,
 - *uniji* $r_1 \mid r_2$ ustreza vsem nizom, ki ustrezajo $r_1$ ali $r_2$,
 - *stiku* $r_1 r_2$ ustrezajo vsi nizi oblike $s_1 s_2$, kjer $s_1$ ustreza
 $r_1$ ter $s_2$ ustreza $r_2$,
 - *Kleenejevemu zaprtju* $r^*$ ustrezajo vsi nizi oblike $s_1 s_2 \cdots s_n$
 za nek $n$ (vključno s praznim nizom), kjer vsak izmed nizov $s_i$ ustreza $r$.

 Za primer si oglejmo regularni izraz $a^* b$. Ta izraz je sestavljen kot stik
 izrazov $a^*$ in $b$ in tako sprejme vse nize, ki se začnejo s poljubnim
 številom ponovitev (lahko nič) znaka $a$ in končajo z znakom $b$. Izrazu tako
 ustreza niz $aaab$, niz $aaabb$ pa ne. Nize, v katerih je število enk deljivo s
 tri, bi lahko opisali z regularnim izrazom $0^*( 10^*10^*10^* )^*$.

 Regularne izraze bomo implementirali z algebrajskim tipom, ki ima za
 konstruktorje zgoraj naštete osnovne elemente in operacije na regularnih
 izrazih.
[*----------------------------------------------------------------------------*)

type regex =
  | Empty
  | Eps
  | Char of char
  | Union of regex * regex
  | Concat of regex * regex
  | Star of regex

let re_enke_deljive_s_3 =
  let poljubno_nicel = Star (Char '0') in
  let enka_in_poljubno_nicel = Concat (Char '1', poljubno_nicel) in
  Concat (poljubno_nicel, Star (Concat (Concat (enka_in_poljubno_nicel, enka_in_poljubno_nicel), enka_in_poljubno_nicel)))
(* val re_enke_deljive_s_3 : regex =
  Concat (Star (Char '0'),
   Star
    (Concat
      (Concat (Concat (Char '1', Star (Char '0')),
        Concat (Char '1', Star (Char '0'))),
      Concat (Char '1', Star (Char '0'))))) *)

(*----------------------------------------------------------------------------*
 ### Izpisovanje
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `string_of_regex : Regex.t -> string`, ki regularni izraz
 predstavi z nizom. Pri tem poskusite zapisati čim manj oklepajev, upoštevaje
 to, da ima Kleenejevo zaprtje najvišjo prioriteto, sledi stik, nato pa unija.
 Poleg tega sta stik in unija asociativni operaciji.
[*----------------------------------------------------------------------------*)

let string_of_regex re =
  let prioriteta = function
    | Union _ -> 1 
    | Concat _ -> 2 
    | Star _ -> 3 
    | _ -> 4 
  in
  let rec pretvori prior re =
    let prioriteta_re = prioriteta re in
    let niz =
      match re with
      | Empty -> "∅"
      | Eps -> "ε"
      | Char c -> String.make 1 c
      | Union (levi, desni) ->
          let levi_niz = pretvori prioriteta_re levi in
          let desni_niz = pretvori prioriteta_re desni in
          levi_niz ^ "|" ^ desni_niz
      | Concat (levi, desni) ->
          let levi_niz = pretvori prioriteta_re levi in
          let desni_niz = pretvori prioriteta_re desni in
          levi_niz ^ desni_niz
      | Star r ->
          let niz_r = pretvori prioriteta_re r in
          niz_r ^ "*"
    in
    if prioriteta_re < prior then "(" ^ niz ^ ")" 
    else niz
  in
  pretvori 0 re

let primer_regex_1 = string_of_regex re_enke_deljive_s_3
(* val primer_regex_1 : string = "0*(10*10*10*)*" *)

(*----------------------------------------------------------------------------*
 ### Sprejeti nizi
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `regex_sprejema: regex -> string -> bool`, ki preveri, ali
 dan niz ustreza regularnemu izrazu.
[*----------------------------------------------------------------------------*)

let rec regex_sprejema re niz =
  match re with
  | Empty -> false 
  | Eps -> niz = "" 
  | Char znak -> niz = String.make 1 znak 
  | Union (levi, desni) -> regex_sprejema levi niz || regex_sprejema desni niz 
  | Concat (levi, desni) ->
      let dolzina = String.length niz in
      let rec pomozna1 i =
        if i > dolzina then false
        else
          let prvi = String.sub niz 0 i
          and drugi = String.sub niz i (dolzina - i) in
          (regex_sprejema levi prvi && regex_sprejema desni drugi) || pomozna1 (i + 1)
      in
      pomozna1 0
  | Star r ->
      if niz = "" then true
      else
        let dolzina = String.length niz in
        let rec pomozna2 i =
          if i > dolzina then false
          else
            let prvi = String.sub niz 0 i
            and drugi = String.sub niz i (dolzina - i) in
            (regex_sprejema r prvi && regex_sprejema (Star r) drugi) || pomozna2 (i + 1)
        in
        pomozna2 1

let primer_regex_2 = regex_sprejema re_enke_deljive_s_3 "10011"
(* val primer_regex_2 : bool = true *)

let primer_regex_3 = regex_sprejema re_enke_deljive_s_3 "100111"
(* val primer_regex_3 : bool = false *)

(*----------------------------------------------------------------------------*
 ### Od regularnega izraza do avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Izkaže se, da med regularnimi izrazi in nedeterminističnimi končnimi avtomati
 obstaja ekvivalenca. Za vsak izraz obstaja ustrezen avtomat, ki sprejema iste
 nize in obratno. Mi bomo ekvivalenco pokazali le v eno stran tako, da bomo za
 vsak konstruktor regularnih izrazov definirali ustrezno konstrukcijo na končnih
 avtomatih.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Definirajte avtomat `prazen_nfa: NFA.t`, ki ne sprejme nobenega niza.
[*----------------------------------------------------------------------------*)

let prazen_nfa = 
  NFA.ustvari "q0" false

let primer_regex_4 = List.filter (nfa_sprejema prazen_nfa) nizi
(* val primer_regex_4 : string list = [] *)

(*----------------------------------------------------------------------------*
 Definirajte avtomat `epsilon_nfa: NFA.t`, ki sprejme natanko prazen niz.
[*----------------------------------------------------------------------------*)

let epsilon_nfa = 
  NFA.ustvari "q0" true

let primer_regex_5 = List.filter (nfa_sprejema epsilon_nfa) nizi
(* val primer_regex_5 : string list = [""] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `znak_nfa: char -> NFA.t`, ki vrne avtomat, ki sprejme
 natanko niz dolžine ena z znakom v argumentu.
[*----------------------------------------------------------------------------*)

let znak_nfa niz =
  NFA.ustvari "q0" false
  |> NFA.dodaj_stanje "q1" true
  |> NFA.dodaj_prehod "q0" niz "q1"

let primer_regex_6 = List.filter (nfa_sprejema (znak_nfa '0')) nizi
(* val primer_regex_6 : string list = ["0"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `unija_nfa: NFA.t -> NFA.t -> NFA.t`, ki vrne avtomat, ki
 sprejme nize sprejete s katerim koli izmed avtomatov v argumentih.
[*----------------------------------------------------------------------------*)

let unija_nfa avt1 avt2 =
  let pomozna predpona avto =
    let stanja = NFA.seznam_stanj avto in
    let prehodi = NFA.seznam_prehodov avto in
    let zacetno = NFA.zacetno_stanje avto in
    let nova_stanja =
      List.map (fun stanje -> (predpona ^ stanje, NFA.je_sprejemno_stanje avto stanje)) stanja
    in
    let novi_prehodi =
      List.map (fun (s1, c, s2) -> (predpona ^ s1, c, predpona ^ s2)) prehodi
    in
    (nova_stanja, novi_prehodi, predpona ^ zacetno)
  in

  let (stanja1, prehodi1, zacetno1) = pomozna "A_" avt1 in
  let (stanja2, prehodi2, zacetno2) = pomozna "B_" avt2 in

  let novo = "novo_zacetno_stanje" in
  let nfa = NFA.ustvari novo false in

  let nfa = List.fold_left (fun n (stanje, vrednost) -> NFA.dodaj_stanje stanje vrednost n) nfa stanja1 in
  let nfa = List.fold_left (fun n (stanje, vrednost) -> NFA.dodaj_stanje stanje vrednost n) nfa stanja2 in

  let pomozna2 n (s1, c, s2) =
    match c with
    | Some x -> NFA.dodaj_prehod s1 x s2 n
    | None -> NFA.dodaj_prazen_prehod s1 s2 n
  in
  let nfa = List.fold_left pomozna2 nfa prehodi1 in
  let nfa = List.fold_left pomozna2 nfa prehodi2 in

  let nfa = NFA.dodaj_prazen_prehod novo zacetno1 nfa in
  let nfa = NFA.dodaj_prazen_prehod novo zacetno2 nfa in

  nfa

let primer_regex_7 = List.filter (nfa_sprejema (unija_nfa epsilon_nfa (znak_nfa '0'))) nizi
(* val primer_regex_7 : string list = [""; "0"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `stik_nfa: NFA.t -> NFA.t -> NFA.t`. Vrnjeni avtomat
 sprejme nize sestavljene iz stika prvega dela, ki ga sprejme avtomat v prvem
 argumentu, in drugega dela, ki ga sprejme avtomat v drugem argumentu.
[*----------------------------------------------------------------------------*)

let stik_nfa avt1 avt2 =
  let pomozna predpona avto =
    let stanja = NFA.seznam_stanj avto in
    let prehodi = NFA.seznam_prehodov avto in
    let zacetno = NFA.zacetno_stanje avto in
    let nova_stanja =
      List.map (fun stanje -> (predpona ^ stanje, NFA.je_sprejemno_stanje avto stanje)) stanja
    in
    let novi_prehodi =
      List.map (fun (s1, znak, s2) -> (predpona ^ s1, znak, predpona ^ s2)) prehodi
    in
    (nova_stanja, novi_prehodi, predpona ^ zacetno)
  in

  let (stanja1, prehodi1, zacetno1) = pomozna "A_" avt1 in
  let (stanja2, prehodi2, zacetno2) = pomozna "B_" avt2 in

  let nfa = NFA.ustvari zacetno1 false in

  let nfa = List.fold_left (fun nfa (stanje, _) -> 
      NFA.dodaj_stanje stanje false nfa) nfa stanja1 in
  let nfa = List.fold_left (fun nfa (stanje, sprejemno) -> 
      NFA.dodaj_stanje stanje sprejemno nfa) nfa stanja2 in

  let pomozna2 n (s1, znak, s2) =
    match znak with
    | Some x -> NFA.dodaj_prehod s1 x s2 n
    | None -> NFA.dodaj_prazen_prehod s1 s2 n
  in
  
  let nfa = List.fold_left pomozna2 nfa prehodi1 in
  let nfa = List.fold_left pomozna2 nfa prehodi2 in

  let nfa =
    List.fold_left (fun nfa (stanje, sprejemno) -> 
      if sprejemno then NFA.dodaj_prazen_prehod stanje zacetno2 nfa else nfa) nfa stanja1
  in

  nfa

let primer_regex_8 = List.filter (nfa_sprejema (stik_nfa (znak_nfa '0') (znak_nfa '1'))) nizi
(* val primer_regex_8 : string list = ["01"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `kleenejevo_zaprtje_nfa: NFA.t -> NFA.t`. Vrnjeni avtomat
 naj sprejme nize, ki jih dobimo s poljubnim ponavljanjem nizov, ki jih sprejme
 avtomat v argumentu.
[*----------------------------------------------------------------------------*)

let kleenejevo_zaprtje_nfa avt =
  let pomozna predpona avto =
    let stanja = NFA.seznam_stanj avto in
    let prehodi = NFA.seznam_prehodov avto in
    let zacetno = NFA.zacetno_stanje avto in

    let nova_stanja =
      List.map (fun stanje -> (predpona ^ stanje, NFA.je_sprejemno_stanje avto stanje)) stanja
    in
    let novi_prehodi =
      List.map (fun (s1, znak, s2) -> (predpona ^ s1, znak, predpona ^ s2)) prehodi
    in
    (nova_stanja, novi_prehodi, predpona ^ zacetno)
  in

  let (stanja, prehodi, zacet) = pomozna "A_" avt in

  let novo_zacetno = "novo" in
  let nfa = NFA.ustvari novo_zacetno true in

  let nfa = List.fold_left (fun n (stanje, sprejemno) -> NFA.dodaj_stanje stanje sprejemno n) nfa stanja in

  let pomozna2 n (s1, c, s2) =
    match c with
    | Some x -> NFA.dodaj_prehod s1 x s2 n
    | None -> NFA.dodaj_prazen_prehod s1 s2 n
  in
  let nfa = List.fold_left pomozna2 nfa prehodi in

  let nfa = NFA.dodaj_prazen_prehod novo_zacetno zacet nfa in
  let nfa = List.fold_left (fun n (stanje, sprejemno) ->
      if sprejemno then NFA.dodaj_prazen_prehod stanje zacet n else n) nfa stanja
  in

  nfa

let primer_regex_9 = List.filter (nfa_sprejema (kleenejevo_zaprtje_nfa (znak_nfa '0'))) nizi
(* val primer_regex_9 : string list = [""; "0"; "00"; "000"; "0000"; "00000"] *)

(*----------------------------------------------------------------------------*
 Zgoraj definirane funkcije združite v definicijo funkcijo `nfa_of_regex: regex
 -> NFA.t`, ki danemu regularnemu izrazu priredi `NFA`, ki sprejme isti jezik.
[*----------------------------------------------------------------------------*)

let rec nfa_of_regex re =
  match re with
  | Empty -> prazen_nfa
  | Eps -> epsilon_nfa
  | Char c -> znak_nfa c
  | Union (r1, r2) -> unija_nfa (nfa_of_regex r1) (nfa_of_regex r2)
  | Concat (r1, r2) -> stik_nfa (nfa_of_regex r1) (nfa_of_regex r2)
  | Star r -> kleenejevo_zaprtje_nfa (nfa_of_regex r)

let primer_regex_10 = List.filter (nfa_sprejema (nfa_of_regex re_enke_deljive_s_3)) nizi
(* val primer_regex_10 : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)

let primer_regex_11 = List.filter (regex_sprejema re_enke_deljive_s_3) nizi
(* val primer_regex_11 : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)


