set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 - Definirajte funkcijo, ki *rekurzivno* (torej naivno in ne direktno s formulo,
    ki jo boste morali dokazati) sešteje prvih `n` lihih naravnih števil, ter
    dokažite, da zanjo velja znana enakost.
 - Definirajte funkcijo, ki *rekurzivno* sešteje prvih `n` produktov dveh
    zaporednih naravnih števil, ter dokažite da zanjo velja znana enakost
    (najprej v obliki, ki ne zahteva deljenja, nato pa še v običajni obliki).

 Indukcijska koraka dokazov trditev `vsota_lihih_kvadrat` in `formula_produktov`
 dokažite z uporabo `calc` bloka.

 *Namig*: pri krajših manipulacijah numeričnih literalov nam taktika `rfl`
 pogosto zadostuje.
------------------------------------------------------------------------------/

-- Vsota prvih n lihih naravnih števil
def vsota_lihih : Nat → Nat :=
  fun n =>
    match n with
    | 0 => 0
    | Nat.succ k => (2 * k + 1) + vsota_lihih k

theorem vsota_lihih_kvadrat : (n : Nat) → vsota_lihih n = n * n :=
  by
    intro n
    induction n with
    | zero =>
      calc
        vsota_lihih 0
         = 0 := by simp [vsota_lihih]
        _= 0 * 0 := by rfl
    | succ k ih =>
      calc
        vsota_lihih (Nat.succ k)
         = 2 * k + 1 + vsota_lihih k := by simp [vsota_lihih]
        _= 2 * k + 1 + k * k := by rw [ih]
        _= k * k + 2 * k + 1 := by
          rw [Nat.add_assoc, Nat.add_comm 1 (k * k), ← Nat.add_assoc, Nat.add_comm (k * k) (2 * k)]
        _= (k + 1) * (k + 1) := by
          rw [Nat.two_mul, ← Nat.add_assoc, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_one, Nat.one_mul]

-- Vsota prvih n produktov zaporednih naravnih števil
def vsota_produktov : Nat → Nat :=
  fun n =>
    match n with
    | 0 => 0
    | Nat.succ k => ((k + 1) * (k + 2)) + vsota_produktov k

theorem formula_produktov : (n : Nat) → 3 * vsota_produktov n = n * (n + 1) * (n + 2) :=
  by
    intro n
    induction n with
    | zero =>
      calc
        3 * vsota_produktov 0
         = 3 * 0 := by simp [vsota_produktov]
        _= 0 * (0 + 1) * (0 + 2) := by rfl
    | succ k ih =>
      calc
        3 * vsota_produktov (Nat.succ k)
         = 3 * (((k + 1) * (k + 2)) + vsota_produktov k) := by simp [vsota_produktov]
        _= 3 * ((k + 1) * (k + 2)) + 3 * vsota_produktov k := by rw [Nat.mul_add]
        _= 3 * ((k + 1) * (k + 2)) + k * (k + 1) * (k + 2) := by rw [ih]
        _= ((k + 1) * (k + 2)) * 3 + ((k + 1) * (k + 2)) * k := by ac_rfl
        _= (k + 1) * (k + 2) * (k + 3) := by rw [← Nat.mul_add, Nat.add_comm 3 k]

theorem prava_formula_produktov : (n : Nat) → vsota_produktov n = (n * (n + 1) * (n + 2)) / 3 :=
  by
    intro n
    have h : 3 * vsota_produktov n = n * (n + 1) * (n + 2) := by rw [formula_produktov]
    have h3 : 0 < 3 := by decide
    calc
      vsota_produktov n
       = (3 * vsota_produktov n) / 3 := by rw [Nat.mul_div_cancel_left _ h3]
      _= (n * (n + 1) * (n + 2)) / 3 := by rw [h]

/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje z elementi poljubnega tipa. Za ustrezno delovanje
 zapišemo funkcijo stikanja dveh vektorjev s pomočjo taktik.

 Zapišite še funkcije:
 - `obrni`, ki vrne na vektor z elementi v obratnem vrstnem redu,
 - `preslikaj`, ki preslika vse elemente vektorja z dano funkcijo,
 - `zip`, ki združi dva vektorja v vektor parov,
 - `dolzina`, ki vrne dolžino vektorja,
 - `glava` in `rep`, ki varno vrneta glavo in rep *nepraznega* vektorja.
 Rezultati operacij na testnem vektorju `[1,2,3]` so zapisani ob koncu
 razdelka `Vektorji`.

 Dokažite tudi trditve o teh funkcijah:
 - `preslikaj_identiteto`: preslikava elementov vektorja z identiteto pusti
    vektor nespremenjen,
 - `preslikaj_kompozitum`: preslikava s kompozitumom funkcij je enaka
    kompozitumu preslikav s posameznimi funkcijami,
 - `dolzina_pravilna`: dolžina vektorja je enaka njegovi indeksirani dolžini,
 - `preslikaj_in_zip_se_ujemata`: preslikava elementov vektorja in nato
    združevanje z `zip` je enako združevanju z `zip` in nato preslikavi parov.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen =>
    by
      rw [Nat.add_comm]
      exact ys
  | .sestavljen x xs' =>
    by
      rw [Nat.add_right_comm]
      exact .sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {m : Nat} → Vektor A m → Vektor A m :=
  fun xs =>
    match xs with
    | .prazen => .prazen
    | .sestavljen x xs' => stakni (obrni xs') (.sestavljen x .prazen)

def preslikaj : {A B : Type} → {n : Nat} → (A → B) → Vektor A n → Vektor B n :=
  fun f xs =>
    match xs with
    | .prazen => .prazen
    | .sestavljen x xs' => .sestavljen (f x) (preslikaj f xs')

def zip : {A B : Type} → {n : Nat} → Vektor A n → Vektor B n → Vektor (A × B) n :=
  fun xs ys =>
    match xs, ys with
    | .prazen, .prazen => .prazen
    | .sestavljen x xs', .sestavljen y ys' => .sestavljen (x, y) (zip xs' ys')

def dolzina : {A : Type} → {n : Nat} → Vektor A n → Nat :=
  fun xs =>
    match xs with
    | .prazen => 0
    | .sestavljen _ xs' => 1 + dolzina xs'

def glava : {A : Type} → {n : Nat} → Vektor A (n + 1) → A :=
  fun xs =>
    match xs with
    | .sestavljen x _ => x

def rep : {A : Type} → {n : Nat} → Vektor A (n + 1) → Vektor A n :=
  fun xs =>
    match xs with
    | .sestavljen _ xs' => xs'

theorem preslikaj_identiteto : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  preslikaj id xs = xs :=
  by
    intros A n xs
    induction xs with
    | prazen =>
      simp [preslikaj]
    | sestavljen x xs' ih =>
      simp [preslikaj]
      rw [ih]

theorem preslikaj_kompozitum :
  {A B C : Type} → {n : Nat} → (f : A → B) → (g : B → C) → (xs : Vektor A n) →
  preslikaj (fun x => g (f x)) xs = preslikaj g (preslikaj f xs) :=
  by
    intros A B C n f g xs
    induction xs with
    | prazen =>
      simp [preslikaj]
    | sestavljen x xs' ih =>
      simp [preslikaj]
      rw [ih]

theorem dolzina_pravilna : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  dolzina xs = n :=
  by
    intros A n xs
    induction xs with
    | prazen =>
      simp [dolzina]
    | sestavljen x xs' ih =>
      simp [dolzina]
      rw [ih, Nat.add_comm]

theorem preslikaj_in_zip_se_ujemata : {A B C : Type} → {n : Nat} →
  (f : A → B) → (g : A → C) → (xs : Vektor A n) →
  zip (preslikaj f xs) (preslikaj g xs) = preslikaj (fun x => (f x, g x)) xs :=
  by
    intros A B C n f g xs
    induction xs with
    | prazen =>
      simp [preslikaj, zip]
    | sestavljen x xs' ih =>
      simp [preslikaj, zip]
      rw [ih]

-- Primeri rezultatov operacij
def primer_vektorja : Vektor Nat 3 :=
  .sestavljen 1 (.sestavljen 2 (.sestavljen 3 .prazen))

#eval obrni primer_vektorja
-- Vrne: Vektor.sestavljen 3 (Vektor.sestavljen 2 (Vektor.sestavljen 1 (Vektor.prazen)))
#eval preslikaj (fun x => x + 10) primer_vektorja
-- Vrne: Vektor.sestavljen 11 (Vektor.sestavljen 12 (Vektor.sestavljen 13 (Vektor.prazen)))
#eval zip primer_vektorja primer_vektorja
-- Vrne: Vektor.sestavljen (1, 1) (Vektor.sestavljen (2, 2) (Vektor.sestavljen (3, 3) (Vektor.prazen)))
#eval dolzina primer_vektorja
-- Vrne: 3
#eval glava primer_vektorja
-- Vrne: 1
#eval rep primer_vektorja
-- Vrne: Vektor.sestavljen 2 (Vektor.sestavljen 3 (Vektor.prazen))

/------------------------------------------------------------------------------
 ## Logične izjave in predikatni račun

 Dokažite spodnje logične trditve.

 Dokazati morate 3 izjave brez predikatov in 3 izjave s predikatoma `forall`
 in `exists`. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."

 Pri nekaterih dokazih boste potrebovali dokaze klasične logike iz modula
 `Classical`.
------------------------------------------------------------------------------/

theorem dvojna_negacija {P : Prop} : ¬¬P ↔ P :=
  by
    apply Iff.intro
    . intro h
      apply Classical.byContradiction
      . intro np
        exact h np
    . intros h np
      exact np h

theorem trojna_negacija {P : Prop} : ¬¬¬P ↔ ¬P :=
  by
    have h := dvojna_negacija (P := ¬ P)
    exact h

theorem kontrapozitivna_oblika {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) :=
  by
    apply Iff.intro
    . intros h nq p
      exact nq (h p)
    . intros h p
      apply Classical.byContradiction
      . intro nq
        exact (h nq) p

theorem pravilo_obstaja_disjunkcija : {A : Type} → {P Q : A → Prop} →
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  by
    intros A P Q
    apply Iff.intro
    . intro h
      cases h
      case intro x hpq =>
        cases hpq
        case inl hp =>
          left
          exact Exists.intro x hp
        case inr hq =>
          right
          exact Exists.intro x hq
    . intro h
      cases h
      case inl hpx =>
        cases hpx
        case intro x px => exact Exists.intro x (Or.inl px)
      case inr hqx =>
        cases hqx
        case intro x qx => exact Exists.intro x (Or.inr qx)

theorem obstaja_p_ali_za_vse_ne_p {A : Type} {P : A → Prop} :
  (∃ x, P x) ∨ (∀ x, ¬ P x) :=
  by
    have h := Classical.em (∃ x, P x)
    cases h
    case inl expx => exact Or.inl expx
    case inr nexpx =>
      right
      intros x px
      exact nexpx (Exists.intro x px)

theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intros G P g
    have h := Classical.em (∀ x, P x)
    cases h
    case inl hpx =>
      apply Exists.intro g
      . intros hpg x
        exact hpx x
    case inr nhpx =>
      have h' : ∃ x, ¬ P x :=
        by
          apply Classical.byContradiction
          . intro nex
            apply nhpx
            . intro x
              apply Classical.byContradiction
              . intro npx
                apply nex
                exact Exists.intro x npx
      cases h'
      case intro x npx =>
        apply Exists.intro x
        intro px
        contradiction

/------------------------------------------------------------------------------
 ## Dvojiška drevesa

  Podan je tip dvojiških dreves skupaj s funkcijami za zrcaljenje drevesa,
  izračun višine in velikosti drevesa.
  Dokažite trditvi:
 - `zrcaljenje_ohrani_visino`: zrcaljenje drevesa ohrani njegovo višino,
 - `visina_manjsa_ali_enaka_velikosti`: višina drevesa je vedno manjša ali
    enaka njegovi velikosti.

  V drugem delu sta definirani funkciji `vsota` in `vsota'`, ki izračunata
  vsoto vseh elementov v drevesu z naravnimi števili. Prva jo izračuna naivno,
  druga pa z uporabo pomožne funkcije z akumulatorjem. Dokažite, da obe funkciji
  dajeta enak rezultat za vsako drevo z naravnimi števili.
  Do pomožne funkcije `aux` lahko dostopate kot `vsota'.aux`.
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → A → Drevo A → Drevo A → Drevo A

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + max (visina l) (visina d)

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno x l d => .sestavljeno x (zrcali d) (zrcali l)

def velikost : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + velikost l + velikost d

theorem zrcaljenje_ohrani_visino :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t :=
  by
    intros A t
    induction t with
    | prazno => simp [zrcali, visina]
    | sestavljeno x l d ihl ihr =>
      simp [zrcali, visina]
      rw [ihl, ihr]
      rw [Nat.max_comm]

theorem visina_manjsa_ali_enaka_velikosti :
  {A : Type} → (t : Drevo A) →
  visina t ≤ velikost t :=
  by
    intros A t
    induction t with
    | prazno => simp [visina, velikost]
    | sestavljeno x l r ihl ihr =>
      simp [visina, velikost]
      rw [Nat.add_comm, Nat.add_assoc, Nat.add_comm 1 (velikost l + velikost r), ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
      apply Nat.succ_le_succ
      rw [Nat.max_le]
      constructor
      exact Nat.le_trans ihl (Nat.le_add_right (velikost l) (velikost r))
      exact Nat.le_trans ihr (Nat.le_add_left (velikost r) (velikost l))

-- Drugi del
def vsota : Drevo Nat → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno x l d => x + vsota l + vsota d

def vsota' : Drevo Nat → Nat :=
  let rec aux : Drevo Nat → Nat → Nat :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno x l d => aux l (x + aux d acc)
  fun t => aux t 0

theorem vsota_eq_vsota' : ∀ {t : Drevo Nat}, vsota t = vsota' t :=
  by
    intro t
    have pomozna : ∀ {t : Drevo Nat} {acc : Nat}, vsota'.aux t acc = vsota t + acc :=
      by
        intro t
        induction t with
        | prazno => simp [vsota, vsota'.aux]
        | sestavljeno x l r ihl ihr =>
          intro aux
          simp [vsota'.aux, vsota]
          rw [ihl, ihr]
          omega
    simp [vsota']
    rw [pomozna]
    rw [Nat.add_zero]
