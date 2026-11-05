import YM.Push.COMMON_WITNESSES.Telescope
import YM.Work.A15

/-!
# Specialized field comparisons, only at origin, and reflection copies

Workable quantitative estimate input candidate for Grill on a tracking
trajectory. Here the reflecting tilings use their `omega`/translation pull
and `hand` on any comparison measurable supplied; in particular the exact
O columns themselves really give the right centered/transformed columns at
each other cell that we decide to use under `Spin.uses`. No hypotheses of
projection reflection post-selection. No support/exact many-source claims
beyond the displayed conditional type. See .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff

variable {G : Gauge} (C : Family G)

/-- Finite level register with all frames to be checked. -/
abbrev Flavour (d : ℕ) := Σ i : Fin (d+1), (C.labels.level i.val).Index × Extraction.Spin.Frame

open Extraction.Spin
variable {C} {d : ℕ}

def herb (x : Flavour C d) : C.book.Token := token C.book
    ⟨x.1.val,(Pi.basisFun ℂ ((C.labels.level x.1.val).Index)) x.2.1⟩ x.2.2

def turnField (x : Flavour C d) (r : Frame) : Flavour C d :=
    ⟨x.1,x.2.1, r.1*x.2.2.1,x.2.2.2.xor r.2⟩
lemma herb_turn (x : Flavour C d) (r : Frame) : herb (turnField x r) = token C.book (herb x) r := by
  unfold herb; rw [orientation]; rfl

variable (h N p : ℕ)

def bornField (x : Flavour C d) : Config G (C.side N p) → ℂ := C.seen (herb x) 0

variable {h N p}

/-- At one cutoff, centred root for the actual F-O column, bounded
approximant F. R is for *sup*, not assumed for primary. -/
structure DirectedField (hN : h ≤ N) (x : Flavour C d) (F : Config G (C.side N p) → ℂ) (R δ : ℝ) : Prop where
  behind : Interior ((center C.S p hN 0).chamber 0) F
  size (q) : ‖F q‖ ≤ R
  ordinary (q) : star (F q)=F q
  root : (center C.S p hN 0).rootTest (C.beta N p) (F-bornField N p x) ≤ δ

/- Build cluster anti-test approximants from these supplies. Keep the exact
Turn frame for each position after wrapping to p. No gluing of budgets beyond
what is actually given. -/
section
variable (hN : h ≤ N)
variable {n : ℕ}

abbrev canvas (C : Family G) (hN : h≤N) (p : ℕ) := center C.S p hN 0
abbrev places (C : Family G) (hN : h≤N) (p : ℕ) (y : Fin n → Cover) (a : Cover) (i : Fin n) : (canvas C hN p).Cell :=
  wrap (C.S.side h p) (y i+a)

def relocate (o : (canvas C hN p).Cell) (x : Flavour C d) :=
    turnField x ((way (canvas C hN p) o).1⁻¹,(way (canvas C hN p) o).2)

def production (Z : Flavour C d → Config G (C.side N p) → ℂ) (f : Fin n → Flavour C d)
    (y : Fin n → Cover) (a : Cover) :=
    stageProduct (canvas C hN p) (places C hN p y a) fun i => Z (relocate hN (places C hN p y a i) (f i))

/-- Exact pull/readout for the primary array used by the flash. -/
lemma in_fields (H : C.Makes) (Z : ∀ o : Flavour C d, C.ref (herb o).1 ≤ N) (f : Fin n → Flavour C d)
    (y : Fin n → Cover) (a : Cover) (q : Config G (C.side N p)) :
    production hN (bornField N p) f y a q = Grid.tiny (C:=C) h (herb ∘ f) y N p a q := by
  unfold production stageProduct Grid.tiny
  apply Finset.prod_congr rfl; intro i _
  let u := places C hN p y a i
  let W := canvas C hN p
  let x := relocate hN u (f i)
  change W.copy u (C.seen (herb x) 0) q = _
  rw [uses H W u 0 (herb x) (Z x), show token C.book (herb x) (way W u)=herb (f i) by
    unfold x relocate; rw [herb_turn,isotropy]]
  have hr : W.copyMap u 0=location C.S h N p (y i+a) := by unfold W canvas location; rw [dif_pos hN,copy_home]; simp [u]
  rw [hr]; rfl

private lemma pullJoin (Z : Flavour C d → Config G (C.side N p) → ℂ) {n m : ℕ} (f : Fin n → Flavour C d) (g : Fin m → Flavour C d)
    (y : Fin n → Cover) (w : Fin m → Cover) (a b : Cover) (q : Config G (C.side N p)) :
    let c := Fin.append (places C hN p y a) (places C hN p w b)
    production hN Z f y a q * production hN Z g w b q =
    stageProduct (canvas C hN p) c (fun i => Z (relocate hN (c i) (Fin.append f g i))) q := by
  simp only [production,stageProduct,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

lemma lawfulPair (Z : Flavour C d → Config G (C.side N p) → ℂ) (H : ∀ i, Interior ((canvas C hN p).chamber 0) (Z i))
    {n m : ℕ} (f : Fin n → Flavour C d) (g : Fin m → Flavour C d) (y : Fin n → Cover) (w : Fin m → Cover) (a b : Cover) :
    Integrable (fun q => production hN Z f y a q * production hN Z g w b q) (law G _ (C.beta N p)) := by
  simp_rw [pullJoin]; exact lawful _ _ _ fun _ => H _

/-- All cells distinct in this paired subbill. Threshold chosen BEFORE n must
support all such tests once n is fixed. -/
lemma pair_filled (Z : Flavour C d → Config G (C.side N p) → ℂ) (W : ℝ) (hW : 0 ≤ W) (R δ : ℝ)
    (hδ : 0≤δ) (hδ' : δ ≤ 1) (hp : ∀ i, DirectedField hN i (Z i) R δ) (H : C.Makes)
    (hw : ∀ i : Flavour C d, centeredBudget C (herb i) W h N p) {n m : ℕ}
    (f : Fin n → Flavour C d) (g : Fin m → Flavour C d)
    (y : Fin n → Cover) (w : Fin m → Cover) (a b : Cover) (hc : Injective (Fin.append (places C hN p y a) (places C hN p w b))) :
    let μ := law G (C.side N p) (C.beta N p)
    let B := W+1
    ‖(∫ q, production hN Z f y a q * production hN Z g w b q ∂μ) -
      (∫ q, production hN (bornField N p) f y a q * production hN (bornField N p) g w b q ∂μ)‖ ≤
      (↑(n+m:ℕ):ℝ) * (δ * B^(n+m)) := by
  intro μ B
  simp_rw [pullJoin]
  let c := Fin.append (places C hN p y a) (places C hN p w b)
  let x i := relocate hN (c i) (Fin.append f g i)
  let T := canvas C hN p
  let β := C.beta N p
  change ‖moment β (stageProduct T c _) - moment β (stageProduct T c _)‖ ≤ _
  conv_rhs => rw [← Fintype.card_fin (n+m)]
  apply replacing T c (seamless H N p) hc _ _ B δ (by unfold B; linarith) hδ
  intro i
  let X := x i
  let P := bornField N p X
  have hv : Interior (T.chamber 0) P ∧ T.rootTest β P ≤ W := (hw X).choose_spec.2 0
  have hq := hp X
  have ht : T.rootTest β (Z X) ≤ B := by
    have hh := (seamless H N p).semi T (Z X-P) P (less_f hq.behind hv.1) hv.1
    rw [sub_add_cancel] at hh
    exact hh.trans ((add_le_add hq.root hv.2).trans (by unfold B; linarith))
  exact ⟨hv.1,hq.behind,hv.2.trans (le_add_of_nonneg_right zero_le_one),ht,hq.root⟩
end
end YM.Push.Common
