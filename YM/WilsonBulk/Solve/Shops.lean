import YM.WilsonBulk.Solve.Shifter

/-!
# Curriculum ledger expressed on actual admissible data (*Key cyc*)

Convention that step price μ i refers to patch on COARSE mesh where Pose at fine i+1. Vacuum Book ℕ cutoff > i uses top upstream N. Press before reexp linear in full O₀ field-variable. 

Supplies coefficient estimates all measured in public native meshes; budget pressure insertion at source grammar later. Chemistry `σ costs` chosen before lengths; see explicit feasibility discussion/providers. Not cyclical scheduler C-history. Invoice `Land` only demands structural/flat and one-step readiness (including Hess top feasibility at input & µ variation of Γ, which `lighting ...` must supply *not* assume in final theorem). Desire prove ∃ infinitely fine beyond ℓ. require actual UV..
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A}
-- single-width curriculum
structure Shop (H : Horizon A) where
  ruler : MapPrices
  motion : Motions A
  sufficient : H.Suffices ruler
  atlasJ : LocalRatio motion.j
  E : ℕ -- demand inc attach any finite; Epoch cutoff admissions
  σ : ℕ→ℝ
  μ : ℕ→ℝ
  a : ℝ
  b : ℝ
  aha : a < 1
  bah : 0 < b
  has : b < a
  book : ℝ→ℝ
  ticket : Tariff book
namespace Shop
variable (U : Shop H)
abbrev rankMax : ℕ := U.E+2
abbrev main : ℕ→ℕ→ Library G:= apotheosis H U.motion
abbrev raw (N i : ℕ) : Library G:= theatre H U.motion N i (U.main N (i+1))
lemma main_welfare (N i : ℕ) (hi : i≤N) : Healthy U.motion.k (U.main N i) (H.H N i) := kernel_run U.atlasJ U.sufficient N i hi
lemma awaken (N i : ℕ) (hi : i<N) : U.main N i=resetI U.motion.k (U.raw N i) := recursed _ U.motion hi
lemma atop (n : ℕ) : U.main n n=upstream G := initiated _ U.motion n
abbrev rank₂ (m : ℕ) := oxidize G (kcap U.ruler (stage A m))
abbrev xDeep (i : ℕ) := U.ruler.Ω (stage A (i+1))
abbrev cDeep (i n : ℕ) := turbulent (historyPatch A i) (U.σ i) (U.σ (i+1)) (U.xDeep i) G n
abbrev rDeep (i : ℕ) := reflector (U.σ i) (U.rank₂ i)
abbrev rise (m N : ℕ) := damp A.S U.a m N
abbrev fall (m N : ℕ) := damp A.S U.b m N
structure Land (ℓ k : ℕ) (x : ℝ) : Prop where
  roof : 1≤ x
  sizes i : ℓ ≤ i → Evaluator A.S i ≤ U.book (age A.S k x i)
  revenue i N N' : ℓ ≤ i → i ≤ N → N≤N' →
    Options (lawn (Cloth G)) (U.σ i) (U.fall i N) (U.book (age A.S k x i)) (onTop G (H.H N i)) (onTop G (H.H N' i))
  tarmac i N : ℓ ≤ i → i<N → Tarmac U.motion.k U.motion.j (U.motion.tree i) (H.H N (i+1)) (H.H N i) (H.towers N i).A0 (U.σ (i+1)) (U.σ i) (U.μ i) (U.rank₂ i) (U.xDeep i) U.E (U.book (age A.S k x i))
  toll i N N' : ℓ ≤ i → i<N→ N≤N' → TollDelta G (U.motion.tree i) (H.H N (i+1)) (H.H N i) (H.H N' (i+1)) (H.H N' i) (U.σ i) (U.μ i) U.E (U.book (age A.S k x i)) (U.fall (i+1) N)
  -- last is LENGTH AFTER ***declaring Height strip parameters***.
  large i : ℓ ≤ i → ∀ n, 1 ≤ n → n ≤ U.E+1 → U.rDeep i*U.cDeep i n ≤ U.rise i (i+1)

variable {U} {ℓ i k n N N' e : ℕ} {x : ℝ} {p q r : ℝ→ℝ} {C : ℝ}
namespace Land
variable (h : U.Land ℓ k x)
set_option linter.unusedSectionVars false 
include h
lemma epoch (hi : ℓ ≤ i) : Season (A.S.block i) (U.σ (i+1)) (U.σ i) (U.μ i) U.E:= (h.tarmac i (i+1) hi (by omega)).warm.era
lemma payload (hi : ℓ ≤ i) : 1≤ U.book (age A.S k x i) := (L_one A.S i).trans (h.sizes _ hi) -- replace L_one
lemma wisdom (i : ℕ) : 1 ≤ age A.S k x i := h.roof.trans (age_ge ..)
lemma conscious (i : ℕ) (hf : Tariff p) : 0 ≤ p (age A.S k x i) := hf.1 _ (zero_le_one.trans (h.wisdom i))
lemma rise_l (hi : i≤N) : U.rise i N ≤1:= damp_lone A.S (U.bah.trans U.has).le hi
lemma fall_l (hi : i≤N) : U.fall i N ≤1:= damp_lone A.S U.bah.le hi
lemma fall_ge : U.fall i N ≤ U.fall (i+1) N:= damp_due A.S U.bah.le
lemma cDeep_nn (he : ℓ ≤ i) (n : ℕ) : 0≤ U.cDeep i n := turbulent_nn (h.epoch he).input.le (Pert.Bulk.merit (U.sufficient.rows (i+1) (i+1) le_rfl))
lemma cDeep_small (he : ℓ ≤ i) (hn : 1 ≤ n) (hf : n ≤ U.E+1) : U.cDeep i n ≤ 1 := (le_mul_of_one_le_left (h.cDeep_nn he n) (h.tarmac i (i+1) he (by omega)).reflectPositive).trans ((h.large _ he n hn hf).trans (rise_l h (by omega)))
end Land
end Shop
end YM.WilsonBulk.Parapet
