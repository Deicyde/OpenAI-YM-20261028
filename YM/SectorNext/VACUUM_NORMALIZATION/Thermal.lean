import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
import YM.SectorNext.VACUUM_NORMALIZATION.Link
import YM.SectorNext.VACUUM_NORMALIZATION.Mast
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped



/-!
# Tree-volume denominator and terminal numerator/denominator comparison

Both genuine Wilson Haar and on any Lawful supplied representation of
that form (explicit h.pos required). Even torus, tree-gauge cost paid
only on free links.  reads **4** missing edges, not an
additional per-volume log. No interpreter change in weights/power.
Includes nonabelian case with dim-cost in real Color. Does not require
ranks etc in comparison certificate, only cutoff estimates. Need true
projective/corrected arrays etc for phase program.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Precision Gauge MeasureTheory Push.SectorMeasure.Presented Masts
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
variable {G : Gauge} {n : Side}
local notation "Δ" => Module.finrank ℝ G.Color

def spare (n : Side) := 3*Fintype.card (Site n)+1
def rich (n : Side) := 3*Fintype.card (Site n)-3
lemma spare_four (n : Side) : spare n=rich n+4 := by unfold spare rich; have h := Fintype.card_pos (α:=Site n); omega

private lemma main_count (H : 1 < n.val) : Fintype.card (main n H).Free=spare n := by
  have he := FlatTree.count_clear (main n H)
  rw [Fintype.card_prod,site_card (1:Side)] at he; change Fintype.card (main n H).Free+_=_*4+1 at he
  unfold spare; omega

/-- Generic package at the denominator; the rooted word weights should
supply comparable inequalities on these same links. Assumes pointwise on
all links; can also relax to ae along reserved tree slice if verified at
THAT measure. -/
lemma tree_ball (H : 1<n.val) {k : Config G n → ℝ} (h : GaugeInvariant k) (hz : ∀ V,0≤ k V)
    (hi : Envelope k) {s : ℝ} (hs : 0≤s) {q z : ℝ} (hq : 0≤q) (hE : q ≤ G.probHaar.real (G.shell (s/4)))
    (hp : 0≤z) (hx : ∀ U∈calm G n s, z ≤ k U) : z*q^spare n ≤ ∫ U,k U ∂prior G n := by
  let A := main n H; let B := Set.pi (Set.univ : Set A.Free) fun _ => G.shell (s/4)
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _=>G.shell_meas _
  have hm : z*(A.order G).real B ≤ _ := calc
    _ = ∫ p : A.Slice G,B.indicator (fun _=>z) p ∂A.order G := by rw [integral_indicator hB,setIntegral_const,smul_eq_mul,mul_comm]
    _ ≤ ∫ p : A.Slice G,k (A.drape p) ∂A.order G := by
      apply integral_mono ((integrable_const _).indicator hB) ((Push.SectorMeasure.Env.along hi A.continuous_drape.measurable).integrable _)
      intro x; by_cases hx' : x∈B
      · rw [indicator_of_mem hx']; apply hx; intro i _; by_cases he : i∈A.trunks
        · rw [show A.drape _ i=1 from A.on_tree _ ⟨i,he⟩]; change G.chord 1 ≤ _; rw [G.chord_one]; linarith
        rw [show A.drape _ i = _ from A.off_tree x ⟨i,he⟩]; exact hx' _ (mem_univ _)
      rw [indicator_of_notMem hx']; exact hz _
    _ = ∫ U,k U ∂prior G n := (A.pack k (hi.integrable _) (fun i _=>h i)).symm
  apply le_trans _ hm
  apply mul_le_mul_of_nonneg_left _ hp; unfold B Tree.Forest.order Measure.real; rw [Measure.pi_pi,Finset.prod_const,Finset.card_univ, ENNReal.toReal_pow,main_count H]; exact pow_le_pow_left₀ hq hE _



lemma GI_stripped (R : Rep G n) {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) : GaugeInvariant (stripped R) := by
  intro t V; unfold stripped; rw [lawful_gi h]

/-- A shrunk ball event, per native free link, color dim penalty. -/
theorem housing : ∃ (s q : ℝ), 0<s ∧ s≤1 ∧ 0<q ∧ q≤1 ∧ ∀ n : Side, ∀ _H : 1<n.val,
    ∀ R : Rep G n,∀ {σ C Λ δ w : ℝ}, R.Lawful σ C Λ δ w → (∀ U,0≤R.eval U) →
    ∀ t : ℝ,1 ≤ t → R.beta=t^2 → t⁻¹ ≤ R.p.threshold →
      Real.exp (-sites n * (R.exCost C Λ δ+baseBudget R.clip C s)) * ((q*(t⁻¹)^Δ)^spare n) ≤ strippedZ R := by
  obtain ⟨r,c,hr,hc,h⟩ := shell_lower (Next.Foundations.chart G) (Next.Foundations.chart_ok G)
  let s := min 1 r
  let q := min 1 (c*(s/4)^Δ)
  have he : 0<s := lt_min (by norm_num) hr
  have hh : s≤1 := min_le_left ..
  have hq : 0<q := lt_min (by norm_num) (by positivity)
  refine ⟨s,q,he,hh,hq,min_le_left ..,fun n H R {σ C Λ δ w} hR hp t ht hz hT=> ?_⟩
  have hx : 0<t := zero_lt_one.trans_le ht
  have hm : 0<s/t := by positivity
  have hd : s/t ≤ R.p.threshold := ((div_le_div_of_nonneg_right hh hx.le).trans_eq (one_div _)).trans hT
  apply tree_ball H (GI_stripped R hR) (fun i=>mul_nonneg (Real.exp_pos _).le (hp i)) ((Envelope.const _).mul (R.envelope hR)) (s:=s/t)
    hm.le (q:=q*(t⁻¹)^Δ) (by positivity) ?_ (Real.exp_pos _).le ?_
  · apply le_trans _ (h (s/t/4) (by positivity) (by calc
      _ ≤ s := by linarith [div_le_self he.le ht]
      _ ≤ _ := min_le_right ..))
    rw [show s/t/4 = s/4*t⁻¹ by ring,mul_pow,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (show (min 1 (c*(s/4)^Δ):ℝ) ≤ c*(s/4)^Δ from min_le_right ..) (by positivity : (0:ℝ)≤(t⁻¹ ^ Δ:ℝ))
  intro U hu
  unfold stripped Rep.eval; rw [Activities.gas_one _ _ (voids hu hd),mul_one,←Real.exp_add]; apply Real.exp_le_exp.mpr
  have hw := R.exponent_lo hR (by rw [hz]; positivity) (s/t) hm hd hu
  have hl : R.beta*baseBudget R.clip C (s/t) = baseBudget R.clip C s := by
    unfold baseBudget; rw [hz]; field_simp
  rw [hl] at hw; unfold sites; linarith only [hw]









def speed (R : Clip) := R.linear









end YM.SectorNext.Vacuum
