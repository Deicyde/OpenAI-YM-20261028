import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.RowStack
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sounds


set_option warningAsError false

/-! D complete selected move-matrix dues at every record. Branch k use
and fderiv priced on true ContDiff neighborhood on selected rows;
no transmittance across the measure indicator or allocation. Or order 0
with no spectral input. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG RG.Patch Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Push.SectorMeasure YM.Push YM.Next YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet
open Next.SectorChange.Rows Next.SectorChange.Wisps Press
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}

lemma threshold {σ : ℝ} (hp : 0 < σ) (P : Patch) (G : Gauge) : ∀ᶠ x : ℝ in atTop,
    span P x ≤ radiusB x/50 ∧ allot P+1 ≤ 9*radiusB x ∧
    2*(allot P+1) < 100*(1+radiusB x) ∧ permit P * temp x ≤ σ := by
  filter_upwards [small_span P, Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1),
    Work.E01.fiery_le G (1:Side) (permit P), (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hp)] with x hx hp hy hu
  exact ⟨hx,by omega,by omega,by simpa [fiery,betaF] using hy.trans hu⟩

lemma block_houses (S : StepData c f) (k : S.Choices) (s : Signed) (i : Bond c) (t : Directions G f)
    (h : S.patch.Branches S.kernel G) : Housed (E:=G.El) (s.act i.1) (predReach S.patch+1) (fun V => blockJet V k s i t) := by
  intro U V he
  have ht : predictorTurn V k s i = predictorTurn U k s i := by
    have hx (a : Directions G f) : predictGroup V k s i a = predictGroup U k s i a := by
      unfold predictGroup; apply prediction_near_eq h
      apply pulled_near; exact replica_near_agree S a (fun i hi => (he i hi).symm)
    funext a; unfold predictorTurn; rw [hx a,hx 0]
  unfold blockJet; simp_rw [ht]

lemma block_needs (S : StepData c f) (k : S.Choices) (s : Signed) (i : Bond c) (j : Atom G f) (V : Config G c)
    (hb : S.patch.Branches S.kernel G) (h : ¬separation (s.act i.1) (S.ratio.parent j.1.1) ≤ predReach S.patch+1) :
    blockJet V k s i (atom j)=0 := by
  refine (blockJet_dep V k s i _ 0 hb ?_).trans (map_zero _)
  intro e he
  have hu : e ≠ j.1 := fun hv => h (hv ▸ he); unfold atom; rw [on_axis,Pi.single_eq_of_ne hu]; rfl

lemma noise_quote (G : Gauge) (P : Patch) (K : KernelChoices) (h : P.Branches K G) (k : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    ∃ C r : ℝ, 0≤C ∧ 0<r ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    100*(1+radiusB x) ≤ c.val →
    ∀ (V : Config G c) (A : Stores S) (F : Forest S.ratio) (s : Signed) (t : S.Choices) (i : Bond c),
      A.flags=RG.flags (temp x) V → curb (shots S x) A F x s (.inr i) → ∀ B : Directions G c, ‖B‖ ≤ r →
      ContDiffAt ℝ ω (fun y => G.mat (workQ V s t i y)) (B,0) ∧
      ∀ j : Atom G f, Due d (s.act i.1) (S.ratio.parent j.1.1) k C (fun b => noiseKick (increment V b) t (atom j) s i) B := by
  obtain ⟨C,r,δ,hC,hr,hδ,hE⟩ := sounds P K h (k+1)
  let Z := Real.exp ((1+2*k)*d*↑(predReach P+1))*C
  have hz : 0≤Z := mul_nonneg (Real.exp_pos _).le hC
  refine ⟨‖-Real.sqrt K.penalty‖*Z,r,mul_nonneg (norm_nonneg _) hz,hr,?_⟩
  filter_upwards [threshold hδ P G] with x hx
  obtain ⟨hs,hp,hq,ha⟩ := hx
  intro c f S hP hK hc V A F s t i hA hi B hB
  obtain ⟨hh,-,hm⟩ := hE _ hP hK _ _ _ _ s t i hA hs hp (by omega) ha hi (B,0) (by simpa)
  have hb : S.patch.Branches S.kernel G := by rw [hP,hK]; exact h
  refine ⟨hh,fun j => ?_⟩
  let v (U : Config G c) := blockJet U t s i (atom j)
  have he : Due d (s.act i.1) (S.ratio.parent j.1.1) k Z (fun b => v (increment V b)) B := by
    have hf : AtCap k C (fun b => v (increment V b)) B := AtCap.upright hm hC (atom_small j)
    have he := charge v B (block_houses S t s i (atom j) hb) (y:=S.ratio.parent j.1.1) (fun h U => block_needs S t s i j U hb h) hf hC hd
    rw [hP] at he; exact he
  unfold noiseKick; rw [hK]; simpa only [neg_smul] using Due.scale he hz (-Real.sqrt K.penalty)

/-- Precision and covariance in the coarse V chart. Flags, x, and
Tree S held fixed THROUGH the estimates. Only the chart exists here,
not saying that the V fields resulting from these increments pass the
original sector hypotheses. At boundaries these ARE the unmasked extension
jets. -/
def scroll (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c)
    (B : Directions G c) := move T x (increment V B) t (shots S x) A F

def pilot (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c)
    (B : Directions G c) := gram T x (increment V B) t (shots S x) A F

lemma pilot_eq (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (x : ℝ) (V : Config G c)
    (B : Directions G c) : pilot T A F t x V B=(scroll T A F t x V B).transpose*scroll T A F t x V B := rfl

/-- Project color once (counting scalar). -/
def componentG (i : G.ColorIndex) : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) i
lemma tint_price (i : G.ColorIndex) : ‖componentG (G:=G) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v
  change |v i| ≤ 1*‖v‖
  rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ v i]
  simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) v

def Entry (x : ℝ) (C r : ℝ) (P : Patch) (G : Gauge) (p : Teller G) (k : ℕ) (δ : ℝ) :=
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
    100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
      A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
        ∀ (i : Receipt G S) (j : In (G:=G) x A F), Due δ (down S i) (front A F j) k C (fun b => scroll T A F t x V b i j) B

/-- The required dues before differentiating inverses. For each stated
post-L σ quote get a REAL neighborhood; or simply ask at B=0. -/
theorem entries (P : Patch) (G : Gauge) (p : Teller G) (k : ℕ) (d : ℝ) (hd : 0≤d)
    (he : (1+2*k)*d ≤ p.top.width/2) (hb : P.Branches p.bind G) :
    ∃ C r : ℝ, 0≤C ∧ 0<r ∧ ∀ᶠ x : ℝ in atTop, Entry x C r P G p k d := by
  obtain ⟨C,r,hc,hr,hE⟩ := noise_quote G P p.bind hb k d hd
  let z := faceMoney p d k
  let n := ‖slip‖*max z C
  have hz := faceMoney_nn p d k
  have hm : 0 ≤ max z C := hc.trans (le_max_right ..)
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) hm
  refine ⟨n,min r (1/2),hn,lt_min hr (by norm_num),?_⟩
  filter_upwards [hE] with x hx
  intro c f S T hS hT hg V t A F hA B hP i j
  let W := shots S x; let y := front A F j; let a : Atom G f := (j.1.val.val,j.2)
  by_cases hu : keep x W A F i.1
  · let v b := bump T x (increment V b) t (fresh x W A F (axisPrice j)) i.1
    have ht : Due d (down S i) y k (max z C) v B := by
      have hf := fresh_atom W A F j; unfold v; rw [hf]
      rcases i with ⟨⟨s,b|b⟩, i⟩
      · exact Due.weaken (face_payment S s T hT x V b a B k hd he (lt_of_le_of_lt (hP.trans (min_le_right ..)) (by norm_num))) (le_max_left ..)
      exact Due.weaken ((hx S hS hT.knobs hg V A F s t b hA hu B (hP.trans (min_le_left ..))).2 a) (le_max_right ..)
    have H := ht.scale hm slip
    let L := componentG (G:=G) i.2
    refine Due.congr_germ ((H.post L).weaken (mul_le_of_le_one_left hn (tint_price _))) (Eventually.of_forall fun b => ?_)
    change ((if keep x W A F i.1 then slip • v b else (0:G.Color)) i.2) = (slip • v b) i.2
    rw [if_pos hu]
  refine Due.congr_germ (Due.funded_zero hn) (Eventually.of_forall fun b => ?_)
  change ((if keep x W A F i.1 then slip • bump T x (increment V b) t (fresh x W A F (axisPrice j)) i.1
    else (0:G.Color)) i.2) = 0
  rw [if_neg hu]; rfl
end YM.AnalyticBridge.Covariance
