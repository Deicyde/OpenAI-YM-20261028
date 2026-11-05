import YM.Further.DENSE_MIXED_KERNELS.Ripple
import YM.Further.DENSE_MIXED_KERNELS.Surface


/-!
# Differentiating held tracks

Use genuine local Haar ChartRatio (calibrated color norm) all along; the
smooth extension demand on S is localized to the evaluated U, even on a
boundary of flags. Gives the held-link velocity estimates from primitive
moving-mean/orientation hypotheses. A change in Z receives a polynomial
in paid normal units, NOT `g⁻¹` with no offsetting fine gain at every
such use. Uniform in all held links, includes repeats in later usage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Lattice RG Wilson Precision Module
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {k : ℕ} {U : Config G n} {P : Directions G n→Prop}
    {A : ChartRatio G} (H : Port A)
section attain
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_pays (k : ℕ) (h : E→F) (s : Set E) (hs : IsCompact s) (hf : ∀ x∈s,ContDiffAt ℝ (↑k) h x) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x∈s, ∀ j ≤ k, ‖iteratedFDeriv ℝ j h x‖ ≤ C := by
  choose f H using (fun i : Fin (k+1) => hs.exists_bound_of_continuousOn <|
    show ContinuousOn (iteratedFDeriv ℝ i.val h) s from fun x hx => ((hf x hx).continuousAt_iteratedFDeriv
      (by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt))).continuousWithinAt)
  let c : ℝ := ∑ i, max (0:ℝ) (f i)
  have he i : 0≤max 0 (f i) := le_max_left ..
  refine ⟨1+c,le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => he i)), fun x hx i hi => ?_⟩
  let j : Fin (k+1) := ⟨i,Nat.lt_succ_iff.mpr hi⟩
  exact (H j x hx).trans ((le_max_right ..).trans ((Finset.single_le_sum (a:=j) (fun i _ => he i)
    (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one)))

namespace Port
private abbrev logJ (A : ChartRatio G) := fun y => Real.log (A.scale*A.J y)
lemma price_chart (k : ℕ) : ∃ c : ℝ, 1 ≤ c ∧ (∀ i, i∈H.enters →
    ContDiffAt ℝ k G.plog (G.mat i) ∧ ∀ j ≤ k, ‖iteratedFDeriv ℝ j G.plog (G.mat i)‖ ≤ c) ∧
    (∀ x, x ∈ H.accepts → ContDiffAt ℝ k (logJ A) x ∧ ∀ j ≤ k, ‖iteratedFDeriv ℝ j (logJ A) x‖ ≤ c) := by
  let B := Metric.closedBall (0:G.Color) H.radius
  have ht : H.accepts ⊆ B := Metric.ball_subset_closedBall
  have hc : IsCompact B := ProperSpace.isCompact_closedBall ..
  let R := (G.mat ∘ G.lieExp) '' B
  have hL : IsCompact R := hc.image (G.continuous_mat.comp G.lieExp_cont)
  have H₁ x (hx : x∈R) : ContDiffAt ℝ k G.plog x := by
    obtain ⟨y,hy,rfl⟩ := hx; exact (H.reads y (by simpa [B] using! hy)).of_le le_top
  have H₂ x (hx : x ∈ B) : ContDiffAt ℝ k (logJ A) x := by
    have hp := Metric.closedBall_subset_ball H.inside hx
    exact ((contDiffAt_const (c:=A.scale)).mul ((H.legal.germ x hp).of_le (show (k:WithTop ℕ∞)≤ω from le_top))).log
      (mul_pos H.legal.scale (H.legal.pos x hp)).ne'
  obtain ⟨p,hp,hp'⟩ := compact_pays k _ _ hL H₁
  obtain ⟨q,hq,hq'⟩ := compact_pays k _ _ hc H₂
  refine ⟨p+q,by linarith, fun i hi => ?_, fun x hx => ⟨H₂ _ (ht hx),fun j hj => (hq' x (ht hx) j hj).trans (by linarith)⟩⟩
  obtain ⟨x,hx,rfl⟩ := hi
  have hr : G.mat (G.lieExp x)∈ R := mem_image_of_mem _ (ht hx)
  exact ⟨H₁ _ hr,fun j hj => (hp' _ hr j hj).trans (by linarith)⟩

def coins (k : ℕ) := (H.price_chart k).choose
lemma cash (k : ℕ) : 1 ≤ H.coins k := (H.price_chart k).choose_spec.1

end Port
end attain

namespace Surface
open Port
variable {H}
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] {W : Config G n → Surface H ι κ Ω}
  {T g : ℝ}
local notation "X" => H.front ι (H.Room κ)
local notation "Y" => H.back ι (H.Room κ)

/-- Physical-size estimate on mean AND route/frame/orientation data fixed
on this local sector formula; only requested for the coordinates that are
held as U. Config U below is the output configuration. -/
structure Shifts (W : Config G n → Surface H ι κ Ω) (U : Config G n) (P : Directions G n→Prop) (k : ℕ) (g T : ℝ) : Prop where
  prop Φ : Ripple (fun x => (W x).mean Φ) U P k g T
  orient Φ (i : ι) : Ripple (fun x => G.mat ((W x).orient Φ i)) U P k g T

variable (hg : 0<g) (hh : g≤1) (ht : 0≤ T) (hs : Shifts W U P k g T) (p : Ω × H.back ι (H.Room κ))

private lemma mat_eta (f : Config G n → G.El) (j : G.El) :
    (fun x => G.mat (j*(f x)⁻¹)) = fun x => G.mat j * star (G.mat (f x)) := by simp_rw [G.mat_mul,G.mat_inv]
private lemma mat_star_linear {M : ℝ} {f : Config G n → G.El} (j : G.El)
    (h : Ripple (fun x=> G.mat (f x)) U P k M T) : Ripple (fun x => G.mat (j*(f x)⁻¹)) U P k M T := by
  let F := G.Mat
  let L : F→L[ℝ]F := (ContinuousLinearMap.mul ℝ F (G.mat j)) ∘L (starL' ℝ (A:=G.Mat) : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
  rw [mat_eta]; exact h.onLeft L fun i => by
    change ‖G.mat j * star i‖ ≤ ‖i‖; rw [Gauge.mul_frob_eq ..]; swap; exact G.mat_star_mul _
    exact (Matrix.frobenius_norm_conjTranspose _).le

-- actual open, including any logged displacement on this port
lemma Shifts.perching (hs : Shifts W U P k g T) {p : Ω × Y} (he : p∈(W U).Perch) :
    ∀ᶠ v in 𝓝 0,p∈(W (increment U v)).Perch := by
  let f i x := p.2.1 i * ((W x).orient p.1 i)⁻¹
  have hp (i : ι) : Rests (fun x => G.mat (f i x)) k U := (mat_star_linear _ (hs.orient p.1 i)).smooth
  have he' i : ContinuousAt (fun w => f i (increment U w)) 0 := by
    have hI : Topology.IsInducing G.mat := (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).isInducing
    exact hI.continuousAt_iff.mpr (ContDiffAt.continuousAt (hp i))
  have h'i (i : ι) : ∀ᶠ v in 𝓝 0, f i (increment U v)∈H.enters :=
    (he' i) (H.around.mem_nhds (show f i (increment U 0) ∈ H.enters from by rw [increment_zero]; exact he i (Set.mem_univ _)))
  filter_upwards [eventually_all.mpr h'i] with v hv using fun i _ => hv i

abbrev arc (S : Surface H ι κ Ω) (p : Ω × H.back ι (H.Room κ)) := H.hear (S.orient p.1) p.2.1

-- chart scope constant, independent of support.
def curve (H : Port A) (k : ℕ) (T : ℝ) := (H.coins k) * (2^k*T)

include hg hh ht hs in
lemma motion (he : p∈ (W U).Perch) (i : ι) :
    Ripple (fun x => (W x).arc p i) U P k g (curve H k T) := by
  let f x := p.2.1 i*((W x).orient p.1 i)⁻¹
  have h₁ := hs.orient p.1 i
  have hp : Ripple (G.mat∘f) U P k g T := mat_star_linear (p.2.1 i) h₁
  have hr : f U∈H.enters := he i (Set.mem_univ _)
  obtain ⟨h,h'⟩ := (H.price_chart k).choose_spec.2.1 (f U) hr
  have ht' := Ripple.comp (g:=G.plog) hp hh ht (zero_le_one.trans (H.cash k)) h (fun i _ hf => h' i hf) hg.le
  refine (ht'.save (by positivity) (H.cash k) hg.le).equiv ?_
  filter_upwards [hs.perching he] with v hv using
    (show H.undo (f (increment U v))=G.plog (G.mat (f (increment U v))) from if_pos (hv i (Set.mem_univ _)))

include hg hh ht hs in
lemma drift (he : p∈(W U).Perch) : Pulse (fun x => ((W x).mapUp g p).2) U P k (2*curve H k T) := by
  let a := curve H k T
  have hE := H.cash k
  have hA : 0 ≤ a := mul_nonneg (zero_le_one.trans hE) (by positivity)
  have hR : T≤a := (le_mul_of_one_le_left ht (one_le_pow₀ (n:=k) (by norm_num : (1:ℝ) ≤ 2))).trans
    (le_mul_of_one_le_left (by positivity) hE)
  have hv : Ripple (fun x => (W x).arc p) U P k g a := Ripple.pi hA hg.le (motion hg hh ht hs p he)
  let L : H.Room ι →L[ℝ] H.Room ι := g⁻¹ • ContinuousLinearMap.id ℝ _
  let z (x : Config G n) := (W x).arc p - (W x).mean p.1
  have hz : Ripple z U P k (2*g) a := by
    rw [two_mul,show z=(fun x => (W x).arc p + (-((W x).mean p.1))) by funext x; exact sub_eq_add_neg ..]
    exact hv.plus (((hs.prop p.1).mono ht hR hg.le le_rfl).neg)
  have HL : ∀ w, ‖L w‖ ≤ g⁻¹*‖w‖ := fun w => by
    unfold L; simp only [_root_.smul_apply,ContinuousLinearMap.id_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le,le_refl]
  have HE : Ripple (fun x => L (z x)) U P k (2*1) a := by
    rw [show (2:ℝ)*1=g⁻¹*(2*g) by field_simp]
    exact hz.linear L HL (inv_pos.mpr hg).le
  exact Ripple.unit ((HE.save hA (by norm_num) zero_le_one).pair (Ripple.fixed 1 (2*a) zero_le_one (by positivity) p.2.2))
end Surface
end YM.Further.DenseMixedKernels
