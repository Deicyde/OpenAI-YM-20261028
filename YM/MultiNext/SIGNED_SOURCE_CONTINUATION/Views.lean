import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.Next.MULTISOURCE.Journey
import YM.Next.SCHEDULE.Air
import YM.Push.RELAY_DIFFERENCE.Rolling
import YM.Push.RELAY_DIFFERENCE.SingleMajorant

set_option warningAsError false

/-!
# Views of germs under hierarchical spin+translation+anti, for mixed budgets

Reuse already proven chain of actual directional derivative ESTIMATES
through these sends (including two-sided deformation costs). Extend to
BudgetPoint.Regular (smoothness & HasDerivs!) and Legible output Pack
for creating credits without extra order losses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.View
open Function Filter MeasureTheory RG Wilson Lattice Labels Source Bid
open Multi Multi.Pack Push.RelayDifference
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side}

variable (s : Signed) (b : Site n)

def flip : Equiv.Perm (Site n) := Push.RelayDifference.Single.rotor s b

def twist (X : Support n) : Support n := X.image (flip s b)

lemma intersection (X : Support n) (t : ℝ) (U : Config G n) : twist s b (X ∩ flags t (pull s b U))=
    twist s b X ∩ flags t U := by
  conv_rhs => rw [← Work.H03.flags_send s b t U]
  exact Finset.image_inter X _ (flip s b).injective

lemma bills (X : Support n) (m : ℕ) : coverNumber m (twist s b X) ≤ coverNumber m X := Push.RelayDifference.Single.cover_price s b X m

lemma agreement (X : Support n) (U V : Config G n) (h : Agrees (twist s b X) U V) : Agrees X (pull s b U) (pull s b V) := by
  intro p hz hz'
  let M := twist s b X
  have he {x : Site n} (hx : x ∈ X) : affine s b x∈M := Finset.mem_image_of_mem _ hx
  let d := (posDir p.2).rotate s
  let x := affine s b p.1
  change d.read U x = d.read V x
  have hh := he hz
  have hw : x + d.vec ∈ M := by
    simp only [x,d, Lattice.Step.vec_rotate, Lattice.Step.vec_pos]
    rw [show _ + s.act (step p.2) = affine s b (p.1 + step p.2) by rw [affine,affine,Signed.act_add]; abel]
    exact he hz'
  generalize d = D at *
  rcases D with ⟨i,t|t⟩
  · exact h (x,i) hh hw
  change (U (x-step i,i))⁻¹ = (V (x-step i,i))⁻¹
  rw [h]; exacts [by simpa [Lattice.Step.vec,sub_eq_add_neg] using hw,by simpa [x] using hh]

lemma same (F : Config G n → ℂ) (h : GaugeInvariant F) (χ : Bool) : GaugeInvariant (oriented F χ s b) := by
  intro t U
  apply congr_arg (hand χ)
  rw [show pull s b (Lattice.gauge t U)=Lattice.gauge (t ∘ affine s b) (pull s b U) by
    funext e
    unfold pull Lattice.gauge
    have he (x i) : affine s b (x+step i) = affine s b x + ((posDir i).rotate s).vec := by
      rw [Lattice.Step.vec_rotate]; simp [affine]; abel
    simp only [Function.comp_apply,he]; exact Lattice.Step.gauge_read ((posDir _).rotate s) t U _]
  exact h ..
lemma measurable (F : Config G n → ℂ) (h : Measurable F) (χ : Bool) : Measurable (oriented F χ s b) := by
  cases χ
  · exact h.comp (continuous_pull s b).measurable
  exact (continuous_star (R:=ℂ)).measurable.comp (h.comp (continuous_pull s b).measurable)

lemma masks (F : Config G n → ℂ) (t : ℝ) (X : Support n) (χ : Bool) : oriented (masked t X F) χ s b =
    masked t (twist s b X) (oriented F χ s b) := by
  funext U
  have he : Healthy t (twist s b X) U ↔ Healthy t X (pull s b U) := TwoSided.healthy_at ..
  by_cases h : Healthy t X (pull s b U)
  · unfold Push.RelayDifference.oriented; rw [masked_eq _ _ _ _ (he.mpr h), masked_eq _ _ _ _ h]
  unfold Push.RelayDifference.oriented; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt he.mp h)]; cases χ <;> simp [hand]

lemma projected {P : BudgetPoint} (χ) {F : Config G n → ℂ} {X : Support n} (h : P.Regular X F)
    (U : Config G n) (hu : Healthy P.threshold X (pull s b U)) : TwoSided.Based U (oriented F χ s b) P.order := by
  have he : TwoSided.Based (pull s b U) F P.order := h.smooth _ hu
  let g (v : Directions G n) := pull s b (increment U v)
  have ht : ContDiffAt ℝ (P.order:WithTop ℕ∞) (F ∘ g) 0 := by
    have hx : Continuous g := (continuous_pull s b).comp (continuous_pi fun i => (G.lieExp_cont.comp (continuous_apply i)).mul continuous_const)
    apply he.from (F:=g) (congrArg (pull s b) (show increment U 0=U by funext i; simp [increment])) hx.continuousAt
    intro i
    unfold g pull Lattice.Step.read increment
    split
    · simp only [G.mat_inv,G.mat_mul]
      refine (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ ?_
      exact (((G.exp_jet.comp (contDiff_apply ℝ G.Color _)).mul contDiff_const).contDiffAt.of_le le_top)
    simp only [G.mat_mul]
    exact (((G.exp_jet.comp (contDiff_apply ℝ G.Color _)).mul contDiff_const).contDiffAt.of_le le_top)
  cases χ
  · exact ht
  exact ((show ℂ ≃L[ℝ] ℂ from starL ℝ).contDiff.contDiffAt.comp _ ht)

lemma reg {P : BudgetPoint} (χ) {F : Config G n → ℂ} {X : Support n} (h : P.Regular X F) :
    P.Regular (twist s b X) (oriented F χ s b) := by
  refine ⟨fun U V H => congrArg (hand χ) (h.sites _ _ (agreement s b X U V H)), measurable s b F h.borel χ, same s b F h.symmetry χ,
    fun U he => projected s b χ h U ((TwoSided.healthy_at ..).1 he), fun U he A l hl => ?_⟩
  let g := oriented F χ s b
  have hf : TwoSided.Based U g P.order := projected s b χ h U ((TwoSided.healthy_at ..).1 he)
  have hh : TwoSided.Based U (leftDerivs g l) 1 := by
    rw [←TwoSided.lefts]
    exact (hf.less (by simp; omega : 1+(l.map TwoSided.l).length ≤ _)).series _
  have ht := hh.approach (TwoSided.l A)
  simp_rw [TwoSided.vary_l] at ht
  change HasDerivAt _ (deriv (fun t : ℝ => leftDerivs g l (increment U (t • A))) 0) 0
  exact ht.differentiableAt.hasDerivAt

def pack (q : Pack n) : Pack n := ⟨⟨twist s b q.zone, twist s b q.flagsAt⟩,q.property.1.image _, Finset.image_subset_image q.property.2⟩

def vehicle : Equiv.Perm (Pack n) := Equiv.ofBijective (pack s b) (Finite.injective_iff_bijective.mp (by
  intro i j he
  have hx := congrArg Pack.zone he; have hy := congrArg Pack.flagsAt he
  apply Subtype.ext; exact Prod.ext (Finset.image_injective (flip s b).injective hx) (Finset.image_injective (flip s b).injective hy)))

lemma notice {P : BudgetPoint} {F : Config G n → ℂ} {q : Pack n} (h : Legible P q F) (χ) : Legible P (pack s b q) (oriented F χ s b) := by
  refine ⟨measurable s b F h.borel χ, same s b F h.symmetry χ, fun U V he hi => congrArg (hand χ)
    (h.reads _ _ (agreement s b q.zone U V he) ?_), fun U hu => ?_⟩
  · change twist s b q.zone ∩ _=twist s b q.zone ∩ _ at hi
    rw [← intersection,← intersection] at hi; exact Finset.image_injective (flip s b).injective hi
  have hp : F (pull s b U) ≠ 0 := by
    intro hh; exact hu (by unfold Push.RelayDifference.oriented; rw [hh]; cases χ <;> simp [hand])
  change twist s b _ ∩ _=_
  rw [← intersection, h.inventory _ hp]; rfl
end YM.MultiNext.SignedSource.View
