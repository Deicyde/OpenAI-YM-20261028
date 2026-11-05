import YM.MultiNext.VACUUM_STABILITY.Words
import YM.Next.MULTISOURCE.Germs
import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.Work.F07.MatrixRoot



set_option warningAsError false

/-!
# Ordered directional derivatives of log words

We really charge reanchoring of the directional derivative envelopes. At derivative order `l`
we pay only on `l` shifts through the stencil, even with an unbounded number of letters. At a
healthy boundary point use the actual `Regular` extension, not the masked product or an open
healthy hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Jets
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Corona Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {n : Side} {G : Gauge}



section germ
variable {F F' : Config G n → ℂ} {k : ℕ} {U : Config G n}

lemma crest_product (h : Crest k F U) (h' : Crest k F' U) : Crest k (F*F') U :=
  into k (F*F') (h.germ.mul h'.germ)

lemma shorten (h : Crest (k+1) F U) : Crest k F U := by
  refine into k F (h.germ.of_le ?_)
  simp

lemma multiplication (A : Directions G n) (h : Crest (k+1) F U) (h' : Crest (k+1) F' U) :
    leftDerivs (F*F') [A] U = leftDerivs F [A] U * F' U + F U * leftDerivs F' [A] U := by
  have he := deriv_mul (h.line [] (by simp) A) (h'.line [] (by simp) A)
  simp_rw [leftDerivs] at *
  rw [zero_smul,inc_zero] at he; exact he

lemma agrees (h : F =ᶠ[𝓝 U] F') (A : List (Directions G n)) : leftDerivs F A U = leftDerivs F' A U := by
  induction A generalizing U with
  | nil => exact h.eq_of_nhds
  | cons i l ih =>
    have he := (swing U i).eventually (eventually_eventually_nhds.mpr h)
    exact (show (fun t : ℝ => leftDerivs F l (increment U (t • i))) =ᶠ[𝓝 0]
        (fun t : ℝ => leftDerivs F' l (increment U (t • i))) from he.mono fun t h => ih h).deriv_eq

/-- Multiplicative polynomial Leibniz cost at a point of a genuine extension. -/
structure Band (k : ℕ) (D : Directions G n → Prop) (U : Config G n) (r c : ℝ) (f : Config G n → ℂ) : Prop where
  readable : Crest k f U
  sane : 0 ≤ r
  nonneg : 0 ≤ c
  caps (l : List (Directions G n)) : l.length ≤ k → (∀ A ∈ l, D A) →
      ‖leftDerivs f l U‖ ≤ c*r^l.length

namespace Band
variable {D : Directions G n → Prop} {r r' c c' : ℝ}

lemma crop (h : Band (k+1) D U r c F) : Band k D U r c F :=
  ⟨shorten h.readable,h.sane,h.nonneg,fun l hl => h.caps l (by omega)⟩

lemma within (h : Band (k+1) D U r c F) (A : Directions G n) (hA : D A) :
    Band k D U r (c*r) (leftDerivs F [A]) := by
  refine ⟨h.readable.falls _,h.sane,mul_nonneg h.nonneg h.sane,fun l hl ht => ?_⟩
  rw [← Work.G07.left_append]
  apply (h.caps (l++[A]) (by simpa) (fun i hi => by
    simp only [List.mem_append,List.mem_singleton] at hi; obtain hh|rfl:=hi
    · exact ht _ hh
    exact hA)).trans_eq
  simp only [List.length_append,List.length_singleton,pow_succ]; ring

lemma start (h : Band k D U r c F) : ‖F U‖ ≤ c := by
  simpa only [leftDerivs,List.length_nil,pow_zero,mul_one] using
    h.caps [] (by simp) (by simp)

lemma scale (h : Band k D U r c F) (z : ℂ) : Band k D U r (‖z‖*c) (z • F) := by
  have he := (ContDiffAt.const_smul z h.readable.germ)
  refine ⟨into _ _ he,h.sane,mul_nonneg (norm_nonneg _) h.nonneg,fun l hl ht => ?_⟩
  rw [scaled_left,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.caps l hl ht) (norm_nonneg _)

lemma multiply (h : Band k D U r c F) (h' : Band k D U r' c' F') : Band k D U (r+r') (c*c') (F*F') := by
  induction k generalizing F F' c c' with
  | zero =>
    refine ⟨crest_product h.readable h'.readable,add_nonneg h.sane h'.sane,mul_nonneg h.nonneg h'.nonneg,
      fun l hl _ => ?_⟩
    simp only [Nat.le_zero,List.length_eq_zero_iff] at hl; subst l
    simpa [leftDerivs,norm_mul] using mul_le_mul h.start h'.start (norm_nonneg _) h.nonneg
  | succ k ih =>
    refine ⟨crest_product h.readable h'.readable,add_nonneg h.sane h'.sane,mul_nonneg h.nonneg h'.nonneg,?_⟩
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _ _; simpa [leftDerivs,norm_mul] using mul_le_mul h.start h'.start (norm_nonneg _) h.nonneg
    | append_singleton l A _ =>
      intro hl hv
      have he := h.readable; have he' := h'.readable
      have hA : D A := hv _ (by simp)
      simp only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right] at hl
      have H (i) (hi : i ∈ l) : D i := hv _ (by simp [hi])
      have hX := ih (h.within _ hA) h'.crop
      have hY := ih h.crop (h'.within _ hA)
      have hF : leftDerivs (F*F') [A] =ᶠ[𝓝 U] (leftDerivs F [A]*F' + F*leftDerivs F' [A]) := by
        filter_upwards [he.near,he'.near] with V he he'; exact multiplication A he he'
      rw [Work.G07.left_append, agrees hF, Crest.sum_at l hl U hX.readable hY.readable]
      apply ((norm_add_le ..).trans (add_le_add (hX.caps _ hl H) (hY.caps _ hl H))).trans_eq
      simp only [List.length_append,List.length_singleton,pow_succ]; ring
end Band
end germ

variable {P : BudgetPoint} {o o' : Site n}

-- uniform translation on the true stencil with a charge per derivative
lemma translate {d : ℝ} (hh : (separation o' o:ℝ) ≤ d) {A : Directions G n} (h : P.dirBound o A) :
    P.dirBound o' ((((1+d)^P.power)⁻¹:ℝ) • A) := by
  have hd : 0 ≤ d := (Nat.cast_nonneg _).trans hh
  intro i
  let t := (1+d)^P.power; have hp : 0 < t := by unfold t; positivity
  change ‖t⁻¹ • A i‖ ≤ _
  rw [norm_smul_of_nonneg (inv_pos.mpr hp).le,inv_mul_le_iff₀ hp]
  refine (h i).trans ?_
  rw [mul_left_comm, show t=(1+d)^P.power from rfl,←mul_pow]
  have hb := P.threshold_pos
  gcongr
  have he : (separation i.1 o:ℝ) ≤ separation i.1 o' + (separation o' o:ℝ) := by
    exact_mod_cast separation_triangle i.1 o' o
  nlinarith [Nat.cast_nonneg (α:=ℝ) (separation i.1 o')]

lemma crossing {U : Config G n} {X : Support n} {F : Config G n → ℂ} (hx : Healthy P.threshold X U)
    (he : P.Regular X F) {c : ℝ} (h : P.supBounds o' X F c) {d : ℝ} (hh : (separation o' o:ℝ) ≤ d) :
    Band P.order (P.dirBound o) U ((1+d)^P.power) c F := by
  have hd : 0 ≤ d := (Nat.cast_nonneg _).trans hh
  let t := (1+d)^P.power; have hp : 0 < t := by unfold t; positivity
  refine ⟨into _ _ (he.smooth U hx), hp.le, h.1, ?_⟩
  intro v hv ht
  let q := v.map (fun A => t⁻¹ • A)
  have heq : q.length=v.length := List.length_map ..
  have hf : q.map (fun A => t • A) = v := by simp [q,hp.ne',Function.comp_def]
  rw [← hf, Push.RelayDifference.left_dilate, norm_smul_of_nonneg (pow_nonneg hp.le _),mul_comm c]
  simp only [List.length_map,heq]
  exact mul_le_mul_of_nonneg_left (h.2 U hx q (heq.trans_le hv) (fun i hi => by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact translate hh (ht _ hj))) (pow_nonneg hp.le _)

lemma regular_mul {X : Support n} {F H : Config G n → ℂ} (hF : P.Regular X F) (hH : P.Regular X H) :
    P.Regular X (F*H) := by
  have hh (U) (hu : Healthy P.threshold X U) := crest_product (into _ F (hF.smooth U hu)) (into _ H (hH.smooth U hu))
  exact ⟨fun U V h => by simp only [Pi.mul_apply,hF.sites U V h,hH.sites U V h], hF.borel.mul hH.borel,
    fun k V => by simp only [Pi.mul_apply,hF.symmetry k V,hH.symmetry k V],fun U hu => (hh U hu).germ,
    fun U hu i l hl => ((hh U hu).line l hl i).hasDerivAt⟩

lemma regular_unit (P : BudgetPoint) (V : Support n) : P.Regular V (1 : Config G n → ℂ) := by
  refine ⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun _ _ => contDiffAt_const,?_⟩
  intro U _ i l hl
  exact ((into P.order 1 (U:=U) (by exact contDiffAt_const)).line l hl i).hasDerivAt

lemma constant_unit (U : Config G n) (D : Directions G n → Prop) (k : ℕ) : Band k D U 0 1 1 := by
  refine ⟨into _ _ contDiffAt_const,le_rfl,zero_le_one,?_⟩
  intro l _ _; change ‖leftDerivs (fun _ => (1:ℂ)) l U‖ ≤ _; rw [Work.G07.left_const (1:ℂ)]; cases l <;> simp
end YM.Multi.Vacuum.Jets
