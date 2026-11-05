import YM.EveryPhase.IrreducibleHelpers
import YM.EveryPhase.Vacuum
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Weak commutant

For the opposite-spectrum step it suffices to use the time translations;
use their bounded analytic semigroup continuation from the very reflection
space glued to the boundary, paste across the real line, and use Liouville.
No use of a strong commutant property. In particular B need not map the
domain to the domain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set MeasureTheory Measure Spec Boundary Next.BOUNDARY OS
open scoped Topology NNReal InnerProductSpace ComplexOrder Interval

section paste
open Complex Paley
private theorem paste {f : ℂ → ℂ} (h : Continuous f) (hp : DifferentiableOn ℂ f loft)
    (hx : DifferentiableOn ℂ f {x : ℂ | x.im < 0}) : Differentiable ℂ f := by
  apply differentiableOn_univ.mp
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).mp ⟨?_,h.continuousOn⟩
  have he (z w : ℂ) (hh : z.im ≤ w.im) : wedgeIntegral z w f = -wedgeIntegral w z f := by
    have upper (z w : ℂ) (hh : z.im ≤ w.im) (hg : 0 ≤ z.im) :=
      integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w h.continuousOn
        (hp.mono (fun t ht => by
          change 0 < t.im
          have he : t.im ∈ Ioo z.im w.im := by simpa only [mem_preimage,min_eq_left hh,max_eq_right hh] using ht.2
          exact hg.trans_lt he.1))
    have lower (z w : ℂ) (hh : z.im ≤ w.im) (hg : w.im ≤ 0) :=
      integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w h.continuousOn
        (hx.mono (fun t ht => by
          change t.im < 0
          have he : t.im ∈ Ioo z.im w.im := by simpa only [mem_preimage,min_eq_left hh,max_eq_right hh] using ht.2
          exact he.2.trans_le hg))
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    by_cases hZ : 0≤ z.im
    · exact upper z w hh hZ
    by_cases hW : w.im ≤ 0
    · exact lower z w hh hW
    have h₁ := lower z (w.re:ℂ) (by simp; linarith) (by simp)
    have h₂ := upper (z.re:ℂ) w (by simp; linarith) (by simp)
    have hV (x a b : ℝ) : IntervalIntegrable (fun t : ℝ => f (↑x+↑t*I)) volume a b :=
      (h.comp (show Continuous (fun t : ℝ => ↑x+ (↑t:ℂ)*I) from by fun_prop)).intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hV w.re z.im 0) (hV w.re 0 w.im),
      ← intervalIntegral.integral_add_adjacent_intervals (hV z.re z.im 0) (hV z.re 0 w.im), smul_add,smul_add]
    simp only [ofReal_zero,ofReal_re,ofReal_im,zero_mul,add_zero] at h₁ h₂ ⊢
    grind
  intro z w _; rcases le_total z.im w.im with hh|hh
  · exact he z w hh
  rw [he w z hh,neg_neg]

private theorem saturated {F G : ℂ → ℂ} {C D : ℝ} (hF : Air F C) (hG : Air G D)
    (h : ∀ x : ℝ, F (x:ℂ)=G (- (x:ℂ))) : ∀ z∈high, F z=F 0 := by
  classical
  let L : ℂ → ℂ := high.piecewise F (fun z => G (-z))
  let v := {x : ℂ| x.im ≤ 0}
  have he : EqOn L F high := piecewise_eqOn _ _ _
  have hl : EqOn L (fun z => G (-z)) v := by
    intro z hp; by_cases hZ : z.im=0
    · rw [he (show z∈high from hZ.symm.le),show z = (↑z.re:ℂ) from Complex.ext rfl (by simpa)]
      exact h z.re
    unfold L; rw [piecewise_eq_of_notMem _ _ _ (show z ∉ high from fun hh => hZ (le_antisymm hp hh))]
  have hc : Continuous L := by
    have hF' := hF.connects.congr he
    have hG' : ContinuousOn L v := ((hG.connects.comp continuous_neg.continuousOn (fun z hz =>
      show 0≤(-z).im by simpa using (show z.im≤0 from hz))) : ContinuousOn (fun z => G (-z)) v).congr hl
    apply continuousOn_univ.mp
    rw [show (@univ ℂ)=high∪v from by ext z; exact ⟨fun _ => le_total 0 z.im,fun _ => trivial⟩]
    exact hF'.union_of_isClosed hG' highC (isClosed_le continuous_im continuous_const)
  have hx : DifferentiableOn ℂ L loft := hF.straight.congr (he.mono Paley.subset)
  have hu : DifferentiableOn ℂ L {z : ℂ| z.im < 0} :=
    (hG.straight.comp (f:=-id) (differentiable_id.neg.differentiableOn) (fun z hz => show 0<(-z).im by simpa using (show z.im<0 from hz))).congr
      (fun z hz => hl (show z.im≤0 from (show z.im<0 from hz).le))
  have hp := paste hc hx hu
  have hh : Bornology.IsBounded (Set.range L) := (Metric.isBounded_closedBall (x:= (0:ℂ)) (r:=max C D)).subset (by
    rintro _ ⟨z,rfl⟩
    rw [mem_closedBall_zero_iff]; rcases le_total 0 z.im with H|H
    · exact (he H).symm ▸ le_trans (hF.bounded z H) (le_max_left C D)
    rw [hl H]; exact (hG.bounded (-z) (by simpa [high] using H)).trans (le_max_right C D))
  exact fun z hz => (he hz).symm.trans ((hp.apply_eq_apply_of_bounded hh z 0).trans (he (by simp [high])))
end paste

variable {G : Gauge} {C : Family G} {S : Table C.book}

/-- Bounded Hilbert-space operators (complex linear); no hypothesis about B's action
on the domain. We write the actual adjoint on word-domain vectors as a field:
existing `Fields.really` identifies `(J p, bar f)` on that domain as the
restriction of the Hilbert-space adjoint (`LinearPMap` order). -/
def weaklyCentral (X : Wightman S) (B : X.operators.H.Op) :=
    ∀ (p : S.Union) (f : Test4) (u v : X.operators.domain),
    inner ℂ (X.operators.field (X.J p) (Probe.bar f) u).val (B v.val) =
      inner ℂ u.val (B (X.operators.field p f v).val)

variable {W : Surface S} {R : S.Rotation} {s : S.RealSpin} {X : Wightman S}
lemma word_central {B} (h : weaklyCentral X B) (w : Sentence S) :
    let V := X.operators
    ∀ u v : V.domain, inner ℂ (monomial V (Sentence.rev X.J w) u).val (B v.val)=
      inner ℂ u.val (B (monomial V w v).val) := by
  dsimp only
  induction w with
  | nil => intros; rfl
  | cons i b ih =>
    intro u v; rw [show Sentence.rev X.J (i::b)=Sentence.rev X.J b++[Letter.op X.J i] by simp [Sentence.rev],
      append_op, LinearMap.comp_apply, ih]; exact h i.1 i.2 u (monomial _ _ v)

lemma pairing_at {V : Wightman S} {T : Table C.book} {D : Chamber T timeAxis}
    {J : V.operators.H →L[ℂ] D.H} (h : Attachment V D J) (x y : V.operators.H) (t : ℝ) :
    D.flow.J 0 (J x) (J y) (t:ℂ)=inner ℂ x (V.action.orbit.translation (t • basis timeAxis) y) := by
  rw [D.flow.veers,zero_add,← ContinuousLinearMap.comp_apply _ J, ← h.acts.across _]
  exact LinearIsometry.inner_map_map (⟨J.toLinearMap,h.acts.scale⟩ : V.operators.H →ₗᵢ[ℂ] D.H) _ _

variable {f : Extraction.Order} {F : Final C f S} (L : Almanac F)

theorem commutant (i) (B : (L.actors i).operators.H.Op) (h : weaklyCentral (L.actors i) B) :
    B=inner ℂ (L.actors i).operators.vacuum (B (L.actors i).operators.vacuum) •
        (ContinuousLinearMap.id ℂ _) := by
  let X := L.actors i
  let J := L.J i
  let V := X.operators
  let D := L.chambers i
  let Ω := V.vacuum
  have hp : FieldCore (L.contours i).world _ _ X := L.cores i
  have hi : Attachment X D J := L.links i
  have he : ∀ w : Sentence S, inner ℂ (V.vector w) (B Ω)=
      inner ℂ Ω (B (V.vector (Sentence.rev X.J w))) := by
    intro w
    have hJ := Boundary.invol F.room.kernel.laws.toSymmetric F.phase.transport.injection hp.induced
    have h := word_central (X:=X) h (Sentence.rev X.J w)
    dsimp only at h; rw [Sentence.rev_rev X.J hJ w] at h
    have he := h V.omega V.omega
    change inner ℂ (monomial V w V.omega).val _ = inner ℂ _ (B (monomial V _ V.omega).val) at he
    rw [evaluate_word,evaluate_word] at he; exact he
  let a := inner ℂ Ω (B Ω)
  have hh (b : Sentence S) : inner ℂ (V.vector b) (B Ω)=inner ℂ (V.vector b) (a • Ω) := by
    let u := V.vector b
    let v := V.vector (Sentence.rev X.J b)
    let p t := D.flow.J 0 (J u) (J (B Ω)) t
    let q t := D.flow.J 0 (J (B.adjoint Ω)) (J v) t
    have hk (t : ℝ) : p (↑t) = q (-↑t) := by
      let r := t • basis timeAxis
      let g := Mink.Poincare.translation (-r)
      let c := X.spin.po g b
      have ht : X.action.orbit.translation (-r) (X.action.orbit.translation r (B Ω))=B Ω := by
        rw [← ContinuousLinearMap.comp_apply,X.action.orbit.sends,neg_add_cancel,X.action.orbit.origin]; rfl
      have hv : X.spin.po g (Sentence.rev X.J b)=Sentence.rev X.J c := by
        unfold c Spins.po Sentence.rev; rw [List.map_reverse,List.map_map,List.map_map]; congr 2; ext1 z
        exact (Letter.rewrites F.room.kernel.laws.toSymmetric F.phase.transport.injection hp.induced
          X.spin hp.letters ..).symm
      have hO : V.vector c=X.action.orbit.translation (-r) u := (hp.covariant g b).symm
      have hG : V.vector (Sentence.rev X.J c)=X.action.orbit.translation ((-t) • basis timeAxis) v := by
        rw [← hv,neg_smul]; exact (hp.covariant g (Sentence.rev X.J b)).symm
      unfold p q; rw [← Complex.ofReal_neg,pairing_at hi,pairing_at hi,← hG]
      calc
        _ = inner ℂ (X.action.orbit.translation (-r) u) (X.action.orbit.translation (-r)
            (X.action.orbit.translation r (B Ω))) := (X.action.flavor g u _).symm
        _ = _ := by rw [ht,← hO, he,ContinuousLinearMap.adjoint_inner_left]
    have hy := saturated (D.flow.altitude 0 (J u) (J (B Ω))) (D.flow.altitude 0 (J (B.adjoint Ω)) (J v)) hk
    have hs (s : ℝ≥0) : inner ℂ u (B Ω) = inner ℂ u (bHeat J s (B Ω)) := by
      have hx (s : ℝ≥0) : p (Complex.I * ↑(s:ℝ))=inner ℂ u (bHeat J s (B Ω)) := by
        unfold p; rw [direct]; exact (ContinuousLinearMap.adjoint_inner_right J u _).symm
      have h₀ : p 0=inner ℂ u (B Ω) := by
        rw [show (0:ℂ)=(↑(0:ℝ):ℂ) from rfl]; dsimp only [p]; rw [pairing_at hi,zero_smul,X.action.orbit.origin]; rfl
      rw [← hx, ← h₀]; exact (hy _ (show _ from by simp [Paley.high])).symm
    have ht := bHeat_limit hi hp (B Ω)
    rw [all_plant L i] at ht
    exact tendsto_nhds_unique_of_eventuallyEq (f:=fun _ : ℝ≥0 => inner ℂ u (B Ω)) tendsto_const_nhds
      (tendsto_const_nhds.inner ht) (Eventually.of_forall hs)
  have hc : B Ω=a • Ω := by
    apply hp.soil.whole.eq_of_inner_right ℂ; intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add i j hi hj => simp only [map_add, inner_add_left,hi,hj]
    | single i c => simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left]; exact congrArg _ (hh i)
  change B=a • _
  apply Kernel.Gram.by_bud hp.soil; intro b
  apply hp.soil.whole.eq_of_inner_right ℂ; intro p
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add,inner_add_left,hi,hj]
  | single i c =>
    have hz := word_central (X:=X) h b (V.evaluates i) V.omega
    change inner ℂ (monomial V _ _).val (B Ω)=inner ℂ (V.vector i) (B (monomial V b V.omega).val) at hz
    have hk := star_monomial V X.J hp.adj V.omega (V.evaluates i) b
    rw [evaluate_word V b, hc,inner_smul_right] at hz; rw [evaluate_word V b] at hk
    simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left, _root_.smul_apply,inner_smul_right]
    change _ * inner ℂ (V.vector i) (B (V.evaluates b).val)=_ * (_ * inner ℂ (V.evaluates i).val (V.evaluates b).val)
    rw [← hz,show inner ℂ _ Ω=inner ℂ (V.evaluates i).val (V.evaluates b).val from by
      apply (starRingEnd ℂ).injective; rw [inner_conj_symm,inner_conj_symm]; exact hk.symm]
    ring

theorem precise (h : FieldCore W R s X) (B) : weaklyCentral X B ↔ ∀ p f (u v : X.operators.domain),
    let T := X.operators.denselyDefined p f
    ∃ (he : u.val ∈ T.adjoint.domain), inner ℂ (T.adjoint (⟨u.val,he⟩)) (B v.val)=
      inner ℂ u.val (B ((X.operators.field p f v).val)) := by
  have ht (p : S.Union) (f : Test4) := X.operators.really X.J h.total h.adj p f
  have hh p f (u : X.operators.domain) (hp : u.val ∈ (X.operators.denselyDefined p f).adjoint.domain) :
      (X.operators.field (X.J p) (Probe.bar f) u).val=(X.operators.denselyDefined p f).adjoint ⟨u.val,hp⟩ :=
    (ht p f).2 rfl
  constructor
  · intro H p f u v; refine ⟨(ht p f).1 u.property,?_⟩; rw [← hh p f u]; exact H p f u v
  intro H p f u v; obtain ⟨he,hv⟩ := H p f u v; rw [hh p f u he]; exact hv

theorem irreducible (i) (B) : weaklyCentral (L.actors i) B ↔
    ∃ a : ℂ, B=a • ContinuousLinearMap.id ℂ _ := by
  constructor
  · intro h; exact ⟨_,commutant L i B h⟩
  rintro ⟨a,rfl⟩ p g u v
  simp only [_root_.smul_apply,ContinuousLinearMap.id_apply,inner_smul_right]
  apply congrArg
  have h := (L.cores i).adj p g v u
  apply (starRingEnd ℂ).injective
  rw [inner_conj_symm,inner_conj_symm]; exact h.symm
end YM.EveryPhase
