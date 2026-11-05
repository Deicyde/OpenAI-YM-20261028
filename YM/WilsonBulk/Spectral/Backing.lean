import YM.WilsonBulk.Spectral.Release

/-! Export unprojected joint flat inverse in actual Width norm. No requirement of increasing D
with ANY previous history, no IR claims, pay `ℝ` budget after L and prescribed clip/ε/kernel,
keep η before LENGTH. commonM real cells uses `frontR` (no nonlinear jets). This kernel is NOT
projected to the strict Wilson tree slice (see next modules). -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Work.F08 Precision Exterior Stationary Audience Matrix Set
open scoped Topology BigOperators Classical

variable {K : KernelChoices} {L c f : Side} {P : Patch} {G : Gauge}
  {η σ ε Ω C W : ℝ}

def completedM (G : Gauge) (B : Bed) (S : StepData c f) (t : S.Choices) :=
  let F:= postroom (G:=G) S t (inch S.patch.L)
  repackM (clothe G S) (clothe G S) (frontR G S B+F.transpose*F)

def jointInverse (G : Gauge) (P : Patch) (K : KernelChoices) (B : Bed) :=
  crystals fun p=> (forceK G P (regulatorF G P) K.penalty B p)⁻¹

lemma patch_coherent (h : P.Branches K G) (B : Bed) (hσ : 0< σ) (hB : B.metric.strip (inch P.L*σ) Ω) :
    ∃ (M : ℕ → Side), Tendsto (fun i => (M i).val) atTop atTop ∧
      ∀ i, ∃ A : Matrix (Co (M i) (ParcelG G P.L)) (Co (M i) (ParcelG G P.L)) ℝ,
        Jaunt (approached A) (forceK G P (regulatorF G P) K.penalty B) 0 := by
  let M : ℕ → Side := fun i => ⟨i+1,Nat.zero_lt_succ _⟩
  have he : Tendsto (fun i => (M i).val) atTop atTop :=
    tendsto_atTop_mono (fun i => (show i ≤ i+1 by omega)) tendsto_id
  refine ⟨M,he,fun i=>?_⟩
  let S : StepData (M i) (M i*P.L) := ⟨P,K,rfl⟩
  let V : S.Choices := Classical.arbitrary _
  exact ⟨completedM G B S V, complete_ticket S V h B hB hσ⟩

lemma uses_budget (h : P.Branches K G) (B : Bed) (hσ : 0<σ) (hB : B.metric.strip (inch P.L*σ) Ω)
    (hη : 0<η)
    (H : Poster η (forceK G P (regulatorF G P) K.penalty B))
    (hp : Freezer (slabW G P.L).dual (slabW G P.L)
      (forceK G P (regulatorF G P) K.penalty B) η C)
    (hw : ∀ p∈strip η, vflux (forceK G P (regulatorF G P) K.penalty B p)⁻¹ ≤ W) :
    (jointInverse G P K B).strip (η/2) (castCost η W) ∧
      ∀ (c f : Side) (hb : f.val=c.val*P.L.val) (t : (StepData.mk P K hb).Choices),
        completedM G B (StepData.mk P K hb) t * (jointInverse G P K B).acts c=1 := by
  obtain ⟨M,hM,hV⟩:= patch_coherent h B hσ hB
  refine ⟨crystal_budget _ (inverse_poster H hp.period) hη hw, ?_⟩
  intro c f hv t
  have he := output_inverse H hp hη hw (fun p hP => inverse_reality p hM hV H hη hP)
      (complete_ticket (StepData.mk P K hv) t h B hB hσ)
  convert! he using 1
  congr!

lemma uniform_backing (G : Gauge) (j : ℕ) (K : KernelChoices) (σ ε Ω : ℝ)
    (hσ : 0<σ) (hε : 0<ε) (hΩ : 0≤ Ω) :
    ∃ η, 0 < η ∧ ∀ L : Side, ∃ A, 0 ≤ A ∧ ∀ P : Patch, P.J=j → P.L=L →
      P.Branches K G → ∀ B : Bed, ∀ p D, B.metric.strip (inch P.L*σ) Ω → (∀ n, Floor B p n ε D) →
      (jointInverse G P K B).strip η A ∧
        ∀ (c f : Side) (hb : f.val=c.val*P.L.val) (t : (StepData.mk (c:=c) (f:=f) P K hb).Choices),
        completedM G B (StepData.mk P K hb) t * (jointInverse G P K B).acts c=1 := by
  obtain ⟨η,C,hη,h,H,U⟩:= completion_choice G j K σ ε Ω hσ hε hΩ
  refine ⟨η/2,by positivity,fun L=>?_⟩
  obtain ⟨W,hW,P⟩:= postCost η (slabW G L) (continuous_slabW G L)
  refine ⟨castCost η (C*W),castCost_nonneg hη.le (mul_nonneg H hW),fun S hj hL hP B p D hB hp=> ?_⟩
  subst L; have hx := U S hj hP B p D hB hp
  exact uses_budget hP B hσ hB hη hx.1 hx.2 (P _ C hx.1 hx.2)

end YM.WilsonBulk
