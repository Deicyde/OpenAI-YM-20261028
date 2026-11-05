import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Kitchen
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Daisy Daisy.Charity Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
variable {W : ℝ → Code G n}
variable (h : Season (X.pours d) P W o r B (P.supportExponent+1)) (hp : Vapor X d P w) (he : Payments.Rates P.B A B w κ)
include h
lemma widening : Season ((drawer G n).pours (widen X d)) P (fun t=>stuff (upK X) (W t)) o r B (P.supportExponent+1):=by
  refine ⟨by dsimp only [widen, pours]; rw [h.term]; rfl,fun v hv=>?_, h.burn.1, ?_,?_⟩
  · apply (Rack.preserves X (spice d (W v)) P).forced_family (?_) (fun _ _ _ => Iff.rfl) (fun _ => MeasurableSet.univ) (fun _ _ _ _ _ => rfl)
    exact h.permit v hv -- family maybe requires exact A.reg/d; definitional
  · intro v hv i hK
    by_cases he:i∈ Set.range (upK X)
    · obtain ⟨i,rfl⟩:= he; change o∉((drawer G n).kernel _).support at hK; rw [hard_up] at hK; dsimp only ; rw [stuffed,stuffed]; exact h.burn.2.1 v hv _ hK
    dsimp only; rw [blank _ _ he, blank _ _ he]
  obtain ⟨f,hf,hB,hv⟩:=h.burn.2.2
  let i:=upK X; refine ⟨stuff i f,(Rack.positive i f hf),fun x=> ?_,fun x hx k y=> ?_⟩
  · refine transfer_budget i ?_ ?_ (hB x)
    · intro z; simp only [pours,i,stuffed]; rw [hard_up]; rfl
    intro z hz; split; rw [blank _ f hz, zero_mul]; rfl
  by_cases ht:k∈Set.range i
  · obtain ⟨k,rfl⟩:=ht; dsimp only [i]; simp_rw [stuffed]; exact hv _ hx _ _
  rw [blank _ _ ht]; exact (by change Est _ _ _ (fun j=> stuff i (W j) _ _); simp_rw [blank _ _ ht,Pi.zero_apply]; exact Est.nil 0 _ _ _ h.burn.1 (by simp))
omit h
include hp
lemma shown : Vapor (drawer G n) (Rack.widen X d) P w:=by
  constructor
  · intro i; by_cases hi:i∈ Set.range (upS X)
    · obtain ⟨i,rfl⟩:=hi; simp only [widen,soft_up,stuffed]; exact hp.texts i
    dsimp only [widen]; rw [blank _ _ hi]; exact fun _ _ _ _=>rfl
  · intro i; by_cases hi:i∈ Set.range (upS X)
    · obtain ⟨i,rfl⟩:=hi; simp only [widen,stuffed,soft_up]; exact hp.visits i
    dsimp only [widen]; rw [blank _ _ hi]; exact fun _ _=>rfl
  · intro i; by_cases hi:i∈ Set.range (upS X)
    · obtain ⟨i,rfl⟩:=hi; simp only [widen,stuffed]; exact hp.travels i
    dsimp only [widen]; rw [blank _ _ hi]; exact fun _ _=>rfl
  · intro i; by_cases hi:i∈ Set.range (upS X)
    · obtain ⟨i,rfl⟩:=hi; simp only [widen,stuffed]; exact hp.tails i
    dsimp only [widen]; rw [blank _ _ hi]; exact measurable_const
  obtain ⟨f,h,hF⟩:=hp.funds
  refine ⟨stuff (upS X) f,⟨Rack.positive _ _ h.1,fun x=>transfer_budget (upS X) ?_ ?_ (h.2 x)⟩,fun i V=>?_⟩
  · simp [stuffed, Rack.soft_up]
  · intro z hz; simp [blank _ f hz]
  by_cases hx:i∈Set.range (upS X)
  · obtain ⟨i,rfl⟩:=hx; simp only [widen,stuffed]; exact hF i V
  dsimp only [widen]; rw [blank _ f hx, blank _ _ hx]; simp
include h
lemma winters (F : ℕ ≃ (drawer G n).Pellet) (t : ℝ)(ht:|t| * r≤1)(U:Config G n) : HasSum (fun i=> (fused F P (widen X (spice d (W t)))).gasOccurrence P i U)
    ((black (X.pours d) (W t)).gas P U * Real.exp (∑' i,d.logarithm i U)):=by
  have hy:= Passage.gathered (F:=F) (hearth (widening h) (shown hp) t ht) U
  rw [show (spice (widen X d) (stuff (upK X) (W t)))= (widen X (spice d (W t))) from rfl] at hy
  rw [(Rack.preserves _ _ _).same_gas, Rack.same_log] at hy; exact hy
-- Redraws none. No need Supplies.Order from C.Prepared.
end YM.PhysicalNext.Repeat.Mallow
