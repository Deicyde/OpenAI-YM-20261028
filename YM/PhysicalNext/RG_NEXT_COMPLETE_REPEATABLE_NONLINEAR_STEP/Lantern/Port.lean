import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Vast
/-!
# Gaussian normal central invoice. Real b (even), finite radius sustained.
 Moving Hessian, not projecting from E6 row on faith.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {j k : ℕ} {u d v p s A : ℝ}
variable (ϕ ψ : E×Poll.Body ι→ℝ) (ρ : E→Poll.Body ι) (M : E → Matrix ι ι ℝ)

def shade (M : E→Matrix ι ι ℝ) (x : E) := Real.log (M x).det/2
def grace (z : Poll.Body ι) (x : ℝ×E) := shade M x.2-shade M 0+ (vote ϕ ρ z (0,0) - vote ϕ ρ z x)+
    (ψ (visit ρ z 0 x)-ψ (visit ρ z 1 x))  -- ψ positive sign in action

def fee (k : ℕ) (p D : ℝ) := p+p+(acrossE k p D+acrossE k p D)+(clump k (spanE p D) p+clump k (spanE p D) p)
structure Golf (ϕ ψ : E×Poll.Body ι→ℝ) (ρ : E→Poll.Body ι) (M : E → Matrix ι ι ℝ) (j : ℕ) (D u v p : ℝ) : Prop where
  pos : 0 < u
  pos' : 0 < v
  small : u ≤ 1
  small' : v ≤ 1
  off : 0 ≤ D
  curve (x) : ‖x‖<u → Brush (j+2) p 1 ρ x
  color (z t x) : ‖z‖ ≤ D → t∈Icc (0:ℝ) 1 → ‖x.1‖< v → ‖x.2‖<u →
    Brush (j+2) p 1 ϕ (visit ρ z t x) ∧ Brush j p 1 ψ (visit ρ z t x)
  station x : ‖x‖<u → ∀ z, fderiv ℝ ϕ (x,ρ x) (0,z)=0 ∧ dotProduct z.ofLp ((M x) *ᵥ z.ofLp)=scratch (0,z) ϕ (x,ρ x)
  gram x : ‖x‖<u→(M x).PosDef ∧ Brush j p 1 (fun x=> shade M x-shade M 0) x
section tries
variable {ϕ ψ ρ M} (D : ℝ) (h : Golf ϕ ψ ρ M j D u v p)
    {x : ℝ×E} (hx : ‖x.2‖ < u) (he : ‖x.1‖< v) {z : Poll.Body ι} (hz : ‖z‖ ≤ D)
include h
lemma run_vote (y : ℝ×E) (hy : ‖y.1‖ < v) (hv : ‖y.2‖ < u) : ‖y‖ ≤ 1 := max_le (hy.le.trans h.small') (hv.le.trans h.small)

include hz he hx
variable [FiniteDimensional ℝ E]
lemma commit : Brush j (acrossE j p D) 1 (vote ϕ ρ z) x := by
  have hh : ∀ᶠ y : ℝ×E in 𝓝 x, ‖y.1‖<v ∧ ‖y.2‖<u := ((continuous_norm.comp continuous_fst).continuousAt.eventually (gt_mem_nhds he)).and
    ((continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hx))
  exact election ϕ ρ _ x (hh.mono fun _ H=> run_vote D h _ H.1 H.2) (hh.mono fun _ H=> (h.curve _ H.2).smaller (by omega)) hz (hh.mono fun _ hi t ht=> (h.color z t _ hz ht hi.1 hi.2).1)

lemma compel : Brush j (fee j p D) 1 (grace ϕ ψ ρ M z) x := by
  let K:= ContinuousLinearMap.snd ℝ ℝ E
  have h₀:‖(0:E)‖<u:=by rw [norm_zero]; exact h.pos
  have hw : Brush j (acrossE j p D) 1 (fun _ : ℝ×E=> vote ϕ ρ z (0,0)) x:= (Brush.certified zero_le_one _).climb ((commit D h (x:=(0,0)) h₀ (show ‖(0:ℝ)‖<v by rw [norm_zero]; exact h.pos') hz).bound) le_rfl
  have hu : Brush j (p+p) 1 (fun x:ℝ×E=> shade M x.2 - shade M 0) x := by
    have he := Brush.reading K (h.gram _ hx|>.2) (ContinuousLinearMap.norm_snd_le ..); rw [one_mul] at he
    apply he.climb (le_add_of_nonneg_right (h.curve _ hx).nonneg) le_rfl
  have hm t (ht:t∈Icc (0:ℝ) 1) := composite (camp ρ ht (run_vote D h x he hx) ((h.curve _ hx).smaller (show j≤j+2 by omega)) hz) (h.color _ _ _ hz ht he hx).2
  refine (hu.gathering (hw.separating (commit D h hx he hz))).gathering ((hm 0 (by simp)).separating (hm 1 (by simp)))
end tries

lemma zeroC (z) : grace ϕ ψ ρ M z (0,0)=0:= by simp [grace,visit]
lemma oppositeC (x : ℝ×E) (z) : grace ϕ ψ ρ M (-z) (-x.1,x.2)=grace ϕ ψ ρ M z x := by
  unfold grace; rw [← pivot]; simp only [show vote ϕ ρ (-z) (0,0)=vote ϕ ρ z (0,0) from Eq.symm (by simpa using pivot ϕ ρ z 0 0)]
  simp [visit]
lemma symL (M : Matrix ι ι ℝ) (x : Poll.Body ι) : lens₀ M (-x)=lens₀ M x:= by unfold lens₀; rw [show WithLp.ofLp (-x)= -x.ofLp from rfl, Matrix.mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]

def ballots (D : ℝ) (x : ℝ×E) (z : Poll.Body ι) := (closedBall 0 D).indicator (fun z=> Real.exp (grace ϕ ψ ρ M z x)) z
def ratify (D : ℝ) (x : ℝ×E) := ∫ z, ballots ϕ ψ ρ M D x z ∂Poll.sweep (M 0)⁻¹
lemma rolls_even (D : ℝ) (h : (M 0).PosDef) : let f:= ratify ϕ ψ ρ M D; f ∘ (fun x=>(-x.1,x.2)) = f := by
  intro f; let K:= (M 0)⁻¹; funext x
  change (∫ z, ballots ϕ ψ ρ M D _ z ∂_) = ∫ z, ballots ϕ ψ ρ M D x z ∂_
  rw [recommends K h.inv,recommends K h.inv]
  let F z:= lens₀ K z * ballots ϕ ψ ρ M D (-x.1,x.2) z
  change (∫ z,F z) = _
  rw [← integral_neg_eq_self F] -- volume
  apply integral_congr_ae; filter_upwards with z; unfold F ballots; rw [symL]; simp only [Set.indicator, mem_closedBall_zero_iff,norm_neg]
  split_ifs; rw [oppositeC]; rfl

variable {x : E}
-- Gaussian term at b=0, includes exact determinants
lemma meter (z : Poll.Body ι) (h : ∀ v∈({0,x}:Set E), (M v).PosDef ∧ ∀ z:Poll.Body ι, dotProduct z.ofLp ((M v)*ᵥ z.ofLp)=scratch (0,z) ϕ (v,ρ v)) :
    lens₀ (M 0)⁻¹ z * Real.exp (grace ϕ ψ ρ M z (0,x)) = lens₀ (M x)⁻¹ z := by
  have hp v (hv:v∈({0,x}:Set E)) : ∀ z:Poll.Body ι, lens₀ (M v)⁻¹ z= (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp (shade M v-vote ϕ ρ z (0,v))) := fun z=> by
    rw [roll,lens₀,Matrix.nonsing_inv_nonsing_inv _,det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv, h v hv|>.2]
    unfold shade; ring_nf
    exact isUnit_iff_ne_zero.mpr (h v hv).1.det_pos.ne'
  simp only [hp _ (Set.mem_insert ..),hp _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))]; rw [grace,visit,visit]; simp only [smul_zero,zero_smul,add_zero,sub_self]; rw [mul_assoc, ← Real.exp_add]; ring_nf
end YM.PhysicalNext.Repeat.Lantern
