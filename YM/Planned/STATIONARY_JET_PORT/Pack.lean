import YM.Planned.STATIONARY_JET_PORT.Laplacian

set_option warningAsError false

/-! Bundle the reusable, order/radius-sensitive log and inverse service -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical
variable {ι σ τ : Type} [Fintype ι] {n : Side} {l : ι → Site n} {m : τ → Site n} {u : σ → Site n}
    {p : Positions ι} {A : Positions ι → Matrix τ τ ℝ} {N K k : ℕ} {C D a M : ℝ} {o : Option (Site n)}

-- `tow` with the other-end dummy becomes a new cable in the opposite convention. Doesn't need symmetry.
lemma Cable.switch {A : Positions ι → Matrix τ σ ℝ} (ha : 0<a) (hc : 0 ≤ C) (h : Cable l m u o a N A p C) :
    Cable l u m o (slip N a) N (fun y => (A y).transpose) p C := by
  intro j i k hk q
  change ‖entry (fun x => A x i j) p q‖ ≤ _
  refine (h.paid i j q hk).trans ?_
  let y := u j; let x := m i
  have hz := tow l y x x o hk q ha
  simp only [Decay,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at hz
  -- target has full decay a at xy; tow prepays HALF that, dummy z=x gives decay slip y x
  have hm : Decay a x y ≤ Decay (a/2) y x := by rw [decay_comm]; exact decay_mono (half_lt_self ha).le _ _
  change C*(Decay a x y*thread o a x*glaze l x q a) ≤ C*_ *thread _ _ _ * glaze _ _ _ _
  rw [mul_assoc (C*_),mul_assoc C,mul_assoc (Decay a x y)]
  refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hm (mul_nonneg
    (thread_pos ..).le (Real.exp_pos _).le)).trans ?_) hc
  rw [← mul_assoc (Decay (slip N a) _ _)]
  exact hz



lemma shift_finger {σ : Type} [DecidableEq σ] (h : bornMatrix A p) (i : σ ↪ τ) (t : ℝ) (d : ι) :
    ∀ j k, (fun y => finger (caisson A t i) d y j k) =ᶠ[𝓝 p] (fun y => finger A d y (i j) (i k)) := by
    intro j k; filter_upwards [(h (i j) (i k)).eventually (by simp)] with z hz
    unfold finger caisson coordinate; simp only [of_apply,Matrix.add_apply,Matrix.submatrix_apply]
    rw [fderiv_fun_add (hz.differentiableAt (by simp)) (differentiableAt_const _),fderiv_const_apply,add_zero]

theorem caisson_finger {σ : Type} [DecidableEq σ] (hF : bornMatrix A p)
    (h : Cable l m m none a (N+1) A p C) (i : σ ↪ τ) (t : ℝ) (d : ι) :
    Cable l (m ∘ i) (m ∘ i) (some (l d)) a N (finger (caisson A t i) d) p C := by
  intro j k e he q
  unfold entry; rw [((shift_finger hF i t d j k).iteratedFDeriv ℝ e).eq_of_nhds]
  exact (h.takeFinger hF (show N<N+1 from Nat.lt_succ_self N) d) (i j) (i k) e he q

-- API cost definitions. One spare order required for N+1 log.
def directRate (K k : ℕ) (a M C : ℝ) := weakLine (ruling a M C K) k
def directCost (K k : ℕ) (a M C : ℝ) := lineCost (ruling a M C K) C (grounding M) K k
def logRate (K N : ℕ) (a M C : ℝ) := weaker (N+1) (slip N (directRate K N a M C))
def logging (K N : ℕ) (a M C : ℝ) := loopBill (directRate K N a M C) C (directCost K N a M C) K N

lemma directRate_pos {K k : ℕ} (ha : 0<a) (hm : 0<M) (hc : 0<C) : 0<directRate K k a M C := weakLine_pos (ruling_pos ha hm hc K) k
lemma directRate_le {K k : ℕ} (ha : 0<a) (hm : 0<M) (hc : 0<C) : directRate K k a M C ≤ a :=
  (weakLine_cap (ruling_pos ha hm hc K) k).trans (min_le_left ..)
lemma directCost_pos {K k : ℕ} (ha : 0<a) (hm : 0<M) (hc : 0<C) : 0<directCost K k a M C :=
  lineCost_pos (ruling_pos ha hm hc K) hc (grounding_pos hm) k K
lemma logRate_pos {K N : ℕ} (ha : 0<a) (hm : 0<M) (hc : 0<C) : 0<logRate K N a M C :=
  div_pos (slip_pos N (directRate_pos ha hm hc)) (by positivity)
lemma logging_pos {K N : ℕ} (ha : 0<a) (hm : 0<M) (hc : 0<C) : 0<logging K N a M C :=
  loopBill_pos (directRate_pos ha hm hc) hc (directCost_pos ha hm hc) N K

/-- Born/actual full here; shifted estimates extend to all restrictions
(including no restriction; see `.whole_inverse`, `.whole_log`). -/
structure BlockPack [Fintype τ] (l : ι → Site n) (m : τ → Site n)
    (K N : ℕ) (a M C : ℝ) (A : Positions ι → Matrix τ τ ℝ) (x : Positions ι) : Prop where
  rate_pos : 0<a
  cost_pos : 0<C
  mass_pos : 0<M
  smooth : bornMatrix A x
  herm : (A x).IsHermitian
  pay : Charge (A x) M
  coefficient : Cable l m m none a (N+1) A x C
  resolvent {θ : Type} [Fintype θ] [DecidableEq θ] (i : θ ↪ τ) (t : ℝ) (ht : 0 ≤ t) :
    let F := caisson A t i; let β := m ∘ i
    Charge (F x) (M+t) ∧ (F x).IsHermitian ∧ 0<(F x).det ∧ (F x)⁻¹*F x=1 ∧ F x*(F x)⁻¹=1 ∧
      Sealed β (groundRate a M C K) (F x)⁻¹ (grounding M/(1+t)) ∧
      bornMatrix (fun y => (F y)⁻¹) x ∧
      (∀ k ≤ N+1, Cable l β β none (directRate K k a M C) k (fun y => (F y)⁻¹) x
        (directCost K k a M C/(1+t))) ∧
      (∀ v, (∑ j, ((F x)⁻¹ *ᵥ v) j ^ 2) ≤ (M+t)⁻¹^2 * ∑ j, (v j)^2)
  integral {θ : Type} [Fintype θ] [DecidableEq θ] (i : θ ↪ τ) (t : ℝ) (ht : 0 ≤ t) :
    let H y := Real.log ((caisson A t i y).det)
    ContDiffAt ℝ ω H x ∧ Scatter l (logRate K N a M C) (N+1) H x (logging K N a M C/(1+t))

variable [Fintype τ]

theorem establish (ha : 0<a) (hc : 0<C) (hm : 0<M) (hs : bornMatrix A p)
    (hH : (A p).IsHermitian) (hp : Charge (A p) M)
    (h : Cable l m m none a (N+1) A p C) (hM : Multiplicity m K) : BlockPack l m K N a M C A p := by
  have build (θ : Type) [Fintype θ] [DecidableEq θ] (i : θ ↪ τ) (t : ℝ) (ht : 0 ≤ t) :=
    rebuild ha hm hc hM hs hH hp h i t ht
  refine ⟨ha,hc,hm,hs,hH,hp,h,(fun i t => build _ i t),?_⟩
  intro θ _ _ i t ht H
  obtain ⟨_,_,hd,_,_,_,_,he,_⟩ := build _ i t ht
  let F := caisson A t i
  let v := directRate K N a M C
  have hF := hs.collar t i
  refine ⟨hF.determinant.log hd.ne',?_⟩
  have hv : 0<v := directRate_pos ha hm hc
  have hh (d : ι) := (caisson_finger hs h i t d).rate hc.le (directRate_le (k:=N) (K:=K) ha hm hc)
  let D := directCost K N a M C
  have hD : 0<D := directCost_pos ha hm hc
  have hg := logdet_scatter (M:=F) hF hd.ne' (hM.comp i.injective) hv hc (show 0<D/(1+t) by positivity)
    hh (he N (Nat.le_succ N))
  change Scatter _ _ _ H p (logging _ _ _ _ _ /(1+t)); change Scatter _ (logRate K N a M C) _ H p _ at hg
  rw [show logging K N a M C/(1+t) = loopBill v C (D/(1+t)) K N by unfold logging loopBill D v; ring]
  exact hg

omit [Fintype ι] [Fintype τ] in
lemma allSigma [DecidableEq τ] (A : Positions ι → Matrix τ τ ℝ) : caisson A 0 (Function.Embedding.refl τ) = A := by
  funext; simp [caisson]

namespace BlockPack
variable (h : BlockPack l m K N a M C A p)
include h

lemma whole_log [DecidableEq τ] :
    let H y := Real.log (A y).det
    ContDiffAt ℝ ω H p ∧ Scatter l (logRate K N a M C) (N+1) H p (logging K N a M C) := by
  have he := h.integral (Function.Embedding.refl τ) 0 le_rfl
  simpa only [allSigma,add_zero,div_one] using he
end BlockPack
end YM.Planned.JetPort
