import YM.Next.BOUNDARY.Coordinates
import YM.Planned.STATIONARY_JET_PORT.Cable
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.STATIONARY_UNIFORM.Response

set_option warningAsError false

/-! Use stationary Envelopes on ALL cables, and make cables from Scatter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical
variable {ι σ τ π : Type} [Fintype ι] [Fintype τ]
    {n : Side} {N k K : ℕ} {p : Positions τ}
    {l : ι → Site n} {m : τ → Site n} {a r C D : ℝ}

def machinist (N K : ℕ) (D a : ℝ) := partitionsBill N*(1+D*((K:ℝ)*countCost (a/2)))^N
def litSpan (N : ℕ) (r a : ℝ) := min r (weaker N a)
lemma machinist_pos (hD : 0 ≤ D) (ha : 0<a) : 0<machinist N K D a :=
  mul_pos (zero_lt_one.trans_le (partitionsBill_one _)) (pow_pos (by have he := count_pos (half_pos ha); positivity) _)
lemma litSpan_pos (hr : 0<r) (ha : 0<a) : 0<litSpan N r a :=
  lt_min hr (by unfold weaker; positivity)
lemma weaker_le (ha : 0≤a) (N : ℕ) : weaker N a ≤ a := by
  apply div_le_self ha; have : (0:ℝ) ≤ N := Nat.cast_nonneg _; linarith
lemma litSpan_le (ha : 0≤a) (N : ℕ) (r : ℝ) : litSpan N r a ≤ a :=
  le_trans (min_le_right ..) (weaker_le ha N)

/-- Differentiating a local read along a stationary path. -/
lemma hooked {g : Positions ι → Positions τ} {x : Positions ι} {u : Site n} {f : Positions τ → ℝ}
    (hF : ContDiffAt ℝ ω f (g x)) (hg : ContDiffAt ℝ ω g x) (ha : 0<a) (hr : 0<r) (hc : 0 ≤ C) (hd : 0 ≤ D)
    (h : Beacon m a N f u (g x) C) (H : Envelope l m r N g x D) (hm : Multiplicity m K) :
    Beacon l (litSpan N r a) N (f ∘ g) u x (C * machinist N K D a) := by
  intro k hk q
  let F := ftaylorSeries ℝ f (g x)
  let P := ftaylorSeries ℝ g x
  let v (j : Fin k) := bolt (q j)
  let R := glaze l u q (litSpan N r a)
  let Z := D*((K:ℝ)*countCost (a/2))
  have hZ : 0 ≤ Z := by have ht := count_pos (half_pos ha); unfold Z; positivity
  have he (s : OrderedFinpartition k) : ‖(F.compAlongOrderedFinpartition P s) v‖ ≤ C * (1+Z)^N * R := by
    have hu := wire_cost (p:=x) (f:=g) (g:=f) q s hk ha hr hc hd u hm
      (fun i (hi:i≤k) t => h i (hi.trans hk) t)
      (fun i j => H _ (s.partSize_pos i).ne' ((s.partSize_le i).trans hk) _ j)
    apply hu.trans; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc) (Real.exp_pos _).le
    exact (pow_le_pow_left₀ hZ (le_add_of_nonneg_left zero_le_one) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right hZ) (s.length_le.trans hk))
  unfold entry; rw [iteratedFDeriv_comp hF hg le_top, FormalMultilinearSeries.taylorComp,_root_.sum_apply]
  refine le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun j _ => he j))) ?_
  rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
  have hh : (Fintype.card (OrderedFinpartition k):ℝ) ≤ partitionsBill N := Finset.single_le_sum
    (f:=fun i => (Fintype.card (OrderedFinpartition i):ℝ)) (fun i _ => Nat.cast_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_add_one_of_le hk))
  apply (mul_le_mul_of_nonneg_right hh (mul_nonneg (by positivity) (Real.exp_pos _).le)).trans_eq
  unfold Z machinist; ring

variable {β : σ → Site n}
lemma Cable.attach {γ : π → Site n} {F : Positions τ → Matrix σ π ℝ} {g : Positions ι → Positions τ}
    {x : Positions ι} {o : Option (Site n)}
    (hF : bornMatrix F (g x)) (hg : ContDiffAt ℝ ω g x) (h : Cable m β γ o a N F (g x) C)
    (H : Envelope l m r N g x D) (ha : 0<a) (hr : 0<r) (hc : 0 ≤ C) (hd : 0 ≤ D) (hm : Multiplicity m K) :
    Cable l β γ o (litSpan N r a) N (F ∘ g) x (C*machinist N K D a) := by
  intro i j
  have hh : 0 ≤ C*Decay a (β i) (γ j) * thread o a (β i) := mul_nonneg
    (mul_nonneg hc (decay_pos ..).le) (thread_pos ..).le
  have ht := hooked (hF i j) hg ha hr hh hd (h i j) H hm
  apply ht.mono
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left (decay_mono (litSpan_le ha.le N r) (β i) (γ j)) hc)
      (thread_mono o (litSpan_le ha.le N r) (β i)) (thread_pos ..).le (mul_nonneg hc (decay_pos ..).le))
    (machinist_pos (N:=N) (K:=K) hd ha).le
  apply he.trans_eq; ring

-- Root all differentiated legs on the ROW of the matrix (`block` is
-- defined with row in last derivative position). D of a dF goes at the
-- HEAD direction of order 2 derivative; our further peels are from tail.
omit [Fintype ι] in
lemma makeCable {f : Positions τ → ℝ} {s : σ → τ} (hf : ContDiffAt ℝ ω f p) (h : Scatter m a N f p C)
    (hk : k+2 ≤ N) :
    Cable m (m ∘ s) (m ∘ s) none a k
      (fun y => Matrix.of fun i j => entry f y ![s j,s i]) p C := by
  -- Use peel_snoc twice, hence exact orientation at every position.
  intro i j t ht q
  have he : (fun y => (Matrix.of (m:=σ) (n:=σ) fun i j => entry f y ![s j,s i]) i j) =ᶠ[𝓝 p]
      fun y => coordinate (coordinate f (s i)) (s j) y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    have H := peel hy ![s j,s i]
    simp only [of_apply]; rw [H]; unfold entry coordinate
    simp [iteratedFDeriv_one_apply]
  simp only [of_apply] at he ⊢; unfold entry at he ⊢; rw [(he.iteratedFDeriv ℝ t).eq_of_nhds]
  let q' := Fin.snoc (α:=fun _ : Fin (t+1) => τ) q (s j)
  let Q := Fin.snoc (α:=fun _ : Fin (t+2) => τ) q' (s i)
  change ‖entry (coordinate (coordinate f (s i)) (s j)) p q‖ ≤ C* _* _ * glaze m _ _ a
  unfold coordinate; rw [peel_snoc ((hf.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const),peel_snoc hf]
  apply (h (t+2) (by omega) Q (Fin.last (t+1))).trans_eq
  change C * glaze m (m (Q (Fin.last (t+1)))) Q a = _
  unfold Q q'; rw [Fin.snoc_last,glaze_snoc,glaze_snoc,thread_none]
  simp only [Function.comp_apply,Decay,separation_self, Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,mul_one,mul_assoc]

omit [Fintype ι] in
lemma bornBlock {f : Positions τ → ℝ} (s : σ → τ) (hf : ContDiffAt ℝ ω f p) :
    bornMatrix (fun y => Matrix.of fun i j => entry f y ![s j,s i]) p := fun i j =>
  (tend_entry hf ![s j,s i]).1
end YM.Planned.JetPort
