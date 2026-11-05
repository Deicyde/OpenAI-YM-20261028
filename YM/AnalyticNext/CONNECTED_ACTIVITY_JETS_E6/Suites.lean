import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac

/-!
# Uniform jets from analytic on patches

Allows general norm, value charts enlarged to actual weak stencils.
Reanchoring (drift) by support rather than period. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Metric Set
open scoped Topology BigOperators ContDiff Classical
variable {E F G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {ι : Type*} {k : ℕ} {d e u v w : ℝ} {f : E→F} {g : F→G} {x : E}
namespace Brush
variable (p : Brush k u d f x)
include p
lemma trim : Brush k (u*(1+d)^k) 1 f x := by
  apply offer.mpr; refine ⟨p.smooth,fun i hi=> ?_⟩
  exact (p.order i hi).trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ p.pos (le_add_of_nonneg_left zero_le_one) _).trans
    (pow_le_pow_right₀ (le_add_of_nonneg_right p.pos) hi)) p.nonneg)
lemma pine (q : Brush k v 1 g (f x)) : Brush k (k.factorial*v) ((1+u)*d) (fun i=> g (f i)) x := by
  apply q.compound p.smooth
  · exact mul_nonneg (add_nonneg zero_le_one p.nonneg) p.pos
  intro i hi hh; apply (p.order i hh).trans; rw [mul_pow]
  exact mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (le_add_of_nonneg_right p.nonneg) (by omega)))
    (pow_nonneg p.pos _)

omit p
lemma linearB (B : E →L[ℝ] F) (hu : ‖B x‖ ≤ u) (he : ‖B‖≤u*d) (hd : 0≤d) : Brush k u d B x := by
  refine ⟨B.contDiff.contDiffAt,hd,?_⟩
  rintro (_|_|i) hi
  · unfold normJ; rwa [norm_iteratedFDeriv_zero,pow_zero,mul_one]
  · change ‖iteratedFDeriv ℝ 1 (⇑B) x‖ ≤ u*d^1; rwa [norm_iteratedFDeriv_one,B.fderiv,pow_one]
  unfold normJ; rw [← norm_iteratedFDeriv_fderiv, show fderiv ℝ (⇑B)=fun _ => B from funext fun _=>B.fderiv,
    iteratedFDeriv_succ_const, Pi.zero_apply,norm_zero]
  exact mul_nonneg ((norm_nonneg _).trans hu) (pow_nonneg hd _)

lemma neighborhood (x : E) (h : ContDiffAt ℝ (↑k) f x) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ y in 𝓝 x, Brush k C 1 f y := by
  let A (i : ℕ) := normJ i f x
  let c:=1+∑ i ∈ Finset.range (k+1), A i
  have hp i : 0≤ A i := norm_nonneg _
  have he (i : ℕ) (hi : i∈Finset.range (k+1)) : ∀ᶠ y in 𝓝 x, normJ i f y < c := by
    have hI : A i < c := lt_of_le_of_lt (Finset.single_le_sum (fun i _=> hp i) hi) (by dsimp only [c]; linarith)
    exact (h.continuousAt_iteratedFDeriv (k:=i) (by rw [Finset.mem_range] at hi; exact_mod_cast Nat.le_of_lt_succ hi)).norm (gt_mem_nhds hI)
  have hc : 0<c := add_pos_of_pos_of_nonneg (by norm_num) (Finset.sum_nonneg fun i _=> hp i)
  refine ⟨c,hc,?_⟩
  filter_upwards [h.eventually (by simp), ((Finset.eventually_all _).mpr he)] with y hy hv
  refine offer.mpr ⟨hy,fun i hi=> (hv i (Finset.mem_range.mpr (by omega))).le⟩
lemma compact {s : Set E} (h : IsCompact s) (he : ∀ x∈s, ContDiffAt ℝ (↑k) f x) :
    ∃ C : ℝ,0 < C ∧ ∀ x∈s, Brush k C 1 f x := by
  let g x:= (1:ℝ)+∑ i∈ Finset.range (k+1),normJ i f x
  by_cases hz : s.Nonempty
  swap
  · exact ⟨1,zero_lt_one,fun x hx=> (hz ⟨x,hx⟩).elim⟩
  have hf (x:E) : 0<g x := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _=> norm_nonneg _)
  have hh : ContinuousOn g s := continuousOn_const.add (continuousOn_finsetSum _ fun i hi x hx=>
    ((he x hx).continuousAt_iteratedFDeriv (k:=i) (by rw [Finset.mem_range] at hi; exact_mod_cast Nat.le_of_lt_succ hi)).norm.continuousWithinAt)
  obtain ⟨x,hx,hm⟩:= h.exists_isMaxOn hz hh
  refine ⟨g x,hf x,fun y hy=> offer.mpr ⟨he y hy, fun i hi=> ?_⟩⟩
  apply le_trans _ (hm hy)
  refine le_trans (Finset.single_le_sum (f:=fun j : ℕ=> normJ j f y) (fun i _=>norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    (le_add_of_nonneg_left zero_le_one)

lemma trail {h : d>0} (p : Brush k v e g (f x)) (r : Brush k (u*d) 1 f x) (he : d*e≤1) :
    Brush k (k.factorial*v) (1+u) (fun i=> g (f i)) x := by
  let H := d • ContinuousLinearMap.id ℝ F
  have hp : ‖H‖ ≤ d := by
    unfold H; rw [norm_smul,Real.norm_of_nonneg h.le]; exact mul_le_of_le_one_right h.le ContinuousLinearMap.norm_id_le
  let F' i:= d⁻¹ • f i; let g' := g ∘ H
  have hx i : H (F' i) = f i := by simp [H,F',smul_smul,h.ne']
  have he' : Brush k v 1 g' (F' x) := (reading H ((hx x).symm ▸ p) hp).climb le_rfl ((mul_comm e d).trans_le he)
  have hf := r.smul d⁻¹; rw [norm_inv, Real.norm_of_nonneg h.le,show d⁻¹*(u*d)=u by field_simp] at hf
  have hF := hf.pine he'
  have heq : (fun x=>g' (F' x))=(fun i=>g (f i)) := funext fun x=> congr_arg g (hx x)
  change Brush k _ _ (fun x=>g' (F' x)) x at hF
  rwa [heq,mul_one] at hF
end Brush
end YM.ConnectedActivityE6.Blaze
