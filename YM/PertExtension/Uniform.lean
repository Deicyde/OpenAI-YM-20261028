import YM.PertExtension.Series
import Mathlib.Analysis.Calculus.Taylor

/-! Finite Taylor calculus in the rescaled tangent variables near a nondegenerate saddle. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Series.Radial
open Function Filter Set Metric
open scoped BigOperators Topology ContDiff Classical
open Zone
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
variable (f : E → ℝ)
protected def zone : Zone E := ⟨fun x=>1 + ‖x‖,fun x => by have := norm_nonneg x; linarith⟩
local notation "Z" => Radial.zone (E:=E)

def jet (k : ℕ)(u : E) : ℝ := ((Nat.factorial k : ℝ))⁻¹ * iteratedFDeriv ℝ k f 0 (fun _=>u)
@[simp] theorem jet_zero (u : E) : jet f 0 u = f 0 := by unfold jet; simp [iteratedFDeriv_zero_apply]

theorem jetInvoice (k : ℕ) : (Z).Invoice (jet f k) := by
  let D := iteratedFDeriv ℝ k f 0
  let c : ℝ := (Nat.factorial k:ℝ)⁻¹
  have hc : 0≤c := by dsimp [c];positivity
  refine ⟨c*‖D‖,k,mul_nonneg hc (norm_nonneg _),fun u=>?_⟩
  calc
   _ = c*‖D (fun _=>u)‖ := by rw [jet, norm_mul];change ‖c‖ * _ = _;rw [Real.norm_eq_abs,abs_of_nonneg hc]
   _ ≤ _ := by
      rw [mul_assoc]; gcongr
      refine le_trans (le_of_eq (by simp : _=‖D (fun _=>u)‖)) ((D.le_opNorm _).trans ?_)
      gcongr; simp [Radial.zone];gcongr; linarith

theorem jet_smul (k)(r : ℝ)(u : E) : jet f k (r • u) = r^k * jet f k u := by
  unfold jet
  simp only [ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]; ring

omit f in
lemma radial_iteratedDeriv {f : E→ℝ} (u : E)(r : ℝ)(k : ℕ) {s : Set E} (hs : IsOpen s)(hr : r • u ∈ s) (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f s) :
    iteratedDeriv k (fun r:ℝ=>f (r • u)) r=iteratedFDeriv ℝ k f (r • u) (fun _=>u) := by
  let L:= ContinuousLinearMap.toSpanSingleton ℝ u
  have hU:=hs.uniqueDiffOn (𝕜:=ℝ); have ht:=(hs.preimage L.continuous).uniqueDiffOn (𝕜:=ℝ)
  have h:=L.iteratedFDerivWithin_comp_right hf hU ht (hx:=hr) (i:=k) (le_rfl)
  have hp : L r ∈ s := hr
  have hd (x) (hx : x ∈ s) := (hf _ hx).contDiffAt (hs.mem_nhds hx)
  have H:ContDiffAt ℝ (k : WithTop ℕ∞) (f ∘ L) r := (hd (L r) hp).comp r L.contDiff.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv ht H hp, iteratedFDerivWithin_eq_iteratedFDeriv hU (hd (L r) hp) hp] at h
  change iteratedDeriv k (f ∘ L) _= _
  rw [iteratedDeriv_eq_iteratedFDeriv,h]; simp [L]

theorem homogeneous_derivative (u : E)(k : ℕ)(hf : ContDiffAt ℝ (k : WithTop ℕ∞) f 0) :
    jet f k u = (k.factorial:ℝ)⁻¹ * iteratedDeriv k (fun t : ℝ=> f (t • u)) 0 := by
  rcases hf.contDiffOn' (m:=k) le_rfl (by simp) with ⟨s,hs,hz,he⟩
  simp only [insert_eq_of_mem (mem_univ ..), univ_inter] at he
  rw [radial_iteratedDeriv u 0 k hs (by simpa using hz) he]; simp [jet]

variable [FiniteDimensional ℝ E]
-- Coercivity from degree two and positive definiteness, vacuous off zero in dimension zero.
theorem quadratic_min (h : ∀ u : E, u ≠ 0 → 0<jet f 2 u) : ∃ c>0, ∀ u, c*‖u‖^2≤jet f 2 u := by
  have H:=isCompact_sphere (0:E) 1
  have nz {u : E} (h : u∈sphere 0 1) : u ≠ 0 := by rintro rfl; simpa using h
  have he : ∃ c>0, ∀ u∈sphere (0:E) 1, c ≤ jet f 2 u := by
    by_cases hN : (sphere (0:E) 1).Nonempty
    · have hCont : ContinuousOn (jet f 2) (sphere (0:E) 1) := by
        apply Continuous.continuousOn
        unfold jet
        apply continuous_const.mul; exact Continuous.comp (iteratedFDeriv ℝ 2 f 0).coe_continuous (continuous_pi (fun i=>continuous_id))
      obtain ⟨u,hu,hb⟩:=H.exists_isMinOn hN hCont
      exact ⟨_, h u (nz hu),hb⟩
    refine ⟨1,one_pos,fun u hu=> (hN ⟨u,hu⟩).elim⟩
  obtain ⟨c,hc,he⟩:=he
  refine ⟨c,hc,fun u=>?_⟩
  by_cases hu : u=0
  · have hz := (jet_smul f 2 0 (0:E)).symm; rw [zero_smul] at hz; simpa [hu] using hz.le
  have hv : ‖u‖ ≠ 0 := (norm_pos_iff.mpr hu).ne'
  let v:= (‖u‖⁻¹) • u
  have hf : u = ‖u‖ • v := by simp [v, smul_smul, hv]
  have hg: v ∈ sphere 0 1 := by simp [v, norm_smul, hv]
  rw (occs := .pos [2]) [hf]
  rw [jet_smul]
  exact (mul_comm _ _).le.trans <| mul_le_mul_of_nonneg_left (he _ hg) (sq_nonneg _)

theorem deposition (n : ℕ)(hf : ContDiffAt ℝ ∞ f 0) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ u (t : ℝ), 0 < t → t*‖u‖ ≤ δ →
      ‖f (t • u) - eval (jet f) n t u‖ ≤ C * ‖u‖^(n+1) * t^(n+1) := by
  let N:= n+1
  rcases hf.contDiffOn' (m:=N) (by exact WithTop.coe_le_coe.mpr le_top) (by simp) with ⟨s,hs,hz,he⟩
  simp only [insert_eq_of_mem (mem_univ ..), univ_inter] at he
  obtain ⟨ε,hε,hM⟩:=Metric.isOpen_iff.mp hs 0 hz
  let δ:=ε/2
  have hδ : 0<δ := half_pos hε
  have hB : closedBall 0 δ ⊆ s := Set.Subset.trans (closedBall_subset_ball (by dsimp [δ]; linarith)) hM
  have hU:= hs.uniqueDiffOn (𝕜:=ℝ)
  have hd (k : ℕ) (hk : k ≤ N) (x : E)(hx : x∈s) : ContDiffAt ℝ k f x := (he.of_le (by exact_mod_cast hk) x hx).contDiffAt (hs.mem_nhds hx)
  obtain ⟨C,hc⟩:= (isCompact_closedBall (0:E) δ).exists_bound_of_continuousOn (he.continuousOn_iteratedFDerivWithin (m:=N) le_rfl hU |>.mono hB)
  have hhh (x)(hx : x∈closedBall (0:E) δ) : ‖iteratedFDeriv ℝ N f x‖ ≤ C := by rw [← iteratedFDerivWithin_eq_iteratedFDeriv hU (hd _ le_rfl _ (hB hx)) (hB hx)];exact hc x hx
  have hC:= (norm_nonneg _).trans (hhh 0 (mem_closedBall_self hδ.le))
  refine ⟨δ,C,hδ,hC,fun u t ht hm=>?_⟩
  let g : ℝ → ℝ := f ∘ (fun t : ℝ=> t • u)
  have hv (r) (hr : r ∈ Icc (0 : ℝ) t) : r • u∈closedBall (0:E) δ := by rw [mem_closedBall_zero_iff,norm_smul_of_nonneg hr.1];exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg u)).trans hm
  have hf (k : ℕ) (hk : k≤N)(r)(hr : r∈Icc (0:ℝ) t) : ContDiffAt ℝ k g r := (hd k hk _ (hB (hv r hr))).comp (f:=fun t : ℝ=>t • u) r (contDiffAt_id.smul (contDiffAt_const (c:=u)))
  have hy (k : ℕ) (hk : k ≤ N) (r) (hr : r ∈ Icc (0:ℝ) t) :
      iteratedDerivWithin k g (Icc (0:ℝ) t) r = iteratedFDeriv ℝ k f (r • u) (fun _=>u):=by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) (hf k hk r hr) hr, ←iteratedDeriv_eq_iteratedFDeriv]; exact radial_iteratedDeriv u r k hs (hB (hv r hr)) (he.of_le (by exact_mod_cast hk))
  have h := taylor_mean_remainder_bound (n:=n) (x:=t) (C:=C*‖u‖^(n+1)) ht.le (f:=g) (by intro x hx; simpa only [N, Nat.cast_add, Nat.cast_one] using! ((hf N le_rfl x hx).contDiffWithinAt (s:=Icc _ _))) (right_mem_Icc.mpr ht.le) ?_; swap
  · intro r hr;rw [hy _ le_rfl r hr]
    apply (ContinuousMultilinearMap.le_of_opNorm_le (hhh _ (hv r hr)) _).trans_eq; simp [N]
  have hh : taylorWithinEval g n (Icc 0 t) 0 t = eval (jet f) n t u:= by
    rw [taylor_within_apply];unfold Zone.eval
    refine Finset.sum_congr rfl fun i hi=>?_
    rw [hy _ (Finset.mem_range.mp hi|>.le) _ (left_mem_Icc.mpr ht.le),zero_smul,sub_zero]; change _ * _= _ * _
    simp [jet];ring
  rw [hh,sub_zero] at h
  refine h.trans ((div_le_iff₀ (mod_cast n.factorial_pos)).mpr ?_)
  have : (1 : ℝ) ≤ n.factorial:= by exact_mod_cast n.factorial_pos
  exact le_mul_of_one_le_right (by positivity) this

theorem ordinary (hf : ContDiffAt ℝ ∞ f 0) : (Z).Built 1 (fun t u=> f (t • u)) (jet f) := by
  refine ⟨jetInvoice f, fun n=> ⟨fun _=>le_rfl,?_⟩⟩
  obtain ⟨δ,C,hδ,hc,h⟩:= deposition f n hf
  refine ⟨δ,C,n+1,hδ,hc,fun u t ht hm=>?_⟩
  have he u : ‖u‖≤ (Z).w u:= by simp [Radial.zone]
  refine (h u t ht ((mul_le_mul_of_nonneg_left (he u) ht.le).trans hm)).trans ?_
  simp only [Pi.one_apply,mul_one];gcongr;apply he

end YM.PertExtension.Series.Radial
