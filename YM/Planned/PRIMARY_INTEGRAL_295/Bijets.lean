import YM.Next.FREE_KERNELS.Amend
import YM.Planned.PRIMARY_INTEGRAL_295.Headroom
import YM.Planned.PRIMARY_INTEGRAL_295.Rays
import YM.Work.B04

/-!
# Exact moment rule on powers of one axis-probe form

No limiting normalized kernel. Exponential rows on the cover agree on
these test jets with using the one residue-zero row and replacing position
by the continuous evaluation x/L (including the exact unit coefficient).
This identity is just E's differentiated `jas0` in a convenient form.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Filter Function Set Lattice Laurent Bloch Exterior RG Precision Next.Free Next.Free.Flight Place
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}
variable (k : ℝ) (hk : 0 < k) (P : Flight j t) (ht : 4 ≤ t)

include hk ht
lemma status (x : Cover) (a b : Axis) (p : Momentum) (h : p∈baseCube) :
    let A := member (linesOf P k) x a b
    mode p (cellar P.L x) * RRead A p = ∑ l : Site P.L,
      mode (aliasAt p l) x * (((P.L.val:ℂ))⁻¹*pilot k P p l (coord a) (coord b)) := by
  intro A; let r := wrap P.L x; let T := lift r
  have he : RRead A p = spread (pilot k) 1 [] P r p (coord a) (coord b) := (secure_both k hk P.legal ht).1.bankRead P.legal 1 (by simp) P r h _ _
  rw [he]; unfold spread; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,listChip,List.map_nil,List.prod_nil,mul_one,toll,pow_one,Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have ht : mode p (cellar P.L x) * mode (aliasAt p l) T = mode (aliasAt p l) x := by
    conv_rhs => rw [balance P.L x]
    rw [mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one,mul_comm]
  simpa only [← mul_assoc] using congr_arg (fun z => z * (((P.L.val:ℂ))⁻¹*pilot k P p l (coord a) (coord b))) ht

/-- Constant sum, even on nonzero residues. -/
lemma origin_money (x : Cover) (a b : Axis) :
    ∑' z, member (linesOf P k) x a b z = if a=b then ((P.L.val:ℝ))⁻¹ else 0 := by
  let A := member (linesOf P k) x a b
  have h := status k hk P ht x a b 0 (show (0:Momentum)∈baseCube from ⟨star_zero _,fun i => by simp [Real.pi_pos.le]⟩)
  dsimp only at h
  have he (f : Cover→ℝ) : RRead f 0 = ((∑' i,f i:ℝ):ℂ) := by
    unfold RRead Laurent.read; simp only [mode_constant,one_smul]; rw [Complex.ofReal_tsum]
  rw [mode_constant,one_mul,he,Finset.sum_eq_single (0:Site P.L)] at h
  · apply Complex.ofReal_injective
    have hx : aliasAt (0:Momentum) (0:Site P.L) = 0 := toe_zero P
    rw [h,hx,mode_constant,one_mul,P.pilot_origin]
    rw [Matrix.one_apply]; by_cases he : a=b <;> simp_all [coord]
  · intro i _ hi; rw [pilot_none P k hi]; simp
  simp

lemma vanish_message {f : ℝ→ℂ} (hf : ContDiffAt ℝ ω f 0) (x : RouteProbe) (l : Site P.L) (hl : l≠0)
    (a b : Axis) (n : ℕ) (h : n<j) :
    iteratedDeriv n (fun t => f t * pilot k P (ray x t) l (coord a) (coord b)) 0=0 := by
  let v p := pilot k P p l (coord a) (coord b)
  have hb : ContDiffAt ℝ ω v 0 := (pilot_silva k hk P ht _ _ _).analyticAt.restrictScalars.contDiffAt
  have hg : ContDiffAt ℝ ω (fun t => v (ray x t)) 0 := ((ray_root x).symm ▸ hb).comp _ (ray_smooth x).contDiffAt
  rw [iteratedDeriv_fun_mul (hf.of_le le_top) (hg.of_le le_top)]
  apply Finset.sum_eq_zero; intro i hi
  have h0 : iteratedDeriv (n-i) (fun t => v (ray x t)) 0=0 := pilot_vanish k hk P ht l hl _ _ (ray_root x) (ray_smooth x).contDiffAt _ (by omega)
  rw [h0]; simp

lemma resonate (x : Cover) (a b : Axis) (w : RouteProbe) (s : E4) (n : ℕ) (h : n<j) :
    let v := (P.L.val:ℝ)⁻¹
    iteratedDeriv n (pulseAt w (s+seat (cellar P.L x)) (member (linesOf P k) x a b)) 0=
      iteratedDeriv n (fun t => tune (w (s+v • seat x)) t * ((P.L.val:ℂ))⁻¹ * pilot k P (ray w t) 0 (coord a) (coord b)) 0 := by
  classical
  intro v
  let A := member (linesOf P k) x a b
  let B (l : Site P.L) (t : ℝ) := tune (w s) t * mode (aliasAt (ray w t) l) x * ((P.L.val:ℂ))⁻¹
  let D (l : Site P.L) (t : ℝ) := B l t * pilot k P (ray w t) l (coord a) (coord b)
  have HE : pulseAt w (s+seat (cellar P.L x)) A =ᶠ[𝓝 0] (fun t => ∑ l : Site P.L, D l t) := by
    filter_upwards [ray_in w] with t ht'
    rw [pulse_lift,map_add,tune_add,← through_mode, mul_assoc,status k hk P ht x a b _ ht',Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; unfold D B; ring
  have hb (l) : ContDiffAt ℝ ω (B l) 0 := by
    have hA : ContDiffAt ℂ ω (fun p => mode (aliasAt p l) x) (ray w 0) := by
      unfold mode aliasAt; fun_prop
    have hB : ContDiffAt ℝ ω (fun p => mode (aliasAt p l) x) (ray w 0) := hA.analyticAt.restrictScalars.contDiffAt
    have hz : ContDiffAt ℝ ω (tune (w s)) 0 := by
      -- can use restriction from complex formula
      let f (z : ℂ) := Complex.exp ((w s:ℂ)*z*Complex.I)
      have hc : ContDiffAt ℂ ω f (Complex.ofRealCLM 0) := by unfold f; fun_prop
      have hh := (show ContDiffAt ℝ ω f (Complex.ofRealCLM 0) from hc.analyticAt.restrictScalars.contDiffAt).comp _ (ContinuousLinearMap.contDiff Complex.ofRealCLM).contDiffAt
      rw [show tune (w s)=f ∘ Complex.ofRealCLM from funext fun z => by simp [tune,f]]; exact hh
    unfold B; exact (hz.mul (hB.comp (f:=ray w) _ (ray_smooth w).contDiffAt)).mul contDiffAt_const
  have hL (l) : ContDiffAt ℝ ω (D l) 0 := by
    let f p := pilot k P p l (coord a) (coord b)
    have h : ContDiffAt ℝ ω f (ray w 0) := (ray_root w).symm ▸ (pilot_silva k hk P ht l _ _).analyticAt.restrictScalars.contDiffAt
    exact (hb l).mul (h.comp _ (ray_smooth w).contDiffAt)
  change iteratedDeriv n (pulseAt _ _ A) 0 = _
  rw [HE.iteratedDeriv_eq, iteratedDeriv_fun_sum (fun l _ => (hL l).of_le le_top),Finset.sum_eq_single (0:Site P.L)]; swap
  · intro i _ hi; exact vanish_message k hk P ht (hb i) w i hi a b n h
  swap; · simp
  have he (t : ℝ) : B 0 t = tune (w (s+v • seat x)) t *((P.L.val:ℂ))⁻¹ := by unfold B; rw [map_add, narrow_mode,tune_add]
  simp_rw [D,he]

/-- `a`th moment exactly the principal prediction on every row, on
cover coordinate powers here. Even old `x=0,L=...`, n=0. -/
lemma pure_moment (x : Cover) (a b : Axis) (w : RouteProbe) (n : ℕ) (h : n < j) :
    let q z := member (linesOf P k) z a b
    let s := (P.L.val:ℝ)⁻¹ • seat x
    ∑' z, (w (seat ((cellar P.L x)+z)))^n * q x z = ∑' z, (w (s+seat z))^n * q 0 z := by
  obtain ⟨σ,C,hσ,hC⟩ := stored P k hk ht
  intro q s
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ (show Complex.I^n≠0 from by simp)
  have ht' := resonate k hk P ht x a b w 0 n h
  have h0 := resonate k hk P ht 0 a b w s n h
  simp only [zero_add] at ht'; simp only [seat_zero,zero_cellar,smul_zero,add_zero] at h0
  have hu (i : Cover) : Width σ C (q i) := hC _ _
  simp_rw [seat_add]; rw [← moment_probe w _ _ hσ (hu x),← moment_probe w _ _ hσ (hu 0)]; exact ht'.trans h0.symm
end YM.Planned.PrimaryIntegral295.Carrier
