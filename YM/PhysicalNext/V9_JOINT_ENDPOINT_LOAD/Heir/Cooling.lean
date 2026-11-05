import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata


/-! # Numeric delay tests here, after actual prices (still before Bar)

True β needs the joint Band convention. No uniformity claim in widths
retuned after the call. No branch forfeiture on either Field threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Filter Function Lattice Wilson Pressure RG Tree Next Next.SectorChange Exterior Bloch Planned.AtomRegular MeasureTheory
    Extra.Iteration Extra.Iteration.Scales
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {X : Support f} {L : Side} {P B : BudgetPoint} {x u a t K : ℝ} {n r : ℕ} {C : Libretto G n} {D : Record}

lemma flowering (a : ℝ) (n : ℕ) : Tendsto (fun x : ℝ => (1+(radiusB x:ℝ))^n * temp (x+a)) atTop (𝓝 0) := by
  have h := (Work.E09.radiusB_temp n).const_mul ((2:ℝ)^n*2)
  rw [mul_zero] at h; refine squeeze_zero' (Eventually.of_forall fun x => by have := Work.E04.temp_nonneg (x+a); positivity) ?_ h
  filter_upwards [Rebuild.geometry a, Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx hr
  have he := Work.E04.temp_nonneg (x+a); have hE := Work.E04.temp_nonneg x
  calc
    _ ≤ ((2:ℝ)*(radiusB x:ℝ))^n * (2*temp x) := by
      gcongr
      · have h : 1 ≤ (radiusB x:ℝ) := by exact_mod_cast hr
        linarith
      exact hx.2.1
    _ = _ := by rw [mul_pow]; ring

lemma reserve {y : ℝ → ℝ} (h : ∀ᶠ x : ℝ in atTop, 0≤y x ∧ y x ≤ K*(1+(radiusB x:ℝ))) (a t : ℝ) (p : ℕ) (ht : 0<t) (v : ℝ) :
    ∀ᶠ x : ℝ in atTop, (v*temp (x+a))*(y x)^p < t := by
  have he := ((flowering a p).const_mul (|v| * K^p)); rw [mul_zero] at he
  filter_upwards [h,he.eventually (gt_mem_nhds ht)] with x ⟨h,hx⟩ he
  apply lt_of_le_of_lt _ he; have hE := Work.E04.temp_nonneg (x+a)
  calc
    _ ≤ |v| * temp (x+a)*(K*(1+(radiusB x:ℝ)))^p := by gcongr; exact le_abs_self _
    _ = _ := by rw [mul_pow]; ring

lemma reachPays (ht : 0<t) (n : ℕ) : ∀ᶠ x : ℝ in atTop, K*(1+(reach x:ℝ))^n*temp (x+a) < t := by
  filter_upwards [reserve (y:=fun x => 1+(reach x:ℝ)) (K:=46) (Eventually.of_forall (fun x => by unfold reach; push_cast; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)])) a t n ht K] with x hx
  linarith only [hx]
lemma reachExpense (a : ℝ) (ha : 0<a) (n : ℕ) (K : ℝ) (hk : 0 ≤ K) : ∀ᶠ x : ℝ in atTop, K*(1+(reach x:ℝ))^n ≤ Real.exp (a*↑(radiusB x)) := by
  obtain ⟨A,hA,H⟩ := MultiNext.SignedSource.Newt.length_mom n (half_pos ha)
  filter_upwards [(Real.tendsto_exp_atTop.comp (Rebuild.cover_grows.const_mul_atTop (half_pos ha))).eventually_ge_atTop (K*(46:ℝ)^n*A)] with x hx
  let b : ℝ := radiusB x; let y := (a/2)*b
  have hh := H (radiusB x)
  have he : 1+(reach x:ℝ) ≤ 46*(1+b) := by unfold reach b; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  calc
    _ ≤ K*(46*(1+b))^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he _) hk
    _ ≤ (K*46^n*A)*Real.exp y := by rw [mul_pow, ←mul_assoc]; exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by unfold y b; ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hx (Real.exp_pos y).le).trans_eq (by dsimp only [Function.comp_apply]; rw [←Real.exp_add]; unfold y b; congr 1; ring)

def Tight (C : Libretto G n) (D : Record) := D.ε ≤ 1/2 ∧ C.web.scale*D.ε ≤ 1/128

lemma rehearses (hL : licensed C.δ C.N L) (ht : Tight C D) (p b : ℕ) (hp : p≤b) : ∀ᶠ x in atTop,
    ∀ P B : BudgetPoint, P.threshold=temp x → B.threshold=fiery G x L → B.B ≤ 2*radiusB x → P.power=p → P.order=n → n ≤ B.order → B.power=b → Rehearsed C D P B L x := by
  let v:=C.C; let K := C.web.scale
  have hv:=C.C_one; have hk:=C.web.cost; have hQ:=D.majorant; change 1 ≤ v at hv; change 1 ≤ K at hk
  let Q:=D.Q; let t := G.slopeConstant * Real.log L.val
  have hK := radial_pos G
  have h (x : ℝ) : 0 ≤ 1+6*(1+(radiusB x:ℝ)) * (L.val:ℝ) ∧ (1:ℝ)+6*(1+radiusB x)*L.val ≤ (1+6*(L.val:ℝ))*(1+(radiusB x:ℝ)) := by constructor <;> nlinarith only [Nat.cast_nonneg (α:=ℝ) (radiusB x),Nat.cast_nonneg (α:=ℝ) L.val,mul_nonneg (a:=(L.val:ℝ)) (b:=(radiusB x:ℝ)) (by positivity) (by positivity)]
  filter_upwards [Rebuild.geometry t,reachPays (K:=4*G.colorScale) (a:=0) C.Z.pos p, reachPays (K:=v) (a:=0) D.radius p,
    reachPays (K:=Q*v) (a:=0) (lt_min C.web.pos zero_lt_one) p, reachExpense C.δ C.width p (2*K*v) (by positivity),
    reachPays (K:=K*4*(Q*v)^2) (a:=0) (show (0:ℝ)<1/256 by norm_num) (p*2),reachPays (K:=radial G*(Q*v)^2) (a:=0) (show (0:ℝ)<1/2 by norm_num) (p*2),
    reserve (Eventually.of_forall h) t 1 b zero_lt_one 1] with x hx h₁ h₂ h₃ h₄ h₅ h₆ h₇ P B hT hW hr' hp' ho hoo hb'
  simp_rw [add_zero,← hT,pow_mul] at h₁ h₂ h₃ h₅ h₆
  change ((_):Prop) ∧ (fiery G x L ≤ 2*temp x ∧ temp x ≤ 2*fiery G x L) at hx
  have hh := hx.2; rw [← hT, ← hW] at hh
  let s := loom P (reach x) v
  have hs : P.threshold ≤ s := le_trans (le_mul_of_one_le_left P.threshold_pos.le hv) (le_mul_of_one_le_right (mul_nonneg (by positivity) P.threshold_pos.le) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
  have hs' : s < D.r := by unfold s loom; rw [hp']; linarith only [h₂]
  have hs'' : Q*s ≤ min C.web.radius 1 := by unfold s loom; rw [hp']; linarith only [h₃]
  refine ⟨ho,hoo,(hp'.symm ▸ hb'.symm ▸ hp),hT,hW,hL,⟨?_,?_⟩,⟨hT ▸ hh.2,hs',hs'',?_,?_,(le_trans ?_ hs),ht.2⟩,⟨?_,?_,hr'⟩⟩
  · unfold Foliage.Cube.moduleBill; rw [hp']; linarith only [h₁]
  · apply le_trans (b:= s) ?_ ((le_mul_of_one_le_left (P.threshold_pos.le.trans hs) (show 1≤Q from hQ)).trans (hs''.trans (min_le_right ..)))
    unfold s loom Foliage.Cube.moduleBill; gcongr ?_ * _; exact le_mul_of_one_le_left P.threshold_pos.le hv
  · change K*(Q*(temp x+s))^2 ≤ _; rw [←hT]; have h := hh.2
    calc
      _ ≤ K*(Q*(s+s))^2 := by have := P.threshold_pos.le.trans hs; have := P.threshold_pos; gcongr
      _ ≤ _ := by unfold s loom; rw [hp']; nlinarith only [mul_le_mul_of_nonneg_right h₅.le P.threshold_pos.le,h]
  · unfold loom; rw [hp']; have ht := mul_le_mul (mul_le_mul_of_nonneg_right h₄ (by norm_num : 0 ≤ (2:ℝ))) hh.2 P.threshold_pos.le (show 0 ≤ Real.exp _*2 by positivity)
    change K*_ ≤ _; nlinarith [mul_nonneg (le_of_lt B.threshold_pos) (Real.exp_pos (C.δ * radiusB x)).le]
  · nlinarith only [mul_le_mul_of_nonneg_right ht.1 B.threshold_pos.le,hh.1]
  · unfold loom; rw [hp']; change radial G*(Q*(v*_*_))^2 ≤ B.threshold; nlinarith only [mul_le_mul_of_nonneg_right h₆.le P.threshold_pos.le,hh.2]
  rw [hb',hW]; rw [one_mul] at h₇; exact h₇.le
end YM.PhysicalNext.JointLoad.Heir
