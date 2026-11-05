import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Colors
import YM.AnalyticNext.QUARTIC_MATCH.Local.Direction


/-!
# The weighted rough and coarse-local directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l c f : Side} {ι : Type} [DecidableEq ι]
namespace Evoke
open Green (wt)
open Tracks
variable (S : StepData c f)
local notation "L" => (S.ratio.count.val:ℝ)

lemma spotBuy {α β : Type} [Fintype α] [Fintype β] (x : α×β→ℝ) (j : β) : rlen (fun i => x (i,j)) ≤ ell2 x := by
  apply (sq_le_sq₀ (ell_nonneg _) (ell_nonneg _)).mp; rw [square_length,square_length, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun i _ => Finset.single_le_sum (f:=fun j => ‖x (i,j)‖^2) (fun _ _ => by positivity) (Finset.mem_univ j)
lemma spinBuy {α : Type} [Fintype α] (a : α→G.Color) {x : G.ColorIndex→ℝ} (_hx : ∀ i,0≤x i)
    (h : ∀ i,rlen (fun k => a k i) ≤ x i) : rlen (fun k => ‖a k‖)^2 ≤ ∑ i,x i^2 := by
  apply le_trans _ (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (ell_nonneg _) (h i) 2))
  apply le_of_eq; unfold rlen; simp_rw [square_length, Real.norm_of_nonneg (norm_nonneg _)]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl
  intro i _; exact PiLp.norm_sq_eq_of_L2 ..
lemma incomeGain {α : Type} [Fintype α] {t : Vertical G c f} (u : α→G.Color) (C : ℝ) (h : 0 ≤ C)
    (hx : ∀ i,rlen (fun k => u k i) ≤ C*stake S t i) : rlen (fun k => ‖u k‖) ≤ C*shares S t := by
  apply (sq_le_sq₀ (ell_nonneg _) (mul_nonneg h (shares_nonneg ..))).mp
  exact (spinBuy u (fun i => mul_nonneg h (stake_nonneg ..)) hx).trans_eq (by simp_rw [mul_pow,← share_count,Finset.mul_sum])

def roughC (η : ℝ) := 1+dc 1 η
lemma rough_ge (η : ℝ) : 1 ≤ roughC η := le_add_of_nonneg_right (dc_pos ..).le

omit [DecidableEq ι] in
theorem contributes {η t : ℝ} (hp : 0 < η) (hy : |t| ≤ η) (P : Purse ι (Site f))
    (w : Vertical G c f) (z : Site f) (k : ι) (hk : P.mark=some k) (hc : P.cap=L^2) (hb : P.amps k=roughC η*shares S w)
    (hx : ∀ i,P.toll k i=wt (-t/L) i z) : Presents S P k (0,polar S t z w) := by
  let K i := stake S w i
  let W := w.1; let X := w.2; let u := polar S t z w
  let b := roughC η; let g := shares S w; have hg : 0 ≤ g := shares_nonneg ..; have hB : 1 ≤ b := rough_ge _; have hL := side_pos S.ratio.count
  have he : P.tagged {k} := ⟨k,Finset.mem_singleton_self _,hk⟩
  have hy0 (i : Site f) (x : G.Color) : P.price {k} i*‖wt (t/L) i z • x‖=‖x‖ := by
    rw [price,Finset.prod_singleton,hx, norm_smul, Real.norm_of_nonneg (Green.wt_pos ..).le, neg_div, lefties,inv_mul_cancel_left₀ (Green.wt_pos ..).ne']
  have hm : P.target {k}=b*g := by unfold target; rw [Finset.prod_singleton,hb]
  have ha (i : G.ColorIndex) : ell2 (parts G 1 W i)/L ≤ K i ∧ ell2 (sitePart X i) ≤ K i ∧ ell2 (d 1 f*ᵥ parts G 1 W i)≤K i := by
    unfold K stake gain; change let l : ℝ := L; let x := ell2 (parts G 1 W i)/L; let y := ell2 (sitePart X i); let p := ell2 (d 1 f *ᵥ parts G 1 W i);
          let b := ell2 ((d 0 f).transpose *ᵥ parts G 1 W i); x ≤ p+b+x+y ∧ y ≤ p+b+x+y ∧ p ≤ p+b+x+y
    dsimp only; have hu := ell_nonneg ((d 0 f).transpose *ᵥ parts G 1 W i); have hh := ell_nonneg (sitePart X i)
    have hc := ell_nonneg (d 1 f *ᵥ parts G 1 W i); have hl := div_nonneg (ell_nonneg (parts G 1 W i)) hL.le; constructor <;> grind
  refine ⟨fun j => ⟨by positivity,fun x => (x he).elim, fun h => ?_⟩, fun j => ⟨by positivity,fun x => (x he).elim,fun h => ?_⟩,
    fun _ => Pays.zero zero_le_one, zero_le_one,fun x => (x (show (Yard.cap S P).tagged {k} from he)).elim,fun _ => ?_⟩
  · change rlen (fun i => P.price {k} i*‖wt (t/L) i z • W (i,j)‖) ≤ P.cap*L⁻¹*P.target {k}
    simp_rw [hy0,hc,hm]
    refine (incomeGain S (t:=w) (fun i => W (i,j)) L hL.le ?_).trans ?_
    · intro i
      exact (spotBuy (parts G 1 W i) j).trans (((div_le_iff₀ hL).mp (ha i).1).trans_eq (mul_comm ..))
    change L*g ≤ L^2*L⁻¹*(b*g); rw [show L^2*L⁻¹=L by field_simp]; gcongr; exact le_mul_of_one_le_left hg hB
  · let a i := P.price {k} i • faceCurl (i,j) u.1
    have hu i : ‖a i‖=P.price {k} i*‖faceCurl (i,j) u.1‖ := by rw [show a i=_ from (rfl : a i=P.price {k} i • _),norm_smul,Real.norm_of_nonneg (P.price_pos _ _).le]
    change rlen (fun i => _*‖faceCurl (i,j) u.1‖) ≤ P.cap*(L^2)⁻¹*P.target {k}
    rw [show (fun i => P.price {k} i*‖faceCurl (i,j) u.1‖)=(fun i => ‖a i‖) from funext fun i => (hu i).symm,
      hc, hm, mul_inv_cancel₀ (pow_ne_zero 2 hL.ne'),one_mul]
    refine incomeGain S _ b (zero_le_one.trans hB) fun i => ?_
    let y := parts G 1 W i
    let Z := feeF S (-t) z (d 1 f*ᵥ feeF S t z y)
    have hh : (fun k => a k i)=(fun l => Z (l,plaquette j)) := by
      funext p; unfold a; rw [price,Finset.prod_singleton,hx]; rfl
    rw [hh]; apply (spotBuy Z _).trans
    have he' := digit S hp zero_le_one (show |-t| ≤ 1*η by rwa [abs_neg,one_mul]) le_rfl z y (sitePart X i)
    simp only [one_mul, neg_neg] at he'; change ell2 (Z-(d 1 f *ᵥ y)) ≤ dc 1 η*K i at he'
    have h1 := (ell_tri (Z-(d 1 f *ᵥ y)) (d 1 f *ᵥ y)).trans (add_le_add he' (ha i).2.2)
    rw [sub_add_cancel] at h1; exact h1.trans_eq (show dc 1 η*K i+ K i=(1+dc 1 η)*K i from by ring)
  · have hy i : (Yard.cap S P).price {k} i *‖u.2 i‖=‖X i‖ := by rw [Yard.cap_price]; exact hy0 ..
    change rlen (fun i => _*‖u.2 i‖) ≤ 1*1*P.target {k}; simp_rw [hy,hm,mul_one,one_mul];
    have HH i : ell2 (fun k => X k i) ≤ 1*K i := by rw [one_mul]; exact (spotBuy (sitePart X i) vac).trans (ha i).2.1
    exact (incomeGain S _ 1 zero_le_one HH).trans ((one_mul g).le.trans (le_mul_of_one_le_left hg hB))

/-- Standalone sparse curvature. for downstream or top. -/
def factor (η : ℝ) := 4*Real.exp η
lemma factor_ge {η : ℝ} (hp : 0≤η) : 1 ≤ factor η := by unfold factor; linarith [Real.one_le_exp hp]
omit [DecidableEq ι] in
lemma coarse_enough (P : Purse ι (Site c)) {η : ℝ} (hp : 0 ≤ η) (i : ι) (he : ¬ P.tagged {i})
    (x : Cell (Per c)) (v : G.Color) (ht : P.amps i=factor η*‖v‖) (hh : ∀ j,P.toll i j=wt η j x.1) :
    let y := sparse x v
    (∀ k : TypeFace 1,P.Pays {i} (fun p => y (p,k)) 1) ∧ (∀ j : PlaqAxes,P.Pays {i} (fun p => faceCurl (p,j) y) 1) := by
  intro y; let t (p : Site c) := P.price {i} p
  have hy (p : Body 1 c) (z : Site c) (hx : separation z p.1 ≤ 1) : t z * ‖y p‖ ≤ Real.exp η*‖v‖ := by
    unfold y t; rw [sparse_at,price, Finset.prod_singleton,hh]; split
    · rename_i hr; have hy : x.1=p.1 := congr_arg (fun j : Cell (Per c) => j.1) hr; rw [hy]
      refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (norm_nonneg _); exact mul_le_of_le_one_right hp (by exact_mod_cast hx)
    rw [norm_zero,mul_zero]; positivity
  constructor <;> intro j <;> refine ⟨zero_le_one,fun _ p => ?_,fun h => (he h).elim⟩
  · rw [target,Finset.prod_singleton,ht,one_mul]
    exact (hy (p,j) p (by simp)).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (by norm_num : (1:ℝ)≤4)) (by positivity))
  change t p* ‖faceCurl (p,j) y‖ ≤ _
  have h := P.price_pos {i} p
  rw [target,Finset.prod_singleton,ht,one_mul, faces]
  apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (norm_sub_le ..))) (show 0 ≤ t p from h.le)).trans
  have H1 := hy (p+step j.val.1,coord j.val.2) p (Response.by_one p (posDir j.val.1)).1
  have H2 := hy (p,coord j.val.2) p (by simp)
  have H3 := hy (p+step j.val.2,coord j.val.1) p (Response.by_one p (posDir j.val.2)).1
  have H4 := hy (p,coord j.val.1) p (by simp)
  simp only [mul_add]; exact (add_le_add (add_le_add H1 H2) (add_le_add H3 H4)).trans_eq (by unfold factor; ring)
end Evoke
end YM.AnalyticNext.QuarticMatch.Local
