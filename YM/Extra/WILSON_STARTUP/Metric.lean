import YM.Extra.WILSON_STARTUP.Design

/-!
# Compatibility of the top startup prescription

Top-only producers for RRack/RShape/RLoops. Real matrix conclusions and
actual path and unmasked top jet, including needed through degree 4.
Use the *same* Bed and path in continuation. No production of tower step,
coarse modified metric, price gap or full Directed promised here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Design
open Matrix Function Filter RG Wilson Lattice Bloch Work Precision Exterior
open scoped Topology Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} (p : Clip)

def spike (v : ℝ) : Row (TypeFace 2) (TypeFace 2) := fun i j x => if i=j ∧ x=0 then v else 0

def bed : Bed := ⟨spike 1,spike 1,spike 1,spike 1,spike (sideRoot p)⟩

theorem attached : Attached (bed p) (top G p) := by
  refine ⟨fun b q x => ?_⟩
  have e : (bed p).roots (Exterior.plaquette b) (Exterior.plaquette q) x = if b=q ∧ 0=x then sideRoot p else 0 := by simp [bed,spike,plaq_iff,eq_comm]
  rw [e]
  exact hasSum_single 0 (fun i hi => by simp [top,hi])

lemma spike_acts (v : ℝ) (n : Side) : (spike v).acts n = v • 1 := by
  ext ⟨x,i⟩ ⟨y,j⟩; simp only [Row.acts, of_apply, Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  rw [tsum_eq_single 0]; swap
  · intro b hb; simp [spike,hb]
  by_cases h : x=y
  · simp [spike,h,mul_ite]
  simp [h,Ne.symm h]


lemma spike_read (v : ℝ) (m : Momentum) : (spike v).read m = (v:ℂ) • 1 := by
  ext i j; simp only [Row.read, of_apply, Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Laurent.read]
  rw [tsum_eq_single 0]; swap
  · intro b hb; simp [spike,hb]
  by_cases h : i=j <;> simp [spike,h]

lemma spike_strip (v : ℝ) (A σ : ℝ) (hv : ‖v‖ ≤ A) : (spike v).strip σ A := by
  have he : 0 ≤ A := (norm_nonneg _).trans hv
  intro i j
  let f := fun b => Real.exp (σ*(Laurent.size b:ℝ))*‖spike v i j b‖
  have hs := hasSum_single 0 (f:=f) (fun b hb => by simp [spike,hb,f])
  refine ⟨fun _ => by positivity,hs.summable,hs.tsum_eq.trans_le ?_⟩
  have h₀ : Laurent.size (0:Cover)=0 := by simp [Laurent.size]
  simp only [f,h₀,spike, and_true,Nat.cast_zero, mul_zero,Real.exp_zero,one_mul]
  split <;> simpa only [norm_zero]

theorem covered (hp : p.direct ≤ 1) {σ A : ℝ} (hA : 1 ≤ A) : (bed p).covered σ A := by
  have he : ‖sideRoot p‖ ≤ 1 := by rw [Real.norm_of_nonneg (r:=sideRoot p) (Real.sqrt_nonneg _)]; have hs := Real.sq_sqrt (x:=bulk p) (sub_nonneg.mpr hp); unfold bulk at hs; unfold sideRoot bulk; nlinarith [p.quadratic_pos]
  have hh := spike_strip 1 A σ (by simpa using hA)
  exact ⟨hh,hh,hh, spike_strip _ _ _ (he.trans hA), hh⟩

theorem full_root (hp : p.direct ≤ 1) (n : Side) : ((bed p).full p n).transpose*(bed p).full p n=1 := by
  ext i j
  simp only [Matrix.mul_apply,transpose_apply, Bed.full,bed,spike_acts, Matrix.of_apply,smul_eq_mul, Matrix.smul_apply]
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_sum_type]; rw [Finset.sum_add_distrib,← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  simp only [Sum.elim_inl, Sum.elim_inr,Prod.mk.eta,Matrix.one_apply]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Fintype.sum_ite_eq']
  by_cases he : i=j
  · simp [he,← sq,Real.sq_sqrt p.quadratic_pos.le,sideRoot,Real.sq_sqrt (sub_nonneg.mpr hp),bulk]
  simp [he,Ne.symm he]

theorem level (hp : p.direct ≤ 1) (n : Side) {η A : ℝ} (he : η ≤ 1) (ha : 1 ≤ A) : Floor (bed p) p n η A := by
  have hn : Numeric (1 : Matrix (Body 2 n) (Body 2 n) ℝ) η A := fun v => by
    have h : 0 ≤ dotProduct v v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [Matrix.one_mulVec]; exact ⟨mul_le_of_le_one_left h he,le_mul_of_one_le_left h ha⟩
  constructor <;> simp [bed,spike_acts,spike_read,hn]
  exact full_root p hp n

theorem bound_arbitrary (G : Gauge) (hp : p.direct ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀, ∀ Λ ≥ (0:ℝ), (top G p).Bounds p σ C Λ := by
  let d := |sideRoot p| *Real.exp (σ * 4)
  let a := ∑ i : PlaqAxes, (extractAtom G i (panel G p)).budget σ
  refine ⟨max 1 (max d a), lt_of_lt_of_le one_pos (le_max_left ..),fun C hC Λ hΛ => budgets p hp σ C Λ hσ hΛ ?_ ?_⟩
  · exact (le_trans (le_max_left d a) (le_max_right ..)).trans hC
  exact (le_trans (le_max_right d a) (le_max_right ..)).trans hC

lemma quadratic_pull {n : Side} (U : Config G n) (s : Signed) (hp : p.direct ≤ 1) :
    quadratic p (top G p) (pull s 0 U) = quadratic p (top G p) U := by
  let π := fun u : G.El => p.direct * G.price u + bulk p * ‖G.curvature u‖^2/2
  unfold quadratic; simp_rw [ell_sq _ hp]
  change ∑ i : Cell n, π _ = ∑ i : Cell n, π _
  simp_rw [Face.send_price U _ s 0 π (by simp [π]) (fun k g => by simp [π,G.curvature_conjugate])]
  exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s (0:Site n), Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (fun p : Cell n => π (faceValue U p))

lemma top_sworn {n : Side} (hp : p.direct ≤ 1) : Bid.Sworn (bed p) n G := by
  obtain ⟨C,hC,h⟩ := bound_arbitrary p G hp 1 one_pos
  have hb := h _ le_rfl _ (le_refl 0); have hf := level p hp n (le_refl _) (le_refl _)
  have ht (s : Signed) (a : Bid.Dir G n) := F03.quadratic_limit hb (attached p) hf (Bid.pulled a s)
  have he (s : Signed) (x y : Bid.Dir G n) : Bid.pulled (x+y) s = Bid.pulled x s + Bid.pulled y s := by
    funext b
    dsimp only [Bid.pulled,Pi.add_apply]; split <;> simp only [neg_add]
  let Q := fun x y : Bid.Dir G n => Bid.gaugeFiscal (bed p) x y
  have hh (x y : Bid.Dir G n) : Q x y = Q y x := by
    unfold Q; rw [F03.metric_pair _ hb (attached p) _ _ hf, F03.metric_pair _ hb (attached p) _ _ hf]
    apply Finset.sum_congr rfl; intro i _; rw [real_inner_comm (F03.faceCurl i y), real_inner_comm (F03.ellLine _ i y)]
  have hz (s : Signed) (a : Bid.Dir G n) : Q (Bid.pulled a s) (Bid.pulled a s) = Q a a := by
    have hs := ht s a
    simp_rw [← F03.represent_pulled, quadratic_pull p _ s hp] at hs
    have hu := tendsto_nhds_unique hs (F03.quadratic_limit hb (attached p) hf a)
    change Q _ _ / 2 = Q _ _ / 2 at hu; linarith
  have ha (x y z : Bid.Dir G n) : Q (x+y) z = Q x z + Q y z := F03.gaugeFiscal_add ..
  have hk (x y z) : Q x (y+z) = Q x y + Q x z := by rw [hh, ha,hh y x,hh z x]
  intro s a b
  change Q _ _ = _
  have h := hz s (a+b)
  rw [he,ha,ha,hk,hk,hk,hk,hz,hz,hh (Bid.pulled b s) (Bid.pulled a s),hh b a] at h
  linarith

end YM.WilsonStartup.Design
