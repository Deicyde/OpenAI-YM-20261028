import YM.Next.FREE_KERNELS.Curl
import YM.Next.FREE_KERNELS.Warm

/-!
# Physical positivity (including S=1 torus)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate

variable {ι n : Type*} {m : Type} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
lemma bands_ensemble {v A : ℝ} {L : Side} (X : Site L → Matrix m m ℂ) (h : ∀ i, Band (X i) v A) : Band (fiber X) v A := by
  intro x
  let f (a : Site L) (i : m) := x (a,i)
  have he : pairingRe (fiber X) x x=∑ a, pairingRe (X a) (f a) (f a) := by
    have ht a i : (fiber X *ᵥ x) (a,i)=(X a*ᵥ f a) i := by simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,fiber,ite_mul]; rfl
    unfold pairingRe dotProduct; rw [Fintype.sum_prod_type,Complex.re_sum];
    refine Finset.sum_congr rfl fun a _ => ?_; simp_rw [ht]; rfl
  have hc : sqLength x=∑ a,sqLength (f a) := by unfold sqLength dotProduct; rw [Fintype.sum_prod_type,Complex.re_sum]; rfl
  change v*sqLength x ≤ pairingRe _ _ _ ∧ pairingRe _ _ _ ≤ A*sqLength x
  rw [he,hc,Finset.mul_sum,Finset.mul_sum]; exact ⟨Finset.sum_le_sum fun a _ => (h a (f a)).1,Finset.sum_le_sum fun a _ => (h a (f a)).2⟩

lemma volume_dot [Fintype n] [DecidableEq n] (x y : m → ℂ) {F : Matrix n m ℂ} {v : ℝ} (g : Crew F (v:ℂ)) :
    dotProduct (star (F*ᵥx)) (F*ᵥy)=(v:ℂ)*dotProduct (star x) y := by
  rw [Matrix.star_mulVec, dotProduct_mulVec,Matrix.vecMul_vecMul,g.2.2,Matrix.vecMul_smul,Matrix.vecMul_one,smul_dotProduct]; rfl
lemma obey_band (R : Row m m) (hr : Whole R) {v A : ℝ} (h : Funds R v A) (n : Side) :
    (R.acts n).IsSymm ∧ Numeric (R.acts n) v A := by
  have hh (p : Site n) := h (mon p) (real_frequency p)
  constructor
  · unfold Matrix.IsSymm; rw [← acts_trans]; exact Whole.eq_on hr.flipped hr (fun p hp => by rw [read_opposite _ hp.1]; exact (h p hp.1).1) n
  let L := fun p : Site n => R.read (mon p)
  let k := (n.val:ℝ)^4; have hk : 0<k := pow_pos (side_pos _) _
  have hm := bands_ensemble L (fun i => (hh i).2)
  let F := rotations n m
  have hF : Crew F (k:ℂ) := by
    have hx := rotations_crew n m; rw [show stageVolume n=(k:ℂ) from by unfold stageVolume k; push_cast; rfl] at hx
    exact hx
  intro x
  let x' (i) := (x i:ℂ)
  let A' := approached (R.acts n)
  let y := ((k:ℂ)⁻¹ • Fᴴ) *ᵥ x'
  have hK : (k:ℂ)≠0 := by exact_mod_cast hk.ne'
  have he : F*ᵥy=x' := by unfold y; rw [Matrix.mulVec_mulVec,Matrix.mul_smul,hF.2.1,smul_smul,inv_mul_cancel₀ hK,one_smul, Matrix.one_mulVec]
  have hG : A'*ᵥx'=F*ᵥ(fiber L *ᵥ y) := by rw [← he,Matrix.mulVec_mulVec y,Matrix.mulVec_mulVec y,show A'*F=_ from circulant n R hr.safe]
  have h1 : dotProduct x x = k*sqLength y := by
    have hx : dotProduct x x=(dotProduct (star x') x').re := by simp [x',dotProduct,Complex.re_sum]
    rw [hx,← he,volume_dot _ _ hF]; simp [sqLength]
  have h2 : dotProduct x (R.acts n*ᵥ x)=k*pairingRe (fiber L) y y := by
    have hz : dotProduct x (R.acts n*ᵥx)=(dotProduct (star x') (A'*ᵥx')).re := by simp [x',A',Matrix.mulVec,dotProduct,Complex.re_sum,Finset.mul_sum,approached]
    rw [hz,hG,← he,volume_dot _ _ hF]; simp [pairingRe]
  rw [h1,h2]; have hu : v*sqLength y ≤ pairingRe _ y y ∧ pairingRe (fiber L) y y ≤ A*sqLength y := hm y
  constructor
  · rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hu.1 hk.le
  rw [mul_left_comm A]; exact mul_le_mul_of_nonneg_left hu.2 hk.le

omit [DecidableEq m] in
lemma normS_price (A : Matrix m m ℂ) {C : ℝ} (h : ∀ i j, Silver (A i j))
    (hp : ∀ i j, i ≠ j → A i j=0) (hb : ∀ i, C ≤ ‖A i i‖) (x : m → ℂ) : C*sqLength x ≤ pairingRe A x x := by
  let g i := (A i i).re
  have he : pairingRe A x x=∑ i, g i * ‖x i‖ ^ 2 := by
    have hh i : (A*ᵥx) i=(g i:ℂ)*x i := by
      change ∑ j, A i j*x j=_
      rw [Finset.sum_eq_single i, (show A i i=(g i:ℂ) from (h i i).of_real.symm)]
      intro j _ he; rw [hp _ _ he.symm,zero_mul]; simp
    unfold pairingRe dotProduct; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hh, Pi.star_apply,mul_left_comm, mul_comm (star (x i)),Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, ← Complex.ofReal_mul,Complex.ofReal_re]
  rw [he,Work.F06.sqLength_apply,Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ((hb i).trans_eq (h i i).norm) (by positivity)

variable {j : ℕ}
lemma heart_heats (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : ι → Train j) : Warm (fun i => pink k (v i)) ∧ Warm fun i => blue k (v i) := by
  obtain ⟨σ,C,hσ,hC,H⟩ := heart_banked k hk hj v
  let B i := blue k (v i); let A i := pink k (v i)
  have hc (i : ι) (p) (hp : p∈baseCube) :
      IsHermitian ((A i).read p) ∧ IsHermitian ((B i).read p) ∧ ∀ x,
        C⁻¹ * sqLength x ≤ pairingRe ((A i).read p) x x ∧ C⁻¹ * sqLength x ≤ pairingRe ((B i).read p) x x := by
    have he := base_subset_realCube zone_pos hp
    let X := pulse k (v i) p; let Y := vault k (v i) p
    obtain ⟨ha,hb⟩ := heart_true k hk hj (v i)
    have hA : (A i).read p=X := ha.echo p hp; have hB : (B i).read p=Y := hb.echo p hp
    have hj a b := heart_silver k hk (v i) he a b
    have hdx (a b) (hab : a ≠ b) : X a b=0 := by unfold X; rw [pulse_diagonal,if_neg hab]
    have hdy (a b) (hab : a ≠ b) : Y a b=0 := by unfold Y; rw [vault_diagonal,if_neg hab]
    have hm (a : TypeFace 2) : ‖X a a‖ * ‖Y a a‖=1 := by
      have hh := congr_fun (congr_fun (show X*Y=1 from (pulse_pays k hk (v i) he).1) a) a
      rw [Matrix.mul_apply,Finset.sum_eq_single a, Matrix.one_apply_eq] at hh; rw [← norm_mul,hh,norm_one]
      intro j _ hx; rw [hdx _ _ hx.symm,zero_mul]; simp
    rw [hA,hB]; obtain ⟨h1,h2⟩ := heart_Herm k hk (v i) he
    have hP (x y : ℝ) (hx : x*y=1) (hh : 0≤x) (hg : y≤C) : C⁻¹ ≤ x := by
      rw [inv_le_iff_one_le_mul₀ hC]; exact hx ▸ (mul_le_mul_of_nonneg_left hg hh)
    refine ⟨h1,h2,fun x => ⟨normS_price X  (fun i j => (hj i j).1) hdx ?_ x,
      normS_price Y  (fun i j => (hj i j).2) hdy ?_ x⟩⟩
    · exact fun a => hP _ _ (hm a) (norm_nonneg _) (hB ▸ Work.F06.row_entry_le (H i).2 hσ.le p hp.1 a a)
    exact fun a => hP _ _ ((mul_comm ..).trans (hm a)) (norm_nonneg _) (hA ▸ Work.F06.row_entry_le (H i).1 hσ.le p hp.1 a a)
  obtain ⟨hA,hB⟩ := heart_saves k hk hj v
  refine ⟨safe_lower_gives A hA _ (inv_pos.mpr hC) (fun i p hp => ?_),safe_lower_gives B hB _ (inv_pos.mpr hC) (fun i p hp => ?_)⟩
  · obtain ⟨ha,-,hb⟩ := hc i _ (inside_base hp); unfold inside at ha hb; simp_rw [Row.periods] at ha hb; exact ⟨ha,fun x => (hb x).1⟩
  obtain ⟨-,ha,hb⟩ := hc i _ (inside_base hp); unfold inside at ha hb; simp_rw [Row.periods] at ha hb; exact ⟨ha,fun x => (hb x).2⟩
end YM.Next.Free
