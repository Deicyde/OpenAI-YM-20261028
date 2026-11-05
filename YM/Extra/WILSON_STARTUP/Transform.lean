import YM.Extra.WILSON_STARTUP.Polar

/-! # Shifted Gram inverse in the full counting coordinates -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Polar
open Function Filter Matrix Lattice Bloch Laurent
open scoped Matrix.Norms.Frobenius Topology ComplexOrder BigOperators
variable {ι τ ρ : Type} [Fintype ι] [DecidableEq ι] {n : Side}

omit [DecidableEq ι] in
lemma fiber_mul (F : Site n → Matrix τ ι ℂ) (G : Site n → Matrix ι ρ ℂ) :
    fiber (fun i => F i * G i) = fiber F * fiber G := by
  ext ⟨p,i⟩ ⟨q,j⟩
  by_cases h : p=q
  · subst q; simp [fiber, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  simp [h, fiber, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite]

omit [DecidableEq ι] [Fintype ι] in
lemma fiber_adj (F : Site n → Matrix τ ι ℂ) : fiber (fun p => (F p)ᴴ) = (fiber F)ᴴ := by
  ext ⟨p,i⟩ ⟨q,j⟩; by_cases h : p=q
  · subst q; simp [fiber]
  simp [fiber, h, Ne.symm h]

omit [Fintype ι] in
lemma fiber_one : fiber (fun _ : Site n => (1:Square ι)) = 1 := by ext ⟨p,i⟩ ⟨q,j⟩; by_cases h : p=q <;> simp [fiber,h,Matrix.one_apply]

lemma turn_adj {x : Matrix (Site n × ι) (Site n × ι) ℂ} {P : Site n → Square ι}
    (h : x * rotations n ι = rotations n ι * fiber P) : xᴴ * rotations n ι = rotations n ι * fiber (fun p => (P p)ᴴ) := by
  let r := rotations n ι
  let c := (n.val:ℂ)^4
  have hc : c≠0 := pow_ne_zero _ (side_ne n)
  have hr : r*rᴴ = c • 1 := rotations_gram n ι
  have hr' : rᴴ*r = c • 1 := by
    apply smul_right_injective _ (inv_ne_zero hc)
    change c⁻¹ • _ = c⁻¹ • _
    rw [show c⁻¹ • (rᴴ*r) = (c⁻¹ • rᴴ)*r from (smul_mul ..).symm, inv_smul_smul₀ hc]
    rw [_root_.mul_eq_one_comm, Matrix.mul_smul,hr,inv_smul_smul₀ hc]
  apply smul_right_injective _ hc
  have he : rᴴ*xᴴ = (fiber P)ᴴ*rᴴ := by simpa only [conjTranspose_mul] using congr_arg Matrix.conjTranspose h
  rw [fiber_adj]
  change c • (xᴴ*r)=c • (r* (fiber P)ᴴ)
  calc
    _ = (r*rᴴ)*xᴴ*r := by rw [hr,Matrix.smul_mul, Matrix.one_mul,Matrix.smul_mul]
    _ = r*(fiber P)ᴴ*(rᴴ*r) := by rw [Matrix.mul_assoc r, he, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = _ := by rw [hr', Matrix.mul_smul,Matrix.mul_one]

theorem invert_tori (r : ℝ) (hr : 0 < r) (P S : Row ι ι) (hp : P.safe) (hs : S.safe)
    (h : ∀ v : Momentum,star v=v → S.read v=invert r (param P v)) (n : Side) :
    S.acts n * (r • 1 + (P.acts n).transpose * P.acts n) = 1 := by
  let A := rotations n ι
  let z (p : Site n) := param P (mon p)
  have hz (p : Site n) : z p = ((z p).1,star (z p).1) := by
    have h := param_conjugate P (mon p) (real_frequency p)
    exact Prod.ext rfl (congr_arg Prod.fst h)
  have hb : fiber (fun p => boost r (z p)) = (r:ℂ) • 1 + (fiber (fun p => P.read (mon p)))ᴴ*fiber (fun p : Site n => P.read (mon p)) := by
    rw [← fiber_adj,← fiber_mul,← fiber_one (n:=n) (ι:=ι)]
    ext ⟨p,i⟩ ⟨q,j⟩
    simp only [fiber,Matrix.of_apply, Matrix.add_apply,Matrix.smul_apply]
    by_cases he : p=q
    · subst q; conv_lhs => rw [hz p,boost];
      simp only [if_true]; rfl
    simp [he]
  have hi p : IsUnit (boost r (z p)) := by rw [hz]; exact boost_unit r hr _
  have hu : fiber (fun p => invert r (z p)) * fiber (fun p => boost r (z p)) = 1 := by
    rw [← fiber_mul]
    simp_rw [invert, fun p => Ring.inverse_mul_cancel _ (hi p)]
    exact fiber_one
  let Z := P.acts n
  let Y := S.acts n
  have hZ : approached Z * A = A * fiber (fun p => P.read (mon p)) := circulant n P hp
  have hY : approached Y * A = A * fiber (fun p => invert r (z p)) := by simp_rw [z, ← h _ (real_frequency _)]; exact circulant n S hs
  have hw : approached Z.transpose * A = A * (fiber (fun p => P.read (mon p)))ᴴ := by rw [← fiber_adj, prom_adj]; exact turn_adj hZ
  have hc (r : ℝ) : approached (r • (1:Matrix (Co n ι) (Co n ι) ℝ)) = (r:ℂ) • 1 := by ext i j; by_cases h : i=j <;> simp [approached,h]
  have hx : approached (r • 1 + Z.transpose*Z) * A = A * fiber (fun p => boost r (z p)) := by
    rw [hb, show approached (r • 1 + Z.transpose*Z) = approached (r • 1) + approached Z.transpose*approached Z from ?_, hc,
      Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul, Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one]; congr 1
    · rw [Matrix.mul_assoc,hZ,← Matrix.mul_assoc _ A _,hw,Matrix.mul_assoc]
    rw [← prom_mul]; ext; simp [approached]
  have hone : approached (1: Matrix (Co n ι) (Co n ι) ℝ) = 1 := by simpa using hc 1
  apply prom_inj; rw [prom_mul,hone]
  apply cancel_rotation n
  change approached Y*approached _*A=1*A
  rw [Matrix.mul_assoc,hx,← Matrix.mul_assoc _ A _,hY,Matrix.mul_assoc,hu,Matrix.mul_one,Matrix.one_mul]

theorem deliver (ι : Type) [Fintype ι] [DecidableEq ι] (r η A : ℝ) (hr : 0<r) (hη : 0<η) (hA : 0≤A) : ∃ C τ : ℝ, 0 < τ ∧ 0 ≤ C ∧ ∀ P : Row ι ι,
    P.strip η A → ∃ S : Row ι ι, S.strip τ C ∧ ∀ n : Side, S.acts n * (r • 1 + (P.acts n).transpose * P.acts n) = 1 := by
  obtain ⟨C,τ,hτ,hC,h⟩ := writes (ι:=ι) _ _ _ hr hη hA
  refine ⟨C,τ,hτ,hC,fun P hP => ?_⟩
  obtain ⟨S,hS,he⟩ := h _ hP
  exact ⟨S,hS,invert_tori r hr P S (Row.rights η _ hP hη.le) (Row.rights τ _ hS hτ.le) he⟩
end YM.WilsonStartup.Polar
