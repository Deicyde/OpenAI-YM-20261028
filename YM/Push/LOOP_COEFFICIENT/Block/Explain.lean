import YM.Push.LOOP_COEFFICIENT.Block.Bulk


/-!
# Applying the per-alias budgets to unnormalized fine-root orders
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Set Filter Matrix Metric Lattice Laurent RG Precision Exterior Bloch Kernel Wilson Paths Continuum Complex Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d E F : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [Fintype d] [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] {A C η : ℝ} {n : ℕ} {G : Gauge} {L : Side} {Y : Profiles L c d} {V : Vertex c a b}

lemma linear_scale {M : E →ₗ[ℂ] F} (_hA : 0≤A) (h : ∀ x,‖x‖≤1 → ‖M x‖≤A) (x : E) : ‖M x‖ ≤ A*‖x‖ := by
  by_cases hx : x=0; · simp [hx]
  have he := h (((‖x‖:ℂ)⁻¹) • x) (by simp [norm_smul,hx])
  simpa [norm_inv, norm_smul,inv_mul_eq_div,div_le_iff₀ (norm_pos_iff.mpr hx)] using he
lemma linear_scale₂ {M : E →ₗ[ℂ] E →ₗ[ℂ] F} (hA : 0≤A) (h : ∀ x y, ‖x‖≤1 → ‖y‖≤1 → ‖M x y‖ ≤ A) (x y : E) : ‖M x y‖ ≤ (A*‖x‖)*‖y‖ := linear_scale (mul_nonneg hA (norm_nonneg _)) (fun z hz => linear_scale (M:=(M.flip z)) hA (fun v hv => h v z hv hz) x) y
structure Heights (L : Side) (V : Vertex c a b) (n : ℕ) (η A : ℝ) : Prop where
  nonneg : 0≤A
  base q i : q∈Tube η → ‖V.base (aliasAt q (L:=L) i)‖ ≤ A * (energy L q i)^n
  one q p i j : q∈Tube η → p∈Tube η → ∀ z, ‖z‖≤1 → ‖V.one (aliasAt q (L:=L) i) (aliasAt p (L:=L) j) z‖ ≤ A * (energy L q i+energy L p j)^(n-1)
  two q p s i j l : q∈Tube η → p∈Tube η → s∈Tube η → ∀ z w, ‖z‖≤1 → ‖w‖≤1 → ‖V.two (aliasAt q (L:=L) i) (aliasAt p (L:=L) j) (aliasAt s (L:=L) l) z w‖ ≤ A
lemma energy_ceiling (L : Side) (q l) : energy L q l ≤ 5 := by
  let p := Fine.shade (aliasAt q l)
  have he (i : Axis) := show ‖Exterior.q p i‖≤2 from (norm_sub_le ..).trans (by norm_num [p,Fine.shade,Complex.norm_exp])
  have ht := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (he i) 2)
  simp [Axis] at ht
  have hh := Real.sqrt_le_iff.mpr (And.intro (by norm_num : 0 ≤ (4:ℝ)) (show Fine.deltaFreq p ≤ 4^2 by unfold Fine.deltaFreq; norm_num at *; exact ht))
  unfold energy; linarith [inv_le_one_of_one_le₀ (show 1≤(L.val:ℝ) by exact_mod_cast L.pos)]

omit [DecidableEq a] in
lemma toll_two_aux (h : Heights L V n η A) (Y : Profiles L c d) (q p s) (hq : Active₂ (Tube η) q p s) (hp : p∈Tube η) (hs : s∈Tube η) z w i j l : (energy L (-(q+p+s)) (-(i+(j+l))))⁻¹ * (energy L q i)⁻¹ * ‖V.two (aliasAt q i) (aliasAt p j) (aliasAt s l) (Y p j *ᵥ z) (Y s l *ᵥ w)‖ ≤ A * ((heft L (-(q+p+s)) (-(i+(j+l))))⁻¹*(heft L q i)⁻¹ * rate Y p z j * rate Y s w l) := by
  refine (mul_le_mul_of_nonneg_left (linear_scale₂ h.nonneg (h.two q p s i j l hq.1 hp hs) _ _) (mul_nonneg (inv_pos.mpr (energy_pos ..)).le (inv_pos.mpr (energy_pos ..)).le)).trans_eq ?_
  unfold heft rate; rw [mul_inv (L.val:ℝ), mul_inv (L.val:ℝ)]; field_simp [side_pos L |>.ne']
omit [DecidableEq a] in
lemma heights_quadratic (h : Heights L V 2 η A) (Y : Profiles L c d) : Toll (fun q i => (energy L q i)⁻¹) (fun q i => (energy L q i)⁻¹) V Y η A := by
  have he q i := energy_pos L q i; have hl := side_pos L; have ha := h.nonneg
  refine ⟨fun q i hq => ?_,fun q p z i j hq hp hz => ?_,fun q p s z w i j l hq hp hs _ _ => toll_two_aux h Y q p s hq hp hs z w i j l⟩
  · rw [energy_neg]; exact (mul_le_mul_of_nonneg_left (h.base q i hq) (mul_nonneg (inv_pos.mpr (he q i)).le (inv_pos.mpr (he q i)).le)).trans_eq  (by field_simp [he q i |>.ne'])
  have ht := h.one q p i j hq.1 hp; norm_num at ht
  let v := Y p j *ᵥ z; refine (mul_le_mul_of_nonneg_left (linear_scale (by have := he q i; have := he p j; positivity) ht v) (mul_nonneg (inv_pos.mpr (he ..)).le (inv_pos.mpr (he ..)).le)).trans ?_
  have hpos := he (-(q+p)) (-(i+j)); unfold rate heft; change _ ≤ A * (_*((L.val:ℝ)*‖v‖)+_*((L.val:ℝ)*‖v‖)+_*_*(_*((L.val:ℝ)*‖v‖)))
  have hi := he q i; have hj := he p j; field_simp [he q i,he p j]; nlinarith [mul_nonneg ha (mul_nonneg (norm_nonneg v) hpos.le)]

omit [DecidableEq a] in
lemma heights_linear {v u : Weight L} (h : Heights L V 1 η A) (Y : Profiles L c d) (hp : (v = (fun _ _ => 1) ∧ u = (fun q i => (energy L q i)⁻¹)) ∨ (v = (fun q i => (energy L q i)⁻¹) ∧ u = (fun _ _ => 1))) : Toll v u V Y η (5*A) := by
  have he q i := energy_pos L q i; have hl := side_pos L; have ha := h.nonneg
  have h₂ q p s z w i j l (hq : Active₂ (Tube η) q p s) (hp : p∈Tube η) (hs : s∈Tube η) := mul_le_mul_of_nonneg_left (toll_two_aux h Y q p s hq hp hs z w i j l) (by norm_num : (0:ℝ) ≤ 5)
  have h₀ q i (hq : q∈Tube η) := (show _ ≤ A*energy L q i by simpa using h.base q i hq)
  have h₁ q p z i j (hq : Active₁ (Tube η) q p) (hp : p∈Tube η) := linear_scale ha (show ∀ v, ‖v‖≤(1:ℝ) → ‖V.one (aliasAt q i) (aliasAt p j) v‖ ≤ A by simpa using! h.one q p i j hq.1 hp) (Y p j *ᵥ z)
  have hv q i : 1 ≤ 5*(energy L q i)⁻¹ := by rw [← div_eq_mul_inv,le_div_iff₀ (he q i),one_mul]; exact energy_ceiling ..
  rcases hp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals refine ⟨fun q i hq => ?_,fun q p z i j hq hp hz => ?_,fun q p s z w i j l hq hp hs _ _ => ?_⟩
  case refine_1 => simp only [one_mul]; refine (mul_le_mul_of_nonneg_left (h₀ q i hq) (inv_pos.mpr (he ..)).le).trans ?_; have := he q i; field_simp; nlinarith [he q i]
  case inr.refine_1 => simp only [energy_neg,mul_one]; refine (mul_le_mul_of_nonneg_left (h₀ q i hq) (inv_pos.mpr (he ..)).le).trans ?_; have := he q i; field_simp; nlinarith [he q i]
  case refine_2 =>
    have hpos := he (-(q+p)) (-(i+j)); have ht := he q i; have hu := he p j; let x := ‖Y p j *ᵥ z‖
    simp only [one_mul]; unfold rate heft; refine (mul_le_mul_of_nonneg_left (h₁ q p z i j hq hp) (inv_pos.mpr ht).le).trans ?_; change _ * (A*x) ≤ 5*A*(_*((L.val:ℝ)*x) + _*((L.val:ℝ)*x) + _*(_*((L.val:ℝ)*x)))
    have hx : 0≤x := norm_nonneg _; field_simp; nlinarith [mul_nonneg (mul_nonneg hx ha) ht.le, mul_nonneg (mul_nonneg hx ha) hu.le, mul_nonneg (mul_nonneg hx ha) hpos.le]
  case inr.refine_2 =>
    have hpos := he (-(q+p)) (-(i+j)); have ht := he q i; have hu := he p j; let x := ‖Y p j *ᵥ z‖
    simp only [mul_one]; unfold rate heft; refine (mul_le_mul_of_nonneg_left (h₁ q p z i j hq hp) (inv_pos.mpr hpos).le).trans ?_; change _ * (A*x) ≤ 5*A*(_*((L.val:ℝ)*x) + _*((L.val:ℝ)*x) + _*(_*((L.val:ℝ)*x)))
    have hx : 0≤x := norm_nonneg _; field_simp; nlinarith [mul_nonneg (mul_nonneg hx ha) ht.le, mul_nonneg (mul_nonneg hx ha) hu.le, mul_nonneg (mul_nonneg hx ha) hpos.le]
  case refine_3 => apply le_trans _ ((h₂ q p s z w i j l hq hp hs).trans_eq (mul_assoc ..).symm); rw [← mul_assoc,← mul_assoc]; gcongr; exacts [(inv_pos.mpr (he ..)).le,hv ..]
  case inr.refine_3 => apply le_trans _ ((h₂ q p s z w i j l hq hp hs).trans_eq (mul_assoc ..).symm); rw [← mul_assoc,← mul_assoc,mul_comm (5:ℝ) ((energy _ _ _)⁻¹),mul_assoc ((energy _ _ _)⁻¹) 5]; gcongr; exacts [(by have := he (-(q+p+s)) (-(i+(j+l))); positivity),hv ..]
end YM.Push.Loops.Block
