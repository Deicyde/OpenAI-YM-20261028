import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rope
/-!
 # Preprice on kernels and hours. Small doesn't depend C of Libretto.Predictor. big.Rust not C core constraints for null remainder where L purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Filter Function Lattice Wilson Pressure RG Tree Precision Next Next.Free Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory Extra.Iteration Extra.Iteration.Scales SelectedOrderedKernels.Sector
    AnalyticBridge.LocalGaussianLaws JointLoad JointLoad.Heir Lute
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {P B : BudgetPoint} {x u a A e t K : ℝ} {b n r p : ℕ} {C : Libretto G n} {D : Record}{X:Support f}
variable (Q:Rights G n) (b p r:ℕ)(M:ℝ)
variable (ht:0≤M)(hA:0<A)(he:0≤e)
-- realized.Shape proof at b=actual Valuation. Use with EARLY predictor fee if needed. Only uses Rights.M radial incidence. Demand Width acceptance equality.
include ht hA he
lemma gestureA : ∃ R:ℝ,1 ≤ R ∧ ∀ {c f:Side}(S : StepData c f) (C: Libretto G n) (D:Record) (P B:BudgetPoint)(X:Support f)(Y:Support c)(u x:ℝ), P.power=p → B.supportExponent=A → Release.accepts r A e S.patch.L → Walled S X Y x r → P.B=radiusB x → B.B ≤ 2*P.B → P.threshold ≤ 2*B.threshold → 0≤u → Rented b C D P B S.patch.L r x u → ∀ τ:ℝ,0≤τ → Real.exp (e*coverNumber P.B Y)*(τ * sale b Q C M D P B S.patch.L X r x u) ≤ R*((S.patch.L.val:ℝ)⁻¹)^(b+1) * B.mass X τ := by
  let j:= debited n p
  obtain ⟨R,hR,H⟩:= MultiNext.SignedSource.Newt.length_mom j (half_pos hA)
  let D:= Peak.poleSum b Q M; have hD:0≤D:=polepos b Q ht
  let Z:=Real.exp (Release.base e r)*(2*D*R); have hz:0≤Z:=by unfold Z; positivity
  refine ⟨1+Z,(by linarith),?_⟩; intro c f S C H' P B X Y u x hP hB hc hw hk hd hW hu hp τ hτ
  let a:=Real.exp (e*coverNumber P.B Y); let v:= Peak.sale b Q C M H' P B S.patch.L X r x u
  let z:=coverNumber B.B X; let g:= Real.exp (Release.base e r); let t:= Real.exp ((A/2)*z)
  have h:a≤g*t:=by
    unfold a g t; rw [← Real.exp_add]; apply Real.exp_monotone
    exact hB ▸ (Release.compressed (B:=B) he (hB.symm ▸ hc) hw hk hd)
  let m:= (S.patch.L.val:ℝ)⁻¹^(b+1)
  have hm:0≤ m:=by unfold m; positivity
  have hx : 0≤a:= (Real.exp_pos _).le
  have ht:= swirls (r:=r) M Q ht hu (show B.B ≤ 2*radiusB x from hk ▸ hd) hW hp (X:=X)
  rw [hP] at ht
  have hs : 0≤ t:=(Real.exp_pos _).le
  have hv:v≤(D*m)*(2*(t*R)):=ht.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (H _) zero_le_two) (mul_nonneg hD hm))
  have hr : g*t*(τ*(D*m*(2*(t*R)))) = Z*m * B.mass X τ:= by
    have he: Real.exp (B.supportExponent * coverNumber B.B X)=t*t:= by unfold t z; rw [hB,←Real.exp_add]; congr 1; ring
    unfold Z g BudgetPoint.mass; rw [he]; ring
  calc
    _ ≤ a*(τ * (D*m*(2*(t*R)))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hτ) hx
    _ ≤ _ := (mul_le_mul_of_nonneg_right h (show 0 ≤ (τ * (D*m*(2*(t*R)))) by positivity)).trans (hr.trans_le (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hm) (hτ.trans (B.loMass _ _ hτ))))
-- huge: use spare L exponent from s^3≥L and boost extra. NO invoking price only from Principal.L وتن
omit ht
variable (C)
lemma foggy : ∃ R:ℝ,1 ≤ R ∧ ∀ {c f:Side}(S : StepData c f) (D:Record) (P B:BudgetPoint)(X:Support f)(Y:Support c)(u x:ℝ), P.power=p → B.supportExponent=A → Release.accepts r A e S.patch.L → Walled S X Y x r → P.B=radiusB x → B.B ≤ 2*P.B → P.threshold ≤ 2*B.threshold → 0≤u → Plented C D P B S.patch.L r x u → ¬ Short S B X → ∀ τ:ℝ,0≤τ → Real.exp (e*coverNumber P.B Y)*(τ*Lute.returnFee C D P B S.patch.L X r x u) ≤ R*((S.patch.L.val:ℝ)⁻¹)^(b+1) * B.mass X τ:= by
  let j:=15+debited n p
  let J:=j+3*(b+1)
  obtain ⟨R,hR,H⟩:= MultiNext.SignedSource.Newt.length_mom J (half_pos hA)
  let c:= 2*beat C; have hD:0≤c:=mul_nonneg zero_le_two (beat_nn _)
  let Z:=Real.exp (Release.base e r)*(c*R); have hz:0≤Z:=by unfold Z; positivity
  refine ⟨1+Z,(by linarith),?_⟩; intro c' f S V P B X Y u x hp hb hc hY he' hv ht hu hP hS τ hτ
  let η := Heir.Release.base e r -- ambiguity
  let L:= (S.patch.L.val:ℝ); let B₁:= L⁻¹; let a:=Real.exp (e*coverNumber P.B Y); let v:=Lute.returnFee C V P B S.patch.L X r x u
  let z:=coverNumber B.B X; let g:=Real.exp η; let t:= Real.exp ((A/2)*z); have hL : 1 ≤ L:=by unfold L; exact_mod_cast S.patch.L.property
  have h:a≤g*t:=by unfold a g η t; rw [←Real.exp_add]; apply Real.exp_monotone; exact hb ▸ (Release.compressed (B:=B) he (hb.symm ▸ hc) hY he' hv)
  have hI:0<B₁:=by unfold B₁; positivity
  have hϑ:=Lute.issued (L:=S.patch.L) (B:=B) (X:=X) (show B.B≤2*radiusB x from he' ▸ hv) ht hu hP; rw [hp] at hϑ
  have ht: v ≤ c * B₁^(b+1)*(t*R):=by
     let y:=1+(z:ℝ); have hy:1≤y:=by simp [y]
     have hb' : B₁≤1:=inv_le_one_of_one_le₀ hL
     have hm: y^3*B₁≥1:=by
       have ht : (S.patch.L.val:ℕ) ≤ z^3:= Nat.le_of_not_gt hS
       unfold B₁; rw [← div_eq_mul_inv]; apply (one_le_div (by positivity)).mpr
       exact (Nat.cast_le.mpr ht).trans (by push_cast; gcongr; exact le_add_of_nonneg_left zero_le_one)
     apply hϑ.trans; change c*B₁^5*y^j ≤ _
     calc
       _ ≤ c*y^j:=by gcongr; exact mul_le_of_le_one_right hD (pow_le_one₀ hI.le hb')
       _ ≤ c*y^j*(y^3*B₁)^(b+1):= le_mul_of_one_le_right (by positivity) (one_le_pow₀ hm)
       _ = c*B₁^(b+1)*y^J:=by unfold J; rw [pow_add (n:=3*(b+1)) (m:=j),pow_mul,mul_pow]; ring
       _ ≤ _:=mul_le_mul_of_nonneg_left (H _) (by positivity)
  have hξ:0≤t:=(Real.exp_pos _).le; have hm := pow_pos hI (b+1)
  have hd : g*t*(τ*(c*B₁^(b+1)*(t*R)))=Z*B₁^(b+1)*B.mass X τ:=by
    have he: Real.exp (B.supportExponent * coverNumber B.B X)=t*t:= by unfold t z; rw [hb,←Real.exp_add]; congr 1; ring
    unfold Z g η BudgetPoint.mass; rw [he]; ring
  calc
    _ ≤ a*(τ*(c*B₁^(b+1)*(t*R))):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hτ) (Real.exp_pos _).le
    _ ≤ _:= (mul_le_mul_of_nonneg_right h (show 0 ≤ τ*(c*B₁^(b+1)*(t*R)) by positivity)).trans (hd.trans_le (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hm.le) (hτ.trans (B.loMass _ _ hτ))))
end YM.PhysicalNext.Repeat.Peak
