import YM.Extra.MULTISOURCE_BOUNDS.Delays

/-!
`rate` is Mix.width on protected markers and has explicit additional
N-to-stop losses on the others (which, for instance, can be used to allow
both contact selections and their exterior spectators without pretending that
a contact root repaints all widths). Only protected-marker claims are
lossless. All parameters fixed across periods; occupancy at EACH current
site, includes alternatives. Each surviving monomial estimated, no global
sum over marker positions in these radius estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG RG.Supply Source Wilson Overlay Marker Labels Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} (C : Family G) (m : ℕ) (t : Tariff)
abbrev year := C.path.levels.clock.J m
abbrev hat := C.path.levels.clock.hatBeta m
abbrev quote := fee t (year C (m+1)) (hat C (m+1))
abbrev jump := steep C.labels (C.path.levels.params (m+1)) (C.S.block m) t (year C (m+1)) (hat C (m+1))
abbrev scaleFee (d : ℕ) := quote C m t * (C.S.block m).val ^ d

theorem quote_ge : 1 ≤ quote C m t := one_le_mul_of_one_le_of_one_le (t.factor_ge _)
    (one_le_pow₀ (C.path.levels.fits.delayed _).le)
theorem jump_ge : 1 ≤ jump C m t := steep_ge _ _ _ _ (C.path.levels.fits.delayed _).le
theorem scaleFee_pos (d : ℕ) : 0 < scaleFee C m t d := mul_pos (zero_lt_one.trans_le (quote_ge ..))
    (pow_pos (by exact_mod_cast (C.S.block m).property) _)

theorem nearby (h : G.Simple) : hat C m ≤ hat C (m+1) := by
  unfold hat Calendar.hatBeta; rw [Schedule.scale_succ]; gcongr
  · exact (Gauge.slopeConstant_pos h).le
  exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (C.S.block m).property : 1 ≤ ((C.S.block m).val:ℝ)))

theorem admitted {d : ℕ} (H : C.Makes) (hm : C.ref d ≤ m) : d ≤ year C m := by
  have he := (H.stages d).1
  exact (by omega : d ≤ d+3).trans (he.trans (C.path.levels.fits.mono hm))

lemma width_change (H : G.Simple) {d : ℕ} (hd : d ≤ year C (m+1)) {r : ℝ} (hr : 0<r) :
    (quote C m t / (gHat C m)^4) * radius C d r m ≤ (radius C d r (m+1) / scaleFee C m t d)*jump C m t := by
  let k := strength C.labels d
  let i := year C (m+1)
  let L := ((C.S.block m).val:ℝ)
  let x := hat C m; let y := hat C (m+1)
  let a := col C m; let b := col C (m+1)
  have ha : 1 ≤ a := col_ge ..
  have hb : 0 < b := zero_lt_one.trans_le (col_ge ..)
  have hw : 0 < wallet C m := zero_lt_one.trans_le (wallet_ge ..)
  have hL : 1 ≤ L := by unfold L; exact_mod_cast (C.S.block m).property
  have hxy := nearby C m H
  have hx : 1 < x := C.path.levels.fits.delayed m
  have hy : 1 < y := hx.trans_le hxy
  have hg := gHat_pos C m
  have hyg : 0 < gHat C (m+1) := gHat_pos C (m+1)
  let B := quote C m t
  have hB : 0 < B := zero_lt_one.trans_le (quote_ge ..)
  have heq : (gHat C m)^4 = (x^2)⁻¹ := by
    change (Real.sqrt x)⁻¹^4 = _; rw [inv_pow,show Real.sqrt x ^4 = (Real.sqrt x ^2)^2 by ring, Real.sq_sqrt (by linarith)]
  have hpow : 1 ≤ (gHat C (m+1))^k * y^ceiling C.labels i := by
    have he : 1 ≤ gHat C (m+1) * y := by
      change 1 ≤ (Real.sqrt y)⁻¹ * y; rw [inv_mul_eq_div]; exact
        (one_le_div (Real.sqrt_pos.mpr (by linarith))).mpr (by nlinarith [Real.sq_sqrt (by linarith : 0≤y)])
    exact (one_le_pow₀ (n:=k) he).trans (by rw [mul_pow]; gcongr
                                            · exact hy.le
                                            exact Finset.le_sup (f:=strength C.labels) (mem_range.mpr (Nat.lt_succ_of_le hd)))
  have hratio : Mix.envelope C r (m+1)/Mix.envelope C r m = b^2/a := by
    change r*b*wallet C (m+1)/(r*a*wallet C m) = _
    rw [wallet, prod_range_succ]; change r*b*(wallet C m*b)/(r*a*wallet C m) = _
    field_simp
  have hc0 : 0 < Mix.envelope C r m := mul_pos (mul_pos hr (zero_lt_one.trans_le ha)) hw
  have hc1 : 0 < Mix.envelope C r (m+1) := mul_pos (mul_pos hr hb) (zero_lt_one.trans_le (wallet_ge ..))
  have hZ : 0 < B*L^d := scaleFee_pos ..
  have hf : 0 ≤ b^2/a := by positivity
  rw [heq,div_inv_eq_mul]; change B*x^2*((gHat C m)^k / Mix.envelope C r m) ≤
    ((gHat C (m+1))^k / Mix.envelope C r (m+1))/(B*L^d)*(jump C m t)
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ hZ,le_div_iff₀ hc1]
  calc
    _ = B^2*L^d*x^2*(gHat C m)^k*(Mix.envelope C r (m+1)/Mix.envelope C r m) := by ring
    _ = B^2*L^d*x^2*((gHat C m)^k*(b^2/a)) := by rw [hratio]; ring
    _ ≤ B^2*L^i*y^2*(1*b^2) := by
      gcongr
      · exact pow_le_one₀ (gHat_pos ..).le (gHat_le_one ..)
      exact div_le_self (by positivity) ha
    _ ≤ B^2*L^i*y^2*((gHat C (m+1))^k*y^ceiling C.labels i * b^2) := by gcongr
    _ = _ := by unfold jump steep; rw [pow_add]; dsimp [i,L,B,y,b,quote,col]; ring

variable {V : Type*} [DecidableEq V]

def overhead (N : ℕ) := ∏ j∈Ico m N, (jump C j t)^2

def rate (hot : Finset V) (D : V→ℕ) (r : V → ℝ) (N : ℕ) (v : V) :=
    if v∈hot then radius C (D v) (r v) m else radius C (D v) (r v) m / overhead C m t N

variable {C m t} {D : V→ℕ} {r : V→ℝ} {N : ℕ} (hot : Finset V)
theorem overhead_ge : 1 ≤ overhead C m t N := Finset.one_le_prod fun _ _ => one_le_pow₀ (jump_ge ..)

theorem rate_le {v : V} (hr : 0<r v) : rate C m t hot D r N v ≤ radius C (D v) (r v) m := by
  unfold rate; split
  · rfl
  exact div_le_self (width_pos C m hr _).le overhead_ge

theorem rate_pos {v : V} (hr : 0<r v) : 0 < rate C m t hot D r N v := by
  unfold rate; split
  next => exact width_pos _ _ hr _
  exact div_pos (width_pos _ _ hr _) (zero_lt_one.trans_le overhead_ge)

theorem switch (h : G.Simple) {v : V} (hd : D v ≤ year C (m+1)) (hr : 0<r v) (hm : m < N) :
    let W := fun m => rate C m t hot D r N v
    let u := W (m+1) / scaleFee C m t (D v)
    let K := quote C m t / gHat C m^4
    (v∈hot → K*W m ≤ u * jump C m t) ∧ (v∉hot → K*W m ≤ u / jump C m t) := by
  intro W u K
  have he := width_change C m t h hd hr
  let Z := jump C m t
  let M := overhead C (m+1) t N
  have hZ : 0 < Z := zero_lt_one.trans_le (jump_ge ..)
  have hM : 0 < M := zero_lt_one.trans_le overhead_ge
  have hp : overhead C m t N = Z^2*M := (Finset.mul_prod_erase _ (fun j => (jump C j t)^2) (mem_Ico.mpr ⟨le_rfl,hm⟩)).symm.trans
    (by unfold M overhead; rw [show Ico (m+1) N = _ from Nat.Ico_succ_left_eq_erase_Ico])
  unfold u W rate
  constructor <;> intro hh <;> simp only [hh,↓reduceIte,hp]
  · exact he
  refine le_trans (b:= (radius C (D v) (r v) (m+1)/scaleFee C m t (D v)*Z) / (Z^2*M)) ?_ ?_
  · rw [← mul_div_assoc]; gcongr
  change _ ≤ radius C (D v) (r v) (m+1) / M / scaleFee C m t (D v) / Z
  have hf := scaleFee_pos C m t (D v)
  apply le_of_eq; field_simp

end YM.Extra.Multi
