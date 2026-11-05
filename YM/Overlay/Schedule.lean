import YM.Overlay.Prior

/-!
# Stage viability for the two centered tabs

Explicitly proving only these (on the base history values). Not supplying
exponents for E & K, or census/coverage/winding estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stock
open Lattice Wilson RG RG.Supply Marker Cells MeasureTheory Filter Set Function Overlay Extraction Real Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal ContDiff
variable {G : Gauge} {C : Sheet G} {D : Rolls C} {P : Protection D} {W : Delays P}

def scaleB (x : ℝ) := Nat.ceil (Real.log x^2)

lemma stepsize (k : ℝ) : ∀ᶠ x in atTop, (scaleB (x+k))^2≤2*(scaleB x)^2 := by
  let a := fun x : ℝ => log (x+k) - log x
  have hz : Tendsto a atTop (𝓝 0) := Real.tendsto_log_comp_add_sub_log k
  have he := hz.eventually (lt_mem_nhds -- should >_
    (show (-1:ℝ)<0 by norm_num))
  filter_upwards [he,hz.eventually (gt_mem_nhds (zero_lt_one' ℝ)), Real.tendsto_log_atTop.eventually_ge_atTop 20] with x hx hh ht
  have h1 : -1< log (x+k)-log x := hx; have h2 : log (x+k)-log x<1 := hh
  have hi : (scaleB x:ℝ) ≥ log x^2 := Nat.le_ceil _
  have hJ : (scaleB (x+k):ℝ) ≤ log (x+k)^2+1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hg : (scaleB (x+k):ℝ) ≤ 5/4*(scaleB x:ℝ) := by
    have hL : log (x+k) ≤ log x+1 := by linarith
    have he := pow_le_pow_left₀ (show 0 ≤ log (x+k) by linarith) hL 2
    nlinarith
  exact_mod_cast (show ((scaleB (x+k):ℕ):ℝ)^2 ≤ 2*((scaleB x:ℕ):ℝ)^2 by nlinarith [pow_le_pow_left₀ (by positivity) hg 2])

private lemma restrained (a b : ℝ) (h : 0<b) (R : ℕ) : ∀ ε : ℝ, 0<ε → ∀ᶠ s : ℝ in atTop,
    (1+log (a+b*s))^R ≤ ε*s := by
  have hz : Tendsto (fun s : ℝ => a+b*s) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop h tendsto_id)
  have he : (fun x : ℝ => log (a+b*x)^R) =o[atTop] id :=
    (Real.isLittleO_pow_log_id_atTop.comp_tendsto hz).trans_isBigO ( (isLittleO_const_id_atTop (a:ℝ)).isBigO.add <|
      (isBigO_refl id _).const_mul_left b )
  have hh : (fun x : ℝ => 1+log (a+b*x)) =O[atTop] (fun x : ℝ => log (a+b*x)) :=
    ((Real.isLittleO_const_log_atTop (c:=1)).isBigO.comp_tendsto hz).add (isBigO_refl _ _)
  intro ε hε
  filter_upwards [((hh.pow R).trans_isLittleO he).def hε,eventually_ge_atTop (0:ℝ)] with i hi ha
  exact le_trans (Real.le_norm_self _) (hi.trans (by simp [abs_of_nonneg ha]))

lemma afford (L : ℕ) (γ : ℝ) (hG : G.Simple) (A : Stage) (o : ℝ) (ho : 0<o) (b : ℝ) :
    ∀ᶠ s : ℝ in atTop,
      let x := γ+G.slopeConstant*s
      (L*(scaleB x:ℝ)^2)^ (4:ℕ)*Vac.fiat G A (x+G.slopeConstant*b) ≤ o*(s+b) := by
  let ia := G.slopeConstant
  have ha : 0 < ia := Gauge.slopeConstant_pos hG
  let x := fun s => γ+ia*s
  let Gt := 2*(1+(4*A.paths+1))+1+(Fintype.card PlaqAxes:ℝ)*(A.clip.direct+A.paths^2)
  let f : ℝ := 4 *Module.finrank ℝ G.Mat
  let M := Gt+f*(log 16+1)+1 -- linear
  have h1 : 0 < Gt := by unfold Gt; have hv := A.paths_pos; have ha := A.clip.quadratic_pos; positivity
  have h2 : 0 ≤ f := by unfold f; positivity
  have h3 : 0 < M := by unfold M; positivity
  have hz : Tendsto x atTop atTop := tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop ha tendsto_id)
  let C : ℝ := 1+ L^ (4:ℕ) * M
  have hu : 0<C := by unfold C; positivity
  have he : ∀ᶠ s in atTop,x s > Real.exp 1 ∧ s > 2*|b| ∧ log (x s+ia*b)-log (x s) < 1 := by
    refine (hz.eventually (eventually_gt_atTop _)).and ((eventually_gt_atTop _).and ?_)
    exact ((Real.tendsto_log_comp_add_sub_log (ia*b)).comp hz).eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [he, restrained γ ia ha 17 (o/(2*C)) (by positivity)] with s hs hB
  obtain ⟨hs,hw,hH⟩ := hs
  change ( (L:ℝ)*(scaleB (x s):ℝ)^2)^4 * Vac.fiat G A (x s+ia*b) ≤ _
  have hx : 1 ≤ log (x s) := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hs.le
  let z := 1+log (x s)
  have hp : 1≤z := by unfold z; linarith
  have hb : (scaleB (x s):ℝ) ≤ z^ (2:ℕ) := by
    refine le_trans (Nat.ceil_lt_add_one (sq_nonneg _)).le ?_
    unfold z; linarith
  have he : Vac.fiat G A (x s+ia*b) ≤ M*z := by
    change Gt+f*(log 16+Real.log (x s+ia*b)/2) ≤ _
    have H := Real.log_pos (by norm_num : (1:ℝ)<16)
    unfold z M at *; nlinarith [mul_nonneg h2 (sub_nonneg.mpr hx)]
  calc
    _ ≤ ((L:ℝ)*(z^2)^2)^4 * (M*z) :=
      le_trans (mul_le_mul_of_nonneg_left he (by positivity))
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 2) (by positivity)) _) (by positivity))
    _ ≤ C*z^ (17:ℕ) := by
      apply le_trans (le_of_eq (show ((L:ℝ)*(z^2)^2)^4 * (M*z) = ((L:ℝ)^4*M)*z^17 by ring))
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
    _ ≤ C*(o/(2*C)*s) := mul_le_mul_of_nonneg_left hB hu.le
    _ ≤ _ := by
      rw [show C*(o/(2*C)*s)=(o/2)*s by field_simp]; nlinarith [neg_le_abs b]

def Priced (W : Delays P) := (∀ j, C.first ≤ j →
    ∀ x : ℝ, W.betaEntry j ≤ x → (scaleB (x+G.slopeConstant* Real.log (D.L j).val))^2≤2*(scaleB x)^2) ∧
    ∀ j, C.first < j → ∀ γ s : ℝ, 0≤s →  W.scaleEntry j γ ≤ s →
      ((D.L j).val * ((scaleB (γ+G.slopeConstant*s):ℝ)^2))^4 *
        Vac.fiat G (C.profile j) (γ+G.slopeConstant*s+G.slopeConstant*Real.log (D.L j).val) ≤
        (j:ℝ)⁻¹ * (s+Real.log (D.L j).val)

/-- after any provided lower gates, include both at each j. -/
lemma raises (W : Delays P) (hG : G.Simple) : ∃ W' : Delays P,
    W.betaEntry ≤ W'.betaEntry ∧ W.scaleEntry ≤ W'.scaleEntry ∧ W.shells=W'.shells ∧ W.growth=W'.growth ∧ Priced W' := by
  choose b hb using fun j : ℕ => eventually_atTop.1 (stepsize (G.slopeConstant*Real.log (D.L j).val))
  let o (j : ℕ) := ((j:ℝ)+1)⁻¹
  choose f hf using fun (j : ℕ) γ => eventually_atTop.1 (afford (D.L j).val γ hG (C.profile j) (o j) (by unfold o; positivity) (Real.log (D.L j).val))
  refine ⟨{ W with betaEntry := fun j => max (b j) (W.betaEntry j), scaleEntry := fun j γ => max (f j γ) (W.scaleEntry j γ) },
    (fun _ => le_max_right ..), (fun _ _ => le_max_right ..),rfl,rfl,?_,?_⟩
  · intro j _ i h; exact hb j i ((le_max_left ..).trans h)
  -- compare factor (s+b) sign require ≥0! impose for s≥0
  intro j hj γ s hs hb; refine (hf j γ s ((le_max_left ..).trans hb)).trans ?_
  have hp : 0 < (j:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hp (by simp)) (add_nonneg hs (Real.log_nonneg (by exact_mod_cast (show 1≤(D.L j).val from le_trans (by norm_num) (D.large j).size))))

theorem consumes {B : Bar W} {X : Wait B} {a : Levels G} (h : Paid X a) (hc : Priced W) : Tabs a := by
  have he (i : ℕ) : a.S.block i=D.L (a.clock.J (i+1)) := (a.fits.sameFactor i).symm.trans (congr_fun h.lengths _)
  have hi (i : ℕ) : a.clock.hatBeta (i+1) = a.clock.hatBeta i+G.slopeConstant* Real.log (a.S.block i).val := by
    unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold Levels.S; ring
  constructor
  · intro i
    have hx : C.first ≤ a.clock.J (i+1) := le_trans h.firstZero.symm.le (a.fits.mono (Nat.zero_le _))
    change scaleB _ ^ _ ≤ _*scaleB _ ^ _
    rw [hi,he]; exact hc.1 _ hx _ (h.pays i)
  intro ε hε
  have hb := a.fits.deep.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun i : ℕ => (a.clock.J (i+1):ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hb)
  filter_upwards [ht.eventually (ge_mem_nhds hε), hb.eventually (eventually_gt_atTop C.first)] with i hh h'
  change a.clock.J (i+1)>C.first at h'
  apply le_trans _ (mul_le_mul_of_nonneg_right hh (Shoot.scale_nn a (i+1)))
  rw [hi,Schedule.scale_succ]; unfold Calendar.coverSize Calendar.hatBeta Levels.params Calendar.params
  simp only [h.bar, h.stage,show a.clock.schedule=a.S from rfl]; rw [he]
  exact hc.2 _ h' _ _ (Shoot.scale_nn a i) (h.paysHigher i h')
end YM.Stock
