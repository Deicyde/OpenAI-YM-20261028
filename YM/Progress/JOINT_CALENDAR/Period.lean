import YM.Progress.JOINT_CALENDAR.Issue

/-!
# Further simultaneous period budget for applying finite-phase claims

Bills independent of actual periods; enough for example to absorb whole
polynomial volumes times e^{-c R/a_m} when actually having such an invoice.
Works with the very same Package.Levels by putting scaleEntry and minLength
requests at their statutory quantifier positions. Handles m=0.  (see also the other gates in Scheduling). Not an estimate of
the determinant for supplying the invoice itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open Filter Function RG RG.Supply Bid Precision Pressure Next Next.Scheduling Next.Scheduling.Weak Lattice
open scoped Topology BigOperators
variable {G : Gauge}

def Native := ℕ → ℝ → ℝ → ℝ

/-- `u j b s` = post-L bill in OUTPUT site units when coarse log scale=s,
β₀=b (the bar), fine smoothing index=j. Sufficient test; includes j
coarse as well as j-1 from using maxima. Earlier or later costs available
in the same way if THEN computable. No requiring arbitrary costs even
asymptotically proportional to the inverse spacing with coefficient growing
in j (cf. `fixed_period_obstacle`). -/
structure Doable (u : Native) : Prop where
  first j b : ContinuousOn (u j b) (Set.Ici 0)
  late j b : ∀ᶠ s in atTop, u j b s ≤ Real.exp s

def Cleared (a : Levels G) (u : Native) := ∀ m n : ℕ, u (a.clock.J (m+1)) a.clock.bar (a.S.scale m) ≤ (a.S.side m n).val



variable {p : Sheet G} {D : Rolls p} {Θ : Protection D}

def Over (u : Native) (V : Delays Θ) := ∀ j b s, V.scaleEntry j b ≤ s → u j b s ≤ Real.exp s

lemma Doable.prepare {u : Native} (h : Doable u) (V : Delays Θ) : ∃ W : Delays Θ, Boost V W ∧ Over u W := by
  choose z hz using fun j b => eventually_atTop.1 (h.late j b)
  exact ⟨{ V with scaleEntry := fun j b => max (V.scaleEntry j b) (z j b) },
    ⟨le_rfl,fun _ _ => le_max_left ..,le_rfl,le_rfl⟩,fun j b s h => hz j b s (le_trans (le_max_right ..) h)⟩

lemma Over.later {u} {V W : Delays Θ} (h : Over u V) (hB : Boost V W) : Over u W :=
    fun j b s he => h j b s ((hB.scale j b).trans he)

lemma Doable.reserve {u} (h : Doable u) (j : ℕ) (b : ℝ) : ∃ r : ℕ, ∀ s : ℝ, 0 ≤ s →
    u j b s ≤ r*Real.exp s := by
  obtain ⟨s₀,h₀⟩ := eventually_atTop.1 (h.late j b)
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image ((h.first j b).mono (Set.Icc_subset_Ici_self (a:=s₀)))
  obtain ⟨r,hr⟩ := exists_nat_ge B
  refine ⟨r+1,fun s hs => ?_⟩
  by_cases he : s₀ ≤ s
  · exact (h₀ s he).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (by exact_mod_cast Nat.le_add_left 1 r))
  exact (hB ⟨s, ⟨hs,le_of_not_ge he⟩,rfl⟩).trans <| hr.trans (by push_cast; nlinarith [Real.one_le_exp hs])

theorem Over.clear {s : Survey G} {q : Quote} {v} {D : Rolls (s.paper q v)} {Θ : Protection D} {u} (h : Doable u) {W : Delays Θ} (hg : Over u W) {Y : Bar W} (J : Wait Y) :
    ∃ I : Wait Y, Behind J I ∧ ∀ {K : Wait Y}, Behind I K → ∀ a : Levels G, Paid K a → Cleared a u := by
  obtain ⟨r,hr⟩ := h.reserve s.first Y.value
  let I : Wait Y := { J with minLength := max J.minLength r }
  refine ⟨I,⟨le_rfl,le_rfl,le_max_left ..⟩,fun hK a ha m n => ?_⟩
  have he : Real.exp (a.S.scale m) = (a.S.denominator m).val := by
    unfold Schedule.scale Schedule.a; rw [inv_inv,Real.exp_log (by positivity)]
  have hn : ((a.S.side m n).val:ℝ) = (a.S.period n).val * ((a.S.denominator m).val : ℝ) := by exact Nat.cast_mul ..
  have ht := a.fits.mono (show 0 ≤ m+1 by omega)
  rw [ha.bar,hn]
  rw [ha.firstZero] at ht; rcases ht.eq_or_lt with h|h
  · rw [← h]; have hh := hr _ (Shoot.scale_nn a m); rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ((le_max_right ..).trans (hK.psize.trans (ha.periods n)) : r ≤ _)) (by positivity))
  have hh := hg _ _ _ (ha.paysHigher m h); rw [he] at hh
  exact hh.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast (a.S.period n).property))

/-- Basic family, y = fine hatBeta during the step, independent of p,
polynomial of y even for huge post-L constants. -/
def native (D : Rolls p) (C : ℕ → ℝ) (d : ℕ → ℕ) : Native := fun j b s =>
    C j * (1+(b+G.slopeConstant*s + G.slopeConstant*Real.log (D.L j).val))^(d j)

lemma doable_native (D : Rolls p) (C : ℕ → ℝ) (d : ℕ → ℕ) : Doable (native D C d) := by
  refine ⟨fun j b => Continuous.continuousOn (by unfold native; fun_prop), fun j b => ?_⟩
  let g := G.slopeConstant
  have co (c : ℝ) := (Asymptotics.isLittleO_const_id_atTop c).isBigO
  have ho := ((co 1).add (((co b).add ((Asymptotics.isBigO_refl id atTop).const_mul_left g)).add (co (g*Real.log (D.L j).val))))
  have ht := (((ho.pow (d j)).const_mul_left (C j)).trans_isLittleO
    (isLittleO_pow_exp_pos_mul_atTop _ (by norm_num : (0:ℝ)<1))).def one_pos
  filter_upwards [ht] with x hx
  exact (Real.le_norm_self _).trans (show ‖native D C d j b x‖ ≤ Real.exp x by simpa only [native,id_eq,g,one_mul,Real.norm_of_nonneg (Real.exp_nonneg _)] using hx)

lemma native_price {C d} {D : Rolls p} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G}
    (h : Paid I a) (hU : Cleared a (native D C d)) (m n : ℕ) :
    let j := a.clock.J (m+1)
    C j*(1+a.clock.hatBeta (m+1))^(d j) ≤ (a.S.side m n).val := by
  intro j; have he : a.S.block m = D.L j := (a.fits.sameFactor _).symm.trans (congr_fun h.lengths _)
  rw [← Deployment.hat, he]; exact hU _ _

lemma cap_small (a : Levels G) (m : ℕ) : a.clock.loopCap m ≤ 2*a.clock.hatBeta m := by
  have he := a.fits.smallField m
  have hj : 1 ≤ (a.clock.J m:ℝ) := by have := a.clock.adm m; exact_mod_cast (show 1 ≤ a.clock.J m by omega)
  have ht : a.clock.theta (a.clock.J m) ≤ (1:ℝ) := (a.fits.thetaRange m).2.trans (inv_le_one_of_one_le₀ hj)
  have hx : 1 ≤ a.clock.monitor m := Real.one_le_exp (sq_nonneg _)
  let y := a.clock.hatBeta m
  have hp : 1 < y := a.fits.delayed m
  unfold Calendar.loopCap
  have hy := Real.rpow_le_rpow_of_exponent_le hx ht; rw [Real.rpow_one] at hy
  have hh : Real.sqrt y ≤ y := by nlinarith [Real.sq_sqrt (x:=y) (by positivity)]
  have hg : a.clock.monitor m ≤ Real.sqrt y := by
    have ht := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg y)
    change Real.sqrt y*( (Real.sqrt y)⁻¹*a.clock.monitor m) ≤ Real.sqrt y*1 at ht
    rwa [mul_inv_cancel_left₀ (Real.sqrt_pos.2 (by linarith)).ne', mul_one] at ht
  linarith

/-- Once-only purchases *after* L/post prices known to commoditize the
period error, including actual site card, BOTH transition prices where
already bounded in Q, etc. -/
structure Attenuated (Q : PostCost D) (a : Levels G) (rate : ℕ → ℝ) (t : ℕ → ℕ) : Prop where
  side m n :
    let j := a.clock.J (m+1); let c := a.S.side m n
    (Fintype.card (Site c):ℝ)*Q.Γ j * a.clock.loopCap (m+1)*Real.exp (-Q.c j*c.val) ≤
      Real.exp (-rate j * a.clock.hatBeta (m+1)^(t j)) * Real.exp (-(Q.c j/2)*c.val)

lemma Attenuated.offer (Q : PostCost D) (rate : ℕ → ℝ) (t : ℕ → ℕ) :
    ∃ u : Native, Doable u ∧ ∀ {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G},
      Paid I a → Cleared a u → Attenuated Q a rate t := by
  choose h hh using fun j => eventually_atTop.1 <| ((isLittleO_pow_exp_pos_mul_atTop 5
    (div_pos (Q.posC j) (by norm_num : (0:ℝ)<4))).const_mul_left (2*Q.Γ j)).def one_pos
  let v j := max (max 1 (h j)) (4*rate j/Q.c j)
  refine ⟨native D v (fun j => max 1 (t j)),doable_native ..,fun ha hU => ⟨fun m n => ?_⟩⟩
  intro j c
  rename_i _ _ _ _ a
  let r : ℝ := c.val; let y := a.clock.hatBeta (m+1); let d := max 1 (t j)
  have hy : 1 < y := a.fits.delayed _
  have hx : v j*(1+y)^d ≤ r := native_price ha hU m n
  have hv : 1 ≤ v j := le_max_of_le_left (le_max_left ..)
  have hp : (1+y) ≤ (1+y)^d := by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ (1+y:ℝ)) (le_max_left 1 (t j))
  have hz : 1+y ≤ r := (hp.trans (le_mul_of_one_le_left (by positivity) hv)).trans hx
  have hhr := hh j r ((le_max_of_le_left (le_max_right ..)).trans ((le_mul_of_one_le_right (by positivity : 0 ≤ v j)
    (one_le_pow₀ (by linarith : 1 ≤ 1+y))).trans hx))
  simp only [Real.norm_of_nonneg (Real.exp_nonneg _), one_mul] at hhr
  have ht : y^(t j) ≤ (1+y)^d := (pow_le_pow_left₀ (by positivity) (by linarith) _).trans <|
    pow_le_pow_right₀ (by linarith) (le_max_right ..)
  have hq := Q.posC j
  have he : rate j*y^(t j) ≤ Q.c j/4*r := by
    have h1 := mul_le_mul_of_nonneg_right (div_le_iff₀ hq |>.1 (show 4*rate j/Q.c j ≤ v j from le_max_right ..))
      (pow_nonneg (show 0 ≤ y by positivity) (t j))
    nlinarith [(mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ht (show 0 ≤ v j by linarith)).trans hx) hq.le)]
  have hal : (Fintype.card (Site c):ℝ)*Q.Γ j * a.clock.loopCap (m+1) ≤ Real.exp ((Q.c j/4)*r) := by
    rw [site_card]; push_cast
    calc
      _ ≤ r^4 * Q.Γ j*(2*y) := mul_le_mul_of_nonneg_left (cap_small ..) (by have := Q.pos j; positivity)
      _ ≤ 2*Q.Γ j*r^5 := by nlinarith [Q.pos j, mul_le_mul_of_nonneg_left (show y ≤ r by linarith) (show 0 ≤ r^4*Q.Γ j by have := Q.pos j; positivity)]
      _ ≤ _ := (Real.le_norm_self _).trans hhr
  apply le_trans (mul_le_mul_of_nonneg_right hal (Real.exp_nonneg _))
  rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  change _ + -Q.c j*r ≤ _ + -(Q.c j/2)*r; linarith
end YM.Progress.Joint
