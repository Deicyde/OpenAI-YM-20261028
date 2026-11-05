import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Integrated

/-!
# Post-L room and hatted loop gates at every step of the one history
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Tree Bloch Bid Craft Input
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {P : Sheet G} {D : Rolls P} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}

abbrev meter := Vac.Numbers.P
lemma meter_pos (x : ℝ) : 0 < meter x := Real.exp_pos _
lemma meter_ge (x : ℝ) : 1 ≤ meter x := Real.one_le_exp (sq_nonneg _)
lemma meter_grows : Tendsto meter atTop atTop := Real.tendsto_exp_atTop.comp
  ((tendsto_pow_atTop (n:=2) (by decide)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))

lemma meter_ratio (a : ℝ) : Tendsto (fun x => meter (x+a) / meter x) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => (x+a)/x) atTop (𝓝 1) := by
    refine (show Tendsto (fun x : ℝ => 1+a/x) atTop (𝓝 1) from ?_).congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
    · simpa using Filter.Tendsto.const_add 1 ((tendsto_const_nhds (x:=a)).div_atTop tendsto_id)
    field_simp
  have he := (Work.E09.temp_ratio a).mul ((Real.continuous_sqrt.tendsto 1).comp h)
  rw [Real.sqrt_one,mul_one] at he
  refine he.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop (-a)] with x hx h'
  have hxa : 0<x+a := by linarith
  unfold temp meter Vac.Numbers.P; dsimp only [comp_apply]; rw [Real.sqrt_div hxa.le]; field_simp

lemma loop_ratio (a θ : ℝ) : Tendsto (fun x : ℝ => meter (x+a)^θ / meter x^θ) atTop (𝓝 1) := by
  have he := (meter_ratio a).rpow_const (p:=θ) (Or.inl one_ne_zero)
  simpa only [Real.one_rpow,Real.div_rpow (meter_pos _).le (meter_pos _).le] using he

structure Late (D : Rolls P) (Θ : Protection D) (Q : QuantumCosts) (j : ℕ) (x : ℝ) : Prop where
  fresh k : k ≤ j → j ≤ k+1 → Q.det j k * ((D.L j).val:ℝ)^4 ≤ meter x ^ Θ.theta k
  shifted k : k ≤ j → j ≤ k+1 → meter (betaF G x (D.L j)) ^ Θ.theta j ≤ 2 * meter x ^ Θ.theta k

lemma eventual_loop (D : Rolls P) (Θ : Protection D) (Q : QuantumCosts) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop, Late D Θ Q j x := by
  have he := (loop_ratio (G.slopeConstant * Real.log (D.L j).val) (Θ.theta j)).eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num))
  have hh := (tendsto_rpow_atTop (Θ.pos j)).comp meter_grows
  filter_upwards [he,hh.eventually_ge_atTop ((max (Q.det j j) (Q.det j (j-1)))*((D.L j).val:ℝ)^4)] with x hx hl
  have hy (k : ℕ) (hk : k ≤ j) : meter x ^ Θ.theta j ≤ meter x ^ Θ.theta k := Real.rpow_le_rpow_of_exponent_le (meter_ge _) (Θ.dec hk)
  constructor
  · intro k hk hs; refine le_trans ?_ (hl.trans (hy _ hk)); apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases (show k=j ∨ k=j-1 by omega) with rfl|rfl; exact le_max_left ..; exact le_max_right ..
  intro k hk _; exact ((div_le_iff₀ (Real.rpow_pos_of_pos (meter_pos _) _)).mp hx).trans (mul_le_mul_of_nonneg_left (hy _ hk) (by norm_num))

structure Warm {D : Rolls P} {Θ : Protection D} (Q : QuantumCosts) (W : Supply.Delays Θ) : Prop where
  volume j : 100*(j+7)*(D.L j).val ≤ W.shells j
  pay j x : W.betaEntry j ≤ x → Late D Θ Q j x

def warmup (Q : QuantumCosts) (V : Supply.Delays Θ) := (show Supply.Delays Θ from { V with
  shells := fun j => max (V.shells j) (100*(j+7)*(D.L j).val)
  betaEntry := fun j => max (V.betaEntry j) (eventually_atTop.mp (eventual_loop D Θ Q j)).choose })
lemma warmed (Q : QuantumCosts) (V : Supply.Delays Θ) : Warm Q (warmup Q V) := ⟨fun _ => le_max_right ..,
  fun j x hx => (eventually_atTop.mp (eventual_loop D Θ Q j)).choose_spec x ((le_max_right ..).trans hx)⟩
lemma Warm.boost {Q : QuantumCosts} (h : Warm Q W) {V : Supply.Delays Θ} (ht : W.betaEntry ≤ V.betaEntry)
    (he : W.shells ≤ V.shells) : Warm Q V := ⟨fun j => (h.volume j).trans (he j), fun j x hx => h.pay j x ((ht j).trans hx)⟩

section applies
variable {a : Levels G} {Q : QuantumCosts} (h : Warm Q W) (ha : Paid I a)
include ha
lemma block_eq (m : ℕ) : a.S.block m = D.L (a.clock.J (m+1)) := (a.fits.sameFactor m).symm.trans (congr_fun ha.lengths _)
omit ha in
lemma block_beta (m : ℕ) : a.clock.hatBeta (m+1) = betaF G (a.clock.hatBeta m) (a.S.block m) := by
  unfold betaF Calendar.hatBeta; rw [Schedule.scale_succ]; change _=_ + _*Real.log (a.clock.schedule.block m).val; ring

include h
lemma loop_ceiling (m : ℕ) :
    Q.det (a.clock.J (m+1)) (a.clock.J m) * ((a.S.block m).val:ℝ)^4 + a.clock.loopCap (m+1)/4 ≤ a.clock.loopCap m := by
  have ht := h.pay _ _ (ha.pays m)
  have hx := a.fits.stepSlow m; have hk := a.fits.mono (Nat.le_succ m)
  unfold Calendar.loopCap Calendar.monitor; rw [ha.theta, block_beta, block_eq ha]
  have h1 := ht.shifted _ hk hx; have h2 := ht.fresh _ hk hx; unfold meter Vac.Numbers.P at h1 h2; linarith
lemma larger (m p : ℕ) : Larger (G:=G) (a.clock.op m p) := by
  let S := a.clock.op m p
  have hv := ha.volume m p; let j := a.clock.J (m+1)
  have h1 : W.shells j ≤ (a.S.side m p).val := (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)).trans hv
  refine ⟨(a.blocks m p).branches, ?_, ?_⟩
  · have he : macroR S.patch = (j+7)*(a.S.block m).val := by change (j+3)*(a.S.block m).val+4*(a.S.block m).val= _; ring
    change 100 * macroR S.patch ≤ _
    rw [he,block_eq ha,← Nat.mul_assoc]; exact ((h.volume _).trans h1).trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.pos)
  have := a.fits.sizeT m p; omega
end applies

/-- Uniform for applications at this ratio including both output stage cases. -/
structure GapQuote (D : Rolls P) (K : MapPrices) (R : PostCost D) : Prop where
  serves (a : Levels G) (C : Horizon a) (N m p : ℕ) (j : ℕ) :
    let S := a.clock.op m p
    ∀ (_hj : j=a.clock.J (m+1)), (D.L j)=S.patch.L → S.kernel=P.kernel → Larger (G:=G) S → m<N → C.Suffices K →
      Sworn (C.H N (m+1)) (a.S.side (m+1) p) G → ∀ (W : PathData G) σ u Λ, W.Bounds (a.params (m+1)).clip σ u Λ →
      Attached (C.H N (m+1)) W → ∀ F : Forest S.ratio,
      PriceGap F (a.params (m+1)).clip W (R.η j) ∧ ∃ ρ, Critical F (a.params (m+1)).clip W ρ ∧
        Guessed F (installed S.ratio (C.towers N m).A0) ρ ∧ HeatG F (a.params (m+1)).clip W ρ (C.H N m)

theorem post (D : Rolls P) (K : MapPrices) (Γ γ g : ℕ → ℝ) (hΓ : ∀ j, 0 < Γ j) (hγ : ∀ j, 0 < γ j) (hg : ∀ j,0 < g j) :
    ∃ R : PostCost D, R.Γ=Γ ∧ R.c=γ ∧ R.g=g ∧ GapQuote D K R := by
  choose b hb H using fun j => (Integrated.stationary_scene (G:=G) (D.L j) j P.kernel (K.η j) (K.eta_pos j)).χ
  refine ⟨⟨b,Γ,γ,g,hb,hΓ,hγ,hg⟩,rfl,rfl,rfl,⟨?_⟩⟩
  intro a C N m p j S hj he ht hh hm h hu W σ u Λ hW hw F
  subst j
  exact H _ _ _ S ht he.symm rfl hh F (C.H N (m+1)) (C.H N m) _ (a.params m).clip W σ u Λ _ _ _ (C.towers N m)
    (h.crossings N m p hm) (h.all N (m+1) hm _) hW hw hu (h.all N m hm.le _)
end YM.Extra.Iteration
