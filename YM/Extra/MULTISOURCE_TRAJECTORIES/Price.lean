import YM.Extra.MULTISOURCE_TRAJECTORIES.InitialService
/-!
# One sufficient schedule criterion at birth (no L or width changed here)

All-period bootstrapping via the true rooted top terms, not isolated estimates
reinterpreted as joint estimates. `InitialRoom` is an additional vacuum/price
request BEFORE retaining a C (not derived from mere C.Makes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Lattice Wilson Function Filter MeasureTheory Finset Overlay Mix Stock Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}
namespace Prices
variable (C : Family G)

def B (N : ℕ) := C.path.levels.clock.coverSize N
def g (N : ℕ) := C.path.levels.clock.hatCoupling N
def sites (N : ℕ) : ℝ := ((B C N+B C N+1:ℕ):ℝ)^4

theorem sites_hi (N : ℕ) : 1 ≤ sites C N := one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 (B C N+B C N))
lemma g_pos (N : ℕ) : 0 < g C N := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed N)))
lemma g_one (N : ℕ) : g C N ≤ 1 := by
  have he := C.path.levels.fits.delayed N
  apply inv_le_one_of_one_le₀
  exact Real.one_le_sqrt.mpr he.le
lemma g_le_threshold (h : C.Makes) (N p : ℕ) : g C N ≤ (C.path.rep N p N).p.threshold := by
  rw [(h.wilson.represents N p N le_rfl).vac]; exact le_mul_of_one_le_right (g_pos C N).le (Real.one_le_exp (sq_nonneg _))

private lemma grows (hG : G.Simple) : Tendsto C.path.levels.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma diverge (hG : G.Simple) : Tendsto (B C) atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((Filter.tendsto_pow_atTop (by decide)).comp (Real.tendsto_log_atTop.comp (grows C hG)))

lemma delay (hG : G.Simple) : Tendsto (fun i => sites C i * g C i^2) atTop (𝓝 0) := by
  let b := C.path.levels.clock.hatBeta
  have he : Tendsto (fun x => 5^4 * ((Real.log (b x))^8 / b x)) atTop (𝓝 0) := by simpa using
    ((Real.isLittleO_pow_log_id_atTop (n:=8)).tendsto_div_nhds_zero.comp (grows C hG)).const_mul ((5:ℝ)^4)
  refine squeeze_zero' (Eventually.of_forall fun x => mul_nonneg (zero_le_one.trans (sites_hi ..)) (sq_nonneg _)) ?_ he
  filter_upwards [(Real.tendsto_log_atTop.comp (grows C hG)).eventually_ge_atTop 1] with i hi
  change 1 ≤ Real.log (b i) at hi
  have hB : (B C i:ℝ) ≤ Real.log (b i)^2+1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hpos : 0 ≤ b i := (zero_lt_one.trans (C.path.levels.fits.delayed i)).le
  change sites C i * (Real.sqrt (b i))⁻¹ ^2 ≤ _
  rw [inv_pow, Real.sq_sqrt hpos,← div_eq_mul_inv,mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hpos
  unfold sites; push_cast
  calc
    _ ≤ (5 * Real.log (b i)^2)^4 := by gcongr; nlinarith
    _ = _ := by ring

lemma footprint_cost (d : ℕ) (hG : G.Simple) (hC : C.Makes) : ∀ᶠ N in atTop,∀ p,∀ {V : Type} (Q : Probes C V N p) (i : V),Q.d i=d →
    Q.footprint i ⊆ halo (B C N) {Q.place i} ∧ coverNumber (B C N) (Q.footprint i) ≤ 1 := by
  let r := (C.localSection d).stencil.sup fun x => univ.sup (fun a : Axis => (x a).natAbs)
  have hr {x} (hx : x∈(C.localSection d).stencil) (a : Axis) : (x a).natAbs ≤ r := (le_sup (s:=univ)
    (f:=fun a => (x a).natAbs) (mem_univ a)).trans (le_sup (f:=fun x => univ.sup (fun a => (x a).natAbs)) hx)
  filter_upwards [(diverge C hG).eventually_ge_atTop r] with N hN p V Q i h
  have he : Q.footprint i ⊆ halo (B C N) {Q.place i} := by
    rw [Q.footprint_eq hC i,h]
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩
    rw [separation_comm,separation,add_sub_cancel_right]
    exact Finset.sup_le fun a _ => (Corona.lap y a).trans ((hr hy a).trans hN)
  refine ⟨he,(Corona.list_cost (D:={Q.place i}) _ ⟨he,Corona.ship_halo _ (fun i hi j hj => ?_)⟩).trans_eq (by simp)⟩
  rw [mem_singleton.mp hi,mem_singleton.mp hj]

private lemma rescale (k l d : ℕ) (φ t g a e w D v : ℝ) (hk : l+d+2 ≤ k) (he : 0 < e) (ha : 0 < a) (hg : 0 < g) (h1 : g ≤ 1)
    (ht : g ≤ t) (hD : 0 ≤ D) (hv : 0 ≤ v) (hφ : 0 ≤ φ) (hf : φ*g^l ≤ 1) (hw : w = g^k/(a*e)) :
    (w*(D*v*e*t⁻¹^d))*φ ≤ D*v/a * g^2 := by
  have hg0 := pow_ne_zero d hg.ne'
  have hh := inv_anti₀ hg ht
  calc
    _ = ((g^k * t⁻¹^d)*φ)*(D*v/a) := by rw [hw]; field_simp
    _ ≤ ((g^(l+2+d)*g⁻¹^d)*φ)*(D*v/a) := by
      have hpos := hg.trans_le ht; gcongr ((?_ * ?_) * _) * _
      · exact pow_le_pow_of_le_one hg.le h1 (by omega)
      exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hh d
    _ = ((φ*g^l)*g^2)*(D*v/a) := by simp only [pow_add,inv_pow]; field_simp
    _ ≤ _ := by rw [mul_comm (D*v/a)]; gcongr; exact mul_le_of_le_one_left (sq_nonneg _) hf

lemma exp_budget {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : k ≤ 1) : Real.exp (a*(k:ℝ)) ≤ Real.exp a :=
    Real.exp_monotone (mul_le_of_le_one_right ha (by exact_mod_cast hk))

def capital (i : ℕ) := (Real.log 2/2) / sites C i

lemma capital_rules (i : ℕ) : 0 < capital C i ∧ Real.exp (capital C i+capital C i)-1 ≤ 1 ∧
    sites C i*(capital C i+capital C i) ≤ 1 := by
  have he := Real.log_pos (by norm_num : 1 < (2:ℝ))
  have h₂ := sites_hi C i
  have h₁ := zero_lt_one.trans_le h₂
  have hh : capital C i+capital C i = Real.log 2 / sites C i := by unfold capital; ring
  rw [hh]; exact ⟨div_pos (half_pos he) h₁,by linarith [(Real.exp_monotone (div_le_self he.le h₂)).trans_eq (Real.exp_log (show (0:ℝ)<2 by norm_num))],by
    rw [mul_div_cancel₀ _ h₁.ne']; linarith [Real.log_le_sub_one_of_pos (x:=2) (by norm_num)]⟩

/-- Uniform in centers, provided at each p the same C offers the reserved old
K hit estimates and exponent. No changes of vacuum to achieve this ticket. -/
def InitialRoom (l : ℕ) := ∀ᶠ N in atTop, ∀ p,
  let X := C.path.rep N p N
  Aperture X ∧ Real.exp (X.p.supportExponent+1)*g C N^l ≤ 1 ∧ ∃ K : ℕ→ℝ, (∀ i U, ‖X.activities.K i U‖ ≤ K i) ∧
      Ac.Hit (fun i => (X.activities.forced i).support) (B C N) K (X.p.supportExponent+1) (capital C N)

private lemma single_hit {V : Type*} [Fintype V] {n : Side} (b : ℕ) (X : V → Support n) (f : V → ℝ) (a u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ i j,i ≠ j → Disjoint (X i) (X j)) (hf : ∀ i,0 ≤ f i) (he : ∀ i,f i * Real.exp (a*coverNumber b (X i)) ≤ u) : Ac.Hit X b f a u := by
  intro x
  refine ⟨fun i => by dsimp only; split; exact mul_nonneg (hf _) (Real.exp_pos _).le; rfl, Summable.of_finite,?_⟩
  rw [tsum_fintype]; by_cases hh : ∃ i,x∈X i
  · obtain ⟨i,hi⟩ := hh; rw [sum_eq_single i,if_pos hi]; exact he _
    · intro j _ hj; exact if_neg (Finset.disjoint_left.mp (hs i j hj.symm) hi)
    simp
  push Not at hh; simpa [hh]

lemma initial_expenses (h : C.Makes) (hG : G.Simple) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u)
    {d k l : ℕ} (hk : l+degree C d+2 ≤ k) (hR : InitialRoom C l) : ∀ᶠ N in atTop, ∀ p,
    Aperture (C.path.rep N p N) ∧ ∀ m i (hN : m ≤ N), i ≤ N → ticket C 1 N p m i hN → ∀ v : C.label d, ‖v‖ ≤ u →
      ∀ W : Windows (C.side N p), ((Probes.center C p hN v).layers (Stock.census _) W).Expenses (width C a k N) := by
  obtain ⟨K,hK,hf⟩ := fraction_global C d
  let J := changes C d * Real.exp 1
  have hJ : 0 ≤ J := mul_nonneg (changes_nn ..) (Real.exp_pos _).le
  have hz (D : ℝ) : ∀ᶠ i in atTop,D*u/a*g C i^2 ≤ capital C i := by
    have hh : Tendsto (fun i => D*u/a*(sites C i*g C i^2)) atTop (𝓝 0) := by simpa using (delay C hG).const_mul (D*u/a)
    filter_upwards [hh.eventually_le_const (half_pos (Real.log_pos (show (1:ℝ)<2 by norm_num)))] with i hi
    apply (le_div_iff₀ (zero_lt_one.trans_le (sites_hi ..))).mpr
    convert hi using 1; ring
  filter_upwards [hR,hz K,hz J, (diverge C hG).eventually_ge_atTop 8, eventually_ge_atTop (C.ref d), footprint_cost C d hG h]
    with N hN hK' hJ' h8 hd hfoot p
  obtain ⟨ho,hs,q,hq,hH⟩ := hN p
  let t := (C.path.rep N p N).p
  let w := width C a k N; let e := envelope C 1 N
  have hB : t.B = B C N := by unfold t; rw [(h.wilson.represents N p N le_rfl).vac]; rfl
  have hw : w = g C N^k/(a*e) := by unfold w width e g envelope; ring_nf
  have he := envelope_pos C zero_lt_one N
  have hp := g_pos C N
  have hw' : 0 < w := by rw [hw]; unfold e; positivity
  have hx (r : ℕ) (hr : r ≤ degree C d) (D : ℝ) (hD : 0 ≤ D) (φ : ℝ) (hφ : 0 ≤ φ) (h₁ : φ ≤ Real.exp (t.supportExponent+1)) :
      w * (D*u*e*t.threshold⁻¹^r)*φ ≤ D*u/a*g C N^2 := rescale k l r _ _ _ _ _ w D u (by omega) he ha hp (g_one ..) (g_le_threshold C h N p)
        hD hu hφ ((mul_le_mul_of_nonneg_right h₁ (pow_nonneg hp.le _)).trans hs) hw
  obtain ⟨hpos,hee,hcoin⟩ := capital_rules C N
  refine ⟨ho,fun m i hN hi ht v hv W => ?_⟩
  let Q := Probes.center C p hN v
  have hb (i : Site (C.side m p)) := hfoot p Q i (show Q.d i = d from rfl)
  have hsep {i j : Site (C.side m p)} (hij : i≠j) : B C N*B C N ≤ separation (Q.place i) (Q.place j) := by
    have HH := ht.2.2 N hi le_rfl i j hij
    rw [Probes.center_place C p hN v i,Probes.center_place C p hN v j]
    unfold B
    simp only [pow_two,mul_one] at HH; exact_mod_cast HH
  refine Q.primary_expenses (Stock.census _) W (fun _ => K*u*e * t.threshold⁻¹^(degree C d)) (fun _ => J*u*e) q
    (fun _ => mul_nonneg (mul_nonneg hJ hu) he.le) ?_ ?_ hq hw' hpos.le hee
      (by change ((t.B+t.B+1:ℕ):ℝ)^4*_ ≤ 1; rw [hB]; exact hcoin) ?_ (by simpa only [← hB] using hH) ?_
  · intro j
    have hg := Q.fraction_budget h j hd
    obtain ⟨f,hf,hh,hV⟩ := hg
    exact ⟨f,hf,hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hJ) he.le),hV⟩
  · intro j U
    apply (hf Q h j le_rfl hd U).trans
    have h0 := t.threshold_pos
    change K*‖v‖*envelope C 1 N*(t.threshold⁻¹^(degree C d)) ≤ K*u*envelope C 1 N*(t.threshold⁻¹^(degree C d)); gcongr
  · intro j
    have hcap := hx 0 (Nat.zero_le _) J hJ _ (Real.exp_pos _).le ((exp_budget t.exponent_pos.le (hB.symm ▸ (hb j).2)).trans (Real.exp_monotone (le_add_of_nonneg_right zero_le_one)))
    have hcap' : capital C N ≤ 1 := (le_add_of_nonneg_right hpos.le).trans ((le_mul_of_one_le_left (by linarith : 0≤capital C N+capital C N) (sites_hi ..)).trans hcoin)
    apply le_trans _ (hcap.trans (hJ'.trans hcap')); unfold loaf; simp [pow_zero,t,w]; apply le_of_eq; ring
  · rw [hB]; apply single_hit _ _ _ _ _ hpos.le (fun i j hij => ?_) (fun j => ?_) (fun j => ?_)
    · refine disjoint_left.mpr fun x hx hy => ?_
      obtain ⟨_,hx,hx'⟩ := halo_spec.mp ((hb i).1 hx); obtain rfl := mem_singleton.mp hx
      obtain ⟨_,hy,hy'⟩ := halo_spec.mp ((hb j).1 hy); obtain rfl := mem_singleton.mp hy
      rw [separation_comm] at hy'
      have HH := (hsep hij).trans (separation_triangle (Q.place i) x (Q.place j))
      nlinarith only [hx',hy',HH,h8]
    · have := t.threshold_pos; change 0 ≤ w*(K*u*envelope C 1 N* _); positivity
    exact (hx _ le_rfl _ hK _ (Real.exp_pos _).le (exp_budget (by have := t.exponent_pos; positivity) (hb _).2)).trans hK'
end Prices
end YM.Extra.Trajectories
