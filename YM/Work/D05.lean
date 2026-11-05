import YM.Bid.Drops
import YM.OS.Halves


/-!
# D05

The centered estimate (use the power, not just `CenteredBook`) gives a
power budget on the *same* period-then-mesh tails (`late`) on which we
can compare with generic values of S. Use two scales, a cell scale m
for separation, and k with room to use centered estimates even from
uncentered points (`fits_budget`). Need to choose k **also** with a
power lower bound on its spacing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.D05
open Function Set Filter Cells Extraction
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {f : Order} {S : Table C.book} {n : ℕ}

private lemma one_le_inv_side (Q : Schedule) (m : ℕ) : 1 ≤ (Q.a m)⁻¹ :=
  (one_le_inv₀ (Q.a_pos m)).2 (by simpa only [Q.a_zero] using Q.strictAnti.antitone (Nat.zero_le m))

private lemma centered_power (h : CenterPort C f) (v : C.book.Token) :
    ∃ (M D : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ k ≥ M,
      f.late (centeredBudget C v (B * (C.S.a k)⁻¹ ^ D) k) := by
  rcases v with ⟨d,v⟩
  obtain ⟨M,hM,B,hB,E⟩ := h.cells.centered d 1 (‖v‖+1) (by norm_num) (by positivity)
  refine ⟨M,d+1,B+1,by positivity,fun k hk => ?_⟩
  refine (E k hk 1 (by norm_num)).mono fun i hi => hi.mono ?_
  rintro j ⟨hj, hroot⟩
  refine ⟨hj,hM.trans (hk.trans hj),fun o => ?_⟩
  obtain ⟨hg,he⟩ := hroot v (by simp) o
  refine ⟨hg,he.trans ?_⟩
  rw [show -(d:ℝ)-1 = -((↑(d+1 : ℕ)) : ℝ) by push_cast; ring,
    Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, add_mul, one_mul]
  exact add_le_add_right (one_le_pow₀ (one_le_inv_side C.S k)) _

/-- For a fixed tuple pay also for its copied orientations. B, D fixed
before the side choice; tails may depend on that side. -/
lemma image_power (h : CenterPort C f) (v : Fin n → C.book.Token) :
    ∃ (M D : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ k ≥ M,
      f.late (Around.imageBudget v (B * (C.S.a k)⁻¹ ^ D) k) := by
  classical
  let w (i : Fin n × Extraction.Spin.Frame) := Extraction.Spin.token C.book (v i.1) i.2
  choose m d b hb E using fun i => centered_power h (w i)
  obtain ⟨M,hM⟩ : ∃ M : ℕ, ∀ i, m i ≤ M :=
    (eventually_all.mpr fun i => eventually_ge_atTop (m i)).exists
  obtain ⟨D,hD⟩ : ∃ D : ℕ, ∀ i, d i ≤ D :=
    (eventually_all.mpr fun i => eventually_ge_atTop (d i)).exists
  obtain ⟨B,hB,hb'⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i, b i ≤ B :=
    ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun i => eventually_ge_atTop (b i))).exists
  refine ⟨M,D,B,hB,fun k hk => ?_⟩
  let A := B * (C.S.a k)⁻¹ ^ D
  have hr (i) : ∀ᶠ l in f.fuse, centeredBudget C (w i) A k l.1 l.2 := by
    rw [Order.fused]
    refine (E i k ((hM i).trans hk)).mono fun j hj => hj.mono fun t ht => fixup C ht ?_
    have ha := one_le_inv_side C.S k
    exact mul_le_mul (hb' i) (pow_le_pow_right₀ ha (hD i))
      (pow_nonneg (zero_le_one.trans ha) _) hB
  have hr' := Order.fused f _ |>.1 (eventually_all.mpr hr)
  have hs : ∀ᶠ j : ℕ in atTop, ∀ i, ∀ p, Around.Fit (w i) k (f.mesh j) p :=
    eventually_all.mpr fun i => Around.fit (w i) k
  refine hr'.mono fun j hj => ?_
  filter_upwards [hj, hs, f.mesh.cofinal.eventually (eventually_ge_atTop k)] with t ht H Hk
  exact ⟨Hk, fun i s => ⟨ht (i,s), H (i,s) _⟩⟩

private def separated (s : ℝ) (n : ℕ) : Set (Points n) :=
  {x | ∀ i j, i ≠ j → s < cubedist (x i) (x j)}

private lemma separated_open (s : ℝ) (n : ℕ) : IsOpen (separated s n) := by
  rw [show separated s n = ⋂ i : Fin n, ⋂ j : Fin n,
    ⋂ _ : i ≠ j, {x : Points n | s < cubedist (x i) (x j)} by ext; simp [separated]]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by unfold cubedist; fun_prop)

private lemma eventual_separation (Q : Schedule) (s : ℝ) (hs : 0 < s) (K : Set (Points n))
    (hK : IsCompact K) (hu : K ⊆ separated s n) :
    ∀ᶠ p in atTop, ∀ x∈K, Gaps.someFine Q p s x := by
  filter_upwards [Gaps.expand_equivalent Q hK] with p hp x hx i j hij
  obtain ⟨a,ha⟩ : ∃ a : Axis, s ≤ |Gaps.distances x i j a| := by
    by_contra! he
    have hl : cubedist (x i) (x j) < s := by
      unfold cubedist
      refine (dist_pi_lt_iff hs).mpr fun a => ?_
      rw [dist_comm, Real.dist_eq]
      exact he a
    exact hl.not_gt (hu hx i j hij)
  exact ⟨a,fun t => ha.trans (hp x hx i j a t)⟩

/-- Comparison at a point. All constants in the side budgets independent
of x. The period threshold to compare (and not wrap around x) needn't be. -/
private lemma separated_bound (H : C.Makes) (hS : S.Smooth) (he : f.PointLimits C S)
    (v : Fin n → C.book.Token) (s A : ℝ) (hs : 0 < s)
    (m k : ℕ) (hm : C.S.a m < s) (hmk : m ≤ k)
    (hk : (n:ℝ)*(2*(3*C.S.a k)) < C.S.a m)
    (hA : f.late (Around.imageBudget v A k)) :
    ∀ x∈separated s n, ‖S.read x v‖ ≤ A ^ n := by
  obtain ⟨P,hP,hv⟩ := he
  have hg (x : Points n) (hx : x∈separated s n) (he : x ∈ generic n) :
      ‖S.read x v‖ ≤ A ^ n := by
    have ht : Tendsto (fun i => (P (f.per i)).read x v) atTop (𝓝 (S.read x v)) := by
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      filter_upwards [hv n {x} (isCompact_singleton) (singleton_subset_iff.mpr he) v ε hε] with i hi
      rw [dist_eq_norm]
      exact hi x (mem_singleton x)
    obtain ⟨K,hK,hI,hU⟩ := exists_compact_subset (separated_open _ _) hx
    refine le_of_tendsto ht.norm ?_
    unfold Order.late at hA
    filter_upwards [hA, f.per.cofinal.eventually (eventual_separation C.S s hs K hK hU),
      f.per.cofinal.eventually (room C.S hK)] with i hi hb hw
    let u j := address (C.S.a (f.mesh j)) x
    have hr := (chosen (S := C.S) x).comp f.mesh.cofinal
    have hX : x ∈ Cyclic C.S (f.per i) n :=
      (no_wrap_tie C.S (hw (interior_subset hI))).2 he
    refine le_of_tendsto (f.evaluated C hP (f.per i) n v x hX u hr).norm ?_
    filter_upwards [hi, hr.eventually (mem_interior_iff_mem_nhds.mp hI)] with j hJ htag
    exact Around.fits_budget H v K s hb A hm hmk hk hJ (u j) htag
  intro x hx
  have hC : x∈conf n := spaced_conf hs fun i j hij => (hx i j hij).le
  have hc : ContinuousAt (fun y => S.read y v) x :=
    ((S.smooth_read hS v).continuousOn x hC).continuousAt ((conf_open n).mem_nhds hC)
  haveI : NeBot (𝓝[generic n] x) := mem_closure_iff_nhdsWithin_neBot.mp (Dash.full n x)
  refine le_of_tendsto (hc.norm.continuousWithinAt (s := generic n)).tendsto ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds ((separated_open s n).mem_nhds hx)] with y hy hY using hg y hY hy

/-- Tile with two scales, neither too fine (uniform power in the
requested separation). Keep M to enter the power-budget regime. -/
lemma scales (Q : Schedule) (h : Q.Gentle) (M n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ m k : ℕ,
      M ≤ k ∧ Q.a m < r/2 ∧ m ≤ k ∧ (n:ℝ)*(2*(3*Q.a k)) < Q.a m ∧
      c * r^4 ≤ Q.a k := by
  obtain ⟨c,hc,H⟩ := OS.thickness Q M h
  let b : ℝ := 6*((n:ℝ)+1)
  have hb : 1 ≤ b := by unfold b; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hb' : 0 < b := zero_lt_one.trans_le hb
  refine ⟨c * (c/(4*b))^2,by positivity,fun r hr ht => ?_⟩
  obtain ⟨m,hm⟩ := OS.turn Q M (r/2) (by positivity)
  have hw : c*(r/2)^2 ≤ Q.a m := H _ (by positivity) (by linarith) m hm
  let δ := Q.a m / b
  have hδ : 0 < δ := div_pos (Q.a_pos _) hb'
  obtain ⟨k,hk⟩ := OS.turn Q M δ hδ
  have hδ' : δ ≤ Q.a m := div_le_self (Q.a_pos _).le hb
  have hm' := hm.2.1
  have hk' := hk.2.1
  refine ⟨m,k,hk.1,hm',(Q.strictAnti.lt_iff_gt.mp (hk'.trans_le hδ')).le,?_,?_⟩
  · have hv : Q.a k*b < Q.a m := (lt_div_iff₀ hb').1 hk'
    unfold b at hv
    linarith [Q.a_pos k]
  calc
    c * (c/(4*b))^2 * r^4 = c * (c*(r/2)^2/b)^2 := by field_simp; ring
    _ ≤ c * δ^2 := by
      have hi : c*(r/2)^2/b ≤ δ := div_le_div_of_nonneg_right hw hb'.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) hc.le
    _ ≤ Q.a k := H δ hδ (by linarith) k hk

theorem answer : YM.Bid.D05 := by
  intro G C S f H h hS he n d v
  let w (i : Fin n) : C.book.Token := ⟨d i, v i⟩
  obtain ⟨M,D,B,hB,hf⟩ := image_power h w
  obtain ⟨c,hc,hu⟩ := scales C.S C.path.levels.fits.mesh M n
  refine ⟨4 * D * n,(B * c⁻¹ ^ D) ^ n,by positivity, fun r hr hR x hx => ?_⟩
  obtain ⟨m,k,hM,hm,hmk,hk,hw⟩ := hu r hr hR
  have hX : x ∈ separated (r/2) n :=
    fun i j hij => lt_of_lt_of_le (by linarith) (hx i j hij)
  have hi : (C.S.a k)⁻¹ ≤ c⁻¹ * (r⁻¹)^4 := calc
    _ ≤ (c*r^4)⁻¹ := inv_le_inv₀ (C.S.a_pos _) (by positivity) |>.2 hw
    _ = _ := by rw [mul_inv, inv_pow]
  change ‖S.read x w‖ ≤ _
  calc
    _ ≤ (B * (C.S.a k)⁻¹ ^ D)^n :=
      separated_bound H hS he w (r/2) _ (by positivity) m k hm hmk hk (hf k hM) x hX
    _ ≤ (B * (c⁻¹ * (r⁻¹)^4)^D)^n := by
      have ha := C.S.a_pos k
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi _) hB) _
    _ = _ := by simp only [mul_pow, pow_mul]; ring

end YM.Work.D05
