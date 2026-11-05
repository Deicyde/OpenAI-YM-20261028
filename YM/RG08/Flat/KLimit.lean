import YM.RG08.UV.Costs
import YM.UVExtension.Free.Rows

/-!
# The formal UV rate for the actual free history

Stipulate the numerical admission, deliver change-of-cutoff bound and limit.
Use the `Received` API of the accepted baseline with **these independently
computed rows**. Add quantitative rate in the advertised strip itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice RG Exterior Precision Next.Free
open Laurent Bloch Work.F08 UVExtension.Free
open scoped Topology BigOperators

variable {K : KernelChoices}

/-- Demand table before any block lengths. A₀ budget indexed by the COARSE
    output J so this covers both neighbor cases with just one output width. -/
structure KPrices (K : KernelChoices) where
  b : ℕ→ℝ
  bill : ℕ→ℝ
  positive : ∀ i, 0 < b i
  solvent : ∀ i, 0 ≤ bill i
  loans (j : ℕ) (w : Train j) : 4 ≤ j →
    (hessian (pink K.penalty w)).strip (b j) (bill j)
  offers (j i : ℕ) (F : Flight j i) (s : List Axis) (hh : s.length ≤ j-2) :
    4 ≤ i → (advanceC F.L (F.duo K.penalty).A0 s).strip (b i) (bill i/(F.L.val:ℝ)^(1+s.length))

lemma k_prices (K : KernelChoices) : Nonempty (KPrices K) := by
  let k := K.penalty
  have hk : 0<k := K.penalty_pos
  have hp (i : ℕ) : ∃ σ C : ℝ, 0<σ ∧ 0≤C ∧
      (∀ w : Train i, 4 ≤ i →
        (hessian (pink k w)).strip σ C) ∧
        ∀ j : ℕ, ∀ F : Flight j i, ∀ s : List Axis, s.length ≤ j-2 →
          4 ≤ i → (advanceC F.L (F.duo k).A0 s).strip σ (C/(F.L.val:ℝ)^(1+s.length)) := by
    by_cases h : 4 ≤ i
    · obtain ⟨x,A,hx,hA,H⟩ := heart_banked k hk h (id : Train i → _)
      obtain ⟨y,B,hy,hB,Hb⟩ := ((secure_both k hk h h).1).honored h 1
      have hv : 4 ≤ i+1 := by omega
      obtain ⟨z,D,hz,hD,Hd⟩ := ((secure_both k hk hv h).1).honored hv 1
      obtain ⟨V,hV,HV⟩ := hessian_price x hx.le
      let b := min x (min y z); let a := max (V*A) (max B D)
      refine ⟨b,a,lt_min hx (lt_min hy hz), (mul_nonneg hV.le hA.le).trans (le_max_left ..),
        fun w _ => strip_mono (HV (pink k w) _ (H w).1) (min_le_left ..) (le_max_left ..),?_⟩
      intro j F s ht _
      have hg : j=i ∨ j=i+1 := by have h1 := F.mono; have h2 := F.narrow; omega
      rcases hg with h|h
      · subst j
        exact strip_mono (Hb F s ht) ((min_le_right ..).trans (min_le_left ..))
          (div_le_div_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (by positivity))
      subst j
      exact strip_mono (Hd F s ht) ((min_le_right ..).trans (min_le_right ..))
          (div_le_div_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (by positivity))
    exact ⟨1,0,one_pos,le_refl _,fun _ hi => (h hi).elim,fun _ _ _ _ hi => (h hi).elim⟩
  choose b B h1 h2 h3 h4 using hp
  exact ⟨⟨b,B,h1,h2,h3,fun j i => h4 i j⟩⟩

/-- Block decisions for these widths, not down-selection on a fixed block
    history. Can add more demands/length/cost gates in callers. -/
structure KGate (P : KPrices K) where
  w : ℕ→ℝ
  minimum : ℕ→ℕ
  small : ∀ i, w i ≤ P.b i
  pos : ∀ i, 0 < w i
  steps (i j : ℕ) (h : i=j ∨ i=j+1) (L : Side) : minimum i ≤ L.val →
    Odd L.val → KContraction L (w i) (w j) (P.bill j)

lemma prepare (P : KPrices K) (w : ℕ→ℝ) (hp : ∀ i, 0 < w i) (hs : ∀ i, w i ≤ P.b i) :
    ∃ g : KGate P, g.w=w := by
  choose f hf using fun i j : ℕ => large_contraction (w i) (w j) (P.bill j) (hp i) (hp j)
  refine ⟨⟨w,fun i => max (f i i) (f i (i-1)),hs,hp,?_⟩,rfl⟩
  intro i j he t hL ho
  apply hf i j t _ ho
  rcases he with h|h <;> subst i
  · exact (le_max_left ..).trans hL
  simp only [Nat.add_sub_cancel] at hL; exact (le_max_right ..).trans hL

variable {X : Chain} {P : KPrices X.kernel}

structure KAllowed (g : KGate P) (ℓ : ℕ) : Prop where
  paid i : ℓ ≤ i → g.minimum (X.J (i+1)) ≤ (X.S.block i).val
  order i : ℓ ≤ i → 5 ≤ X.J (i+1)

lemma k_strip (X : Chain) (P : KPrices X.kernel) (N m : ℕ) :
    (X.K₀ N m).strip (P.b (X.J m)) (P.bill (X.J m)) :=
  P.loans _ _ (X.adm _)

lemma az_strip (X : Chain) (P : KPrices X.kernel) (N m) (s : List Axis)
    (h : s.length ≤ X.J (m+1)-2) :
    (advanceC _ (X.A₀ N m) s).strip (P.b (X.J m))
      (P.bill (X.J m)/((X.S.block m).val:ℝ)^(1+s.length)) :=
  P.offers _ _ (X.flight N m) s h (X.adm _)

lemma k_step (g : KGate P) {N N' i ℓ : ℕ} (h : KAllowed g ℓ)
    (hn : i<N) (hn' : N ≤ N') (hl : ℓ ≤ i) {A : ℝ} (ha : 0≤A)
    (he : (minusRows (X.K₀ N (i+1)) (X.K₀ N' (i+1))).strip (g.w (X.J (i+1))) A) :
    (minusRows (X.K₀ N i) (X.K₀ N' i)).strip (g.w (X.J i))
      (A*gain X.S (1/2) i (i+1)) := by
  have ht (M : ℕ) (s : List Axis) (hp : s.length ≤ 3) := strip_mono
      (az_strip X P M i s (by have hh := h.order i hl; omega)) (g.small (X.J i)) le_rfl
  have hp := g.steps (X.J (i+1)) (X.J i)
    (by have h1 := X.slow i; have h2 := X.mono i; omega) (X.S.block i) (h.paid i hl) (X.S.block_odd _)
  rw [X.k_difference_step i N N' hn (hn.trans_le hn'), gain_succ_half,← mul_div_assoc,mul_one]
  refine hp _ _ ?_ (ht N') _ _ ha he (hessian_difference_zero (X.metric_whole ..)
    (X.metric_whole ..) ((X.metric_start ..).trans (X.metric_start ..).symm))
  simpa only [advanceC,List.length_nil,Nat.add_zero,pow_one] using ht N [] (by decide)

/-- First separate result keeps the exact fine-end cost. -/
theorem k_paid (g : KGate P) {N N' i ℓ : ℕ} (h : KAllowed g ℓ)
    (hi : i≤N) (hn : N ≤ N') (hl : ℓ ≤ i) :
    (X.K₀ N i-X.K₀ N' i).strip (g.w (X.J i)) ((P.bill (X.J N) + P.bill (X.J N)) * gain X.S (1/2) i N) := by
  change (minusRows _ _).strip _ _
  induction hi using Nat.decreasingInduction with
  | self => rw [gain_zero,mul_one]; exact strip_mono (strip_minus (k_strip X P _ N) (k_strip X P _ N)) (g.small _) le_rfl
  | of_succ m hm ih =>
    have hk := k_step g h hm hn hl (mul_nonneg (add_nonneg (P.solvent _) (P.solvent _)) (gain_pos ..).le)
        (ih (hl.trans (Nat.le_succ m)))
    apply strip_mono hk le_rfl
    rw [gain_trans X.S _ m (m+1) N]; apply le_of_eq; ring

/-- Charge the allowed window polynomial. K has no period or derivative
    limitation here; formal construction, not the rigidity theorem for Rep.eval.
    Constants before the schedule and entirely uniform in view and top. -/
theorem k_cauchy (A : ℝ) (ha : 0 ≤ A) (q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (X : Chain) (P : KPrices X.kernel) (g : KGate P) (Z : ℝ),
      0 ≤ Z → ∀ (ℓ k : ℕ), KAllowed g ℓ →
      (∀ i, ℓ ≤ i → P.bill (X.J i) ≤ A*age X.S Z k i^q) →
      ∀ (N N' i : ℕ), ℓ ≤ i → i≤N → N≤N' →
        (X.K₀ N i-X.K₀ N' i).strip (g.w (X.J i)) (D * age X.S Z k i^q * gain X.S (1/4) i N) := by
  obtain ⟨C,hC,H⟩ := gain_poly (1/2) (1/4) (by norm_num) q
  refine ⟨(A+A)*C,by positivity,fun X P g Z hz ℓ k h hp N N' i he hv hn => ?_⟩
  apply strip_mono (k_paid g h hv hn he) le_rfl
  have ht := hp N (he.trans hv)
  calc
    _ ≤ (A*age X.S Z k N^q + A*age X.S Z k N^q)*gain X.S (1/2) i N := by gcongr; exact (gain_pos ..).le
    _ = (A+A)*(age X.S Z k N^q*gain X.S (1/2) i N) := by ring
    _ ≤ (A+A)*(C*age X.S Z k i^q*gain X.S (1/4) i N) := by
      exact mul_le_mul_of_nonneg_left (H _ _ _ _ _ hz hv) (by positivity)
    _ = _ := by ring

lemma cauchy_row_rate {α β : Type} [Fintype α] [Fintype β]
    {X : ℕ → Row α β} {i : ℕ} (f : ℕ → ℝ) {b A : ℝ} (hb : 0 < b)
    (h : ∀ᶠ N in atTop, (X N).strip b A)
    (hp : ∀ N ≥ i, ∀ M ≥ N, (X N-X M).strip b (f N)) (ht : Tendsto f atTop (𝓝 0)) :
    ∃ Y, Received X Y b A ∧ ∀ N ≥ i, (X N-Y).strip b (f N) := by
  have he (x : α) (y : β) (z) : CauchySeq (fun i => X i x y z) := by
    refine Metric.cauchySeq_iff'.mpr ?_
    intro ε hE
    obtain ⟨k,hk,hk'⟩ := ((eventually_ge_atTop i).and (ht.eventually (gt_mem_nhds hE))).exists
    refine ⟨k,fun j hj => ?_⟩
    rw [dist_comm,dist_eq_norm_sub]; exact (le_trans (le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp (mul_nonneg hb.le (Nat.cast_nonneg _)))) (Push.AbsoluteSums.budget_single (hp k hk j hj x y) z)).trans_lt hk'
  choose V hV using fun x y z => cauchySeq_tendsto_of_complete (he x y z)
  have he : Tendsto X atTop (𝓝 V) := tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun y => hV i x y
  refine ⟨V,reported he h,fun N hN => inherits (tendsto_const_nhds.sub he) ?_⟩
  exact (eventually_ge_atTop _).mono (hp N hN)

theorem k_limit (A : ℝ) (ha : 0 ≤ A) (q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (X : Chain) (P : KPrices X.kernel) (g : KGate P)
      (Z : ℝ), 0 ≤ Z → ∀ ℓ k, KAllowed g ℓ →
      (∀ i, ℓ ≤ i → P.bill (X.J i) ≤ A*age X.S Z k i^q) →
      ∀ i ≥ ℓ, ∃ Y : KRow, Received (fun N => X.K₀ N i) Y (g.w (X.J i)) (A*age X.S Z k i^q) ∧
        ∀ N ≥ i, (X.K₀ N i-Y).strip (g.w (X.J i))
          (D*age X.S Z k i^q * (X.S.a N/X.S.a i) ^ (1/4:ℝ)) := by
  obtain ⟨D,hD,H⟩ := k_cauchy A ha q
  refine ⟨D,hD,fun X P g Z hz ℓ k h hp i hi => ?_⟩
  simp_rw [← gain_spacing]
  exact cauchy_row_rate _ (g.pos _) (.of_forall fun N => strip_mono (k_strip X P N i) (g.small _) (hp i hi))
    (fun N hu M hm => H _ _ _ Z hz ℓ k h hp _ _ _ hi hu hm)
    (by simpa using (tendsto_gain X.S (v:=1/4) (by norm_num) i).const_mul (D*age X.S Z k i^q))

end YM.RG08
