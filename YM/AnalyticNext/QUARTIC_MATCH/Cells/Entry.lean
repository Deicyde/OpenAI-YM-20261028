import YM.AnalyticNext.QUARTIC_MATCH.Cells.Detect

/-!
# Universal entry extraction

Every bill is per translation (anchored one argument, may project root first).
`Weave.enough` doesn't require ANY upper bound on repeats to enter. Smaller
pointwise estimates can be earned on the schedule itself and transfer to TRUE
universal arrays if constructed at a fixed, possibly worse, rate on auxiliaries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Finset Topology Laurent Filter Sheets
open scoped Topology BigOperators ContDiff

variable {V : Type} [NormedAddCommGroup V] {I : Type} [Fintype I] (i : I) {σ C : ℝ}

abbrev Bills (I V : Type) := (c : Side) → ArrayC I (Per c) V

/-- Don't require evidence at smaller/coarser sides not covered by actual definitions. -/
structure Weave (L : ℕ) (F : Bills I V) : Prop where
  same {c : Side} : L ≤ c.val → Cohere (F c)
  periods (c d : Side) : L ≤ c.val → L ≤ d.val → ∀ h : c.val∣d.val, ∀ X : I → Cell ℤ,
    F c (tor c ∘ X) = ∑' w : ↥(upperDeck i h), F d (sway w.val (tor d ∘ X))

/-- Literal finite positions. Can use the lift even on antipodal ties. -/
structure Spatial {c : Side} (F : ArrayC I (Per c) V) (σ C : ℝ) : Prop where
  rate : 0 < σ
  cap : 0 ≤ C
  low (X : I → Cell (Per c)) (i j : I) :
    ‖F X‖ ≤ C * Real.exp (-σ*size (lift ((X i).1-(X j).1)))

lemma Spatial.real {d : Side} {F : ArrayC I (Per d) V} (h : Spatial F σ C) (X : I → Cell ℤ)
    {Y : I → Cell (Per d)} (_e : Y=tor d ∘ X)
    (hy : ∀ j, lift ((Y j).1-(Y i).1)=(X j).1-(X i).1) :
    ‖F Y‖ ≤ C * Real.exp (-shiftRate I σ * loads (fun j => (X j).1-(X i).1)) := by
  classical
  haveI : Nonempty I := ⟨i⟩
  let f j := size ((X j).1-(X i).1)
  obtain ⟨j,hj,hb⟩ := Finset.exists_max_image Finset.univ f univ_nonempty
  have hz := h.low Y j i; rw [hy] at hz; apply hz.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap
  have hm : ∑ i : I, f i ≤ Fintype.card I * f j := by
    convert! Finset.sum_le_sum (s:=Finset.univ) (fun i h => hb i h) using 1; simp
  change -σ*(f j:ℝ) ≤ -(σ/(Fintype.card I:ℝ))* ↑(∑ x,f x)
  have hg : ((∑ x,f x):ℝ) ≤ Fintype.card I*(f j:ℝ) := by exact_mod_cast hm
  have hf := div_mul_cancel₀ σ (show (Fintype.card I:ℝ)≠0 by positivity)
  rw [show -σ*↑(f j)= -(σ/(Fintype.card I:ℝ))*(Fintype.card I*(f j:ℝ)) by rw [← mul_assoc,neg_mul (σ/↑(Fintype.card I)),hf]]
  rw [Nat.cast_sum]; exact mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr (positive_rate h.rate i).le)

variable {L : ℕ} {F : Bills I V} {n : ℕ → Side}
section coordinates

variable {A : ArrayC I ℤ V}

omit [Fintype I] in
lemma rates (hn : Tendsto (fun i => (n i).val) atTop atTop) (hF : ∀ᶠ m in atTop, Spatial (F (n m)) σ C)
    (he : ∀ X : I→Cell ℤ, Tendsto (fun j => F (n j) (tor (n j) ∘ X)) atTop (𝓝 (A X))) (hh : Cohere A) :
    Pricing A σ C := by
  obtain ⟨m,hm⟩ := hF.exists
  refine ⟨hh,hm.rate,hm.cap,fun X i j => ?_⟩
  apply le_of_tendsto ((he X).norm)
  filter_upwards [hF, Next.Free.eventually_unfold n hn ((X i).1-(X j).1)] with m hm hy
  have hw (k : I) : (tor (n m) ∘ X) k=tor _ _ := rfl
  have H := hm.low (tor (n m) ∘ X) i j
  simp only [Function.comp_apply, tor, ← map_sub, hy] at H
  exact H

omit [Fintype I] in
lemma Weave.unrolled (h : Weave i L F) (X : I → Cell ℤ) {c d : Side} (hc : L≤c.val) (hd : L≤d.val) (he : c.val∣d.val) :
    F c (tor c ∘ X) = ∑' w : ↥(sheets c i), ({w : sheets c i | short i c d X w}: Set _).indicator
      (fun w : sheets c i => F d (tor d ∘ sway w.val X)) w := by
  classical
  rw [← tsum_subtype (s:={w|short i c d X w}), h.periods c d hc hd he X]
  change _ = ∑' x : {v : sheets c i // short i c d X v}, F d (tor d ∘ sway x.val.val X)
  rw [← Equiv.tsum_eq (signpost i he X)
    (fun w : {w : sheets c i // short i c d X w} => F d (tor d ∘ sway w.val.val X))]
  apply tsum_congr; intro w; congr 1
  funext j; change _=tor d (move _ (X j)); rw [tor_move, show wrap d ((signpost i he X w).val.val j)=w.val j from ones i he X w j]
  rfl

variable [CompleteSpace V]

/-- Uniformity here can depend on the step, not on the tested period upstairs. -/
lemma Weave.limit (h : Weave i L F) (hn : Tendsto (fun i => (n i).val) atTop atTop) (hp : Pricing A σ C)
    (hF : ∀ᶠ m in atTop, Spatial (F (n m)) σ C)
    (he : ∀ X : I→Cell ℤ, Tendsto (fun j => F (n j) (tor (n j) ∘ X)) atTop (𝓝 (A X)))
    (c : Side) (hc : L≤c.val) (ht : ∀ᶠ m in atTop, c.val∣(n m).val) (Y : I→Cell (Per c)) :
    F c Y = scene c i A Y := by
  classical
  let X := rise c ∘ Y
  let D j w := ({w:sheets c i| short i c (n j) X w} : Set _).indicator
    (fun w : sheets c i => F (n j) (tor _ ∘ sway w.val X)) w
  have hD : (fun j => ∑' w : sheets c i,D j w) =ᶠ[atTop] fun _ => F c Y := by
    filter_upwards [ht,hn.eventually (eventually_ge_atTop L)] with j hj hy
    have hx : Y=tor c ∘ X := funext fun i => (to_ground ..).symm
    exact (h.unrolled i X hc hy hj).symm.trans (congr_arg (F c) hx.symm)
  let B (w : sheets c i) := C * Real.exp (-shiftRate I σ * loads (distanceL i X w))
  have hb : Summable B :=
    ((pays_all (I:=I) (positive_rate hp.rate i)).2.1.mul_left C).comp_injective (distanceI i X)
  have hx (w : ↥(sheets c i)) : ∀ᶠ j : ℕ in atTop, short i c (n j) X w :=
    eventually_all.mpr (fun j : I => Next.Free.eventually_unfold n hn (distanceL i X w j))
  have hw (w : sheets c i) : Tendsto (fun j => D j w) atTop (𝓝 (A (sway w.val X))) := by
    refine (he _).congr' ?_; filter_upwards [hx w] with j hj
    unfold D; rw [Set.indicator_of_mem hj]
  have hW : ∀ᶠ m in atTop, ∀ w, ‖D m w‖ ≤ B w := by
    filter_upwards [hF] with m hm w
    unfold D; by_cases hy : short i c (n m) X w
    · rw [Set.indicator_of_mem hy]
      have he (j : I) := hy j
      unfold B; rw [show distanceL i X w=(fun j => (sway w.val X j).1-(sway w.val X i).1) by
        ext1 j; rw [distanceS i]]
      apply hm.real i _ rfl ?_
      intro j; simp only [Function.comp_apply,tor, ← map_sub, distanceS i, he]
    rw [Set.indicator_of_notMem hy,norm_zero]; exact mul_nonneg hp.cap (Real.exp_pos _).le
  exact tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds (tendsto_tsum_of_dominated_convergence hb hw hW) hD.symm
end coordinates

section extraction
variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Make a sampling *device*, internal to the finite coefficient proof. No
assumptions on or claims about coincidence with any continuum extraction. -/
private def march (L m : ℕ) : Side := ⟨Nat.factorial (m+L+1), Nat.factorial_pos _⟩
private lemma march_le (L m : ℕ) : m+L+1 ≤ (march L m).val := by
  unfold march; dsimp; rw [Nat.factorial_succ]
  exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
private lemma march_out : Tendsto (fun m => (march L m).val) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id; intro m; exact Nat.le_trans (by change m ≤ m+L+1; omega) (march_le ..)
private lemma march_dvd (L : ℕ) (c : Side) : ∀ᶠ m in atTop, c.val∣(march L m).val := by
  filter_upwards [eventually_ge_atTop c.val] with m hm; exact Nat.dvd_factorial c.property (by omega)

theorem Weave.enough (h : Weave i L F) (hk : ∀ (c : Side), L ≤ c.val → Spatial (F c) σ C) :
    ∃ A, Pricing A σ C ∧ ∀ (c : Side), L≤c.val → F c=scene c i A := by
  let n m := march L m
  have hc (m : ℕ) : L≤(n m).val := (by omega : L≤m+L+1) |>.trans (march_le ..)
  have ht m := hk (n m) (hc m)
  have hx m X : F (n m) X ∈ Metric.closedBall (0:V) C := by
    have hg := (ht m).low X i i
    simpa [lift,Laurent.size] using hg
  let f (m : ℕ) := fun X : I→Cell ℤ => F (n m) (tor (n m) ∘ X)
  have hn : Tendsto (fun j => (n j).val) atTop atTop := march_out
  obtain ⟨A,-,s,hs,H⟩ := (isCompact_pi_infinite (fun _ : I→Cell ℤ => isCompact_closedBall (0:V) C)).tendsto_subseq
    (x:=f) (fun _ _ => hx _ _)
  have he (X : I→Cell ℤ) : Tendsto (fun j => F (n (s j)) (tor (n (s j)) ∘ X)) atTop (𝓝 (A X)) :=
    tendsto_pi_nhds.mp H X
  have hg : Cohere A := fun b X => by
    apply tendsto_nhds_unique (he (move b ∘ X))
    refine (he X).congr' (Eventually.of_forall ?_); intro i
    let y := n (s i)
    change F y (tor y ∘ X)=F y (tor y ∘ move b ∘ X)
    rw [show tor y ∘ move b ∘ X=move (wrap y b) ∘ (tor y ∘ X) from funext (fun i => tor_move ..),
      h.same (hc _)]
  have HN := hs.tendsto_atTop
  have ha := rates (A:=A) (F:=F) (n:=n ∘ s) (hn.comp HN) (Eventually.of_forall fun i => ht _) he hg
  exact ⟨A,ha, fun c hd => funext (h.limit i (n:=n ∘ s) (hn.comp HN) ha (Eventually.of_forall fun i => ht _) he c hd (HN.eventually (march_dvd L c)))⟩
end extraction
end YM.AnalyticNext.QuarticMatch.BoxChain
