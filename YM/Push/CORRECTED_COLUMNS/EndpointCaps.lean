import YM.Overlay.Pays
import YM.Push.CORRECTED_COLUMNS.Haar
import YM.Vac.Shelter

/-!
# Local value bills at the last level

One possible interface for the K endpoint. Doesn't ask for a hierarchy
or phase above these bills; they will be paid independently on the marked
push. No derivative estimates used for marked terms at this stage. No
smallness of the number of copies. Sum *before* integration. Compare
 at h.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Endpoint
open Marker Lattice RG Wilson MeasureTheory Function Overlay
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {P : Rep G n}

section Decay

/-- Negative *linear* plaquette exponent we will retain, also on flagged
sectors. `l` is a dimensionless weight. Scale s, normalize by s/4 to
later compare to the probability-Haar shell of radius s/4. -/
def per (l s : ℝ) (U : Config G n) : ℝ := ∑ p : Face (Per n), l*(G.chord (faceValue U p)/(s/4))
lemma per_orbit (l s : ℝ) (U : Config G n) (t : Signed) : per l s (pull t 0 U) = per l s U := by
  unfold per
  simp only [Face.send_price U _ t (0 : Site n) G.chord G.chord_inv (fun k g => G.chord_conj g k)]
  let e : Equiv.Perm (Face (Per n)) := Equiv.ofBijective (Face.send t 0) ⟨Face.injective_send t _,
    (Finite.injective_iff_surjective).mp (Face.injective_send t _)⟩
  exact Equiv.sum_comp e fun i => l*(G.chord (faceValue U i)/(s/4))
lemma retained (l s : ℝ) (U : Config G n) :
    Real.exp (-per l s U)= ∏ p : Face (Per n), link G l (s/4) (faceValue U p) := by
  simp only [per,← Finset.sum_neg_distrib,Real.exp_sum,link,neg_mul]

/-- Pay the shifted exponent by the actual caps, not just the
mask-true vacuum. -/
theorem suppress (P : Rep G n) {l s σ A Λ δ w : ℝ} (H : P.Lawful σ A Λ δ w) (hl : 0 < l) (hs : 0 < s)
    (hp : 0 < P.beta) (ht : s≤P.p.threshold) (hv : 4*l ≤ P.beta*P.clip.linear*s^2) (U : Config G n) :
    P.exponent U + per l s U ≤ P.scalar+ (Fintype.card (Site n):ℝ)*(P.exCost A Λ δ+Fintype.card PlaqAxes*(4*l)) := by
  let C := P.clip
  have hc (r : ℝ) (hr : 0 ≤ r) : l*(r/(s/4)) -4*l ≤ P.beta*PathData.clipped C P.p.threshold r := by
    rcases lt_or_ge r s with he|he
    · rw [PathData.clipped,if_pos (he.le.trans ht)]
      have hj : r/(s/4) ≤ 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
      have hw := mul_le_mul_of_nonneg_left hj hl.le
      have hq := C.quadratic_pos
      exact le_trans (by linarith : _ ≤ (0:ℝ)) (by positivity)
    have H₁ : l*(r/(s/4)) ≤ P.beta*(C.linear*s*r) := by
      have hy := mul_le_mul_of_nonneg_right hv hr
      change 4*l*r ≤ P.beta*C.linear*s^2*r at hy
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      -- hv here includes s²; use directly
      linarith
    have H₂ : l*(r/(s/4))-4*l ≤ l*(r/(s/4)) := sub_le_self _ (by positivity)
    unfold PathData.clipped; split
    · apply (H₂.trans H₁).trans
      apply mul_le_mul_of_nonneg_left _ hp.le
      have hg : C.linear ≤ C.direct/2 := by have h := C.kink; linarith [C.quadratic_pos]
      have hz := C.quadratic_pos
      have hC := mul_le_mul hg he hs.le (by positivity : 0 ≤ C.direct/2)
      linarith only [mul_le_mul_of_nonneg_right hC hr]
    apply (H₂.trans H₁).trans
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht C.tail_pos.le) hr
  let N : ℝ := Fintype.card (Site n)
  let D := Fintype.card PlaqAxes*(4*l)
  let loops := PathData.loopsPrice P.p P.beta A Λ
  have hj (V : Config G n) : per l s V-N*D-N*loops ≤ P.path.principal P.clip P.p P.beta V := by
    have ht (f : Face (Per n)) : l*(G.chord (faceValue V f)/(s/4))-4*l ≤ P.beta*P.path.baseTerm P.clip P.p V f := by
      apply (hc _ (G.chord_nonneg (faceValue V f))).trans
      apply mul_le_mul_of_nonneg_left _ hp.le
      unfold PathData.baseTerm; split
      · exact le_add_of_nonneg_right (by positivity)
      rw [add_zero]
    have ha : per l s V-N*D ≤ P.beta * ∑ f, P.path.baseTerm P.clip P.p V f := by
      have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ht i)
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum _ _ P.beta] at h
      simpa only [per,D,N,Face,Site,Fintype.card_prod,Finset.card_univ,nsmul_eq_mul,Nat.cast_mul,mul_assoc] using h
    linarith only [ha,(abs_le.mp (P.path.volume_price _ P.p P.beta hp.le V H.paths)).1]
  have hL : per l s U - N*D-N*loops ≤ P.path.inChannels P.clip P.p P.beta U := by
    apply (Branch.avg_const (n:=Signed) _).symm.le.trans (Branch.avg_mono fun i => ?_)
    exact per_orbit _ _ _ _ ▸ hj (pull i 0 U)
  have hg : -(N*δ) ≤ P.activities.additive P.p U := (abs_le.mp (volumeE _ H.labels U)).1
  change P.scalar-_-_+_ ≤ P.scalar+N*(δ+loops+D)
  linarith only [hL,hg]
end Decay

section Value
variable {V : Type*} [DecidableEq V] [Fintype V] {R : Census V}

/-- Sufficient local supports/hit caps, weaker than derivative
`Overlay.Radial`. `K` pays also at these radii on a FAILED good-set; in
particular `.keeps` unchanged. `bulk` pays only values and omits support
exponent (only enough for this terminal step; ask separately with reserves
for earlier transfer). `pins` et al recorded for integration clarity;
estimates here don't rely on spatial decay. `t` arguments are REAL and
multiply absolute norms. Supports from the very same Rep, disjoint/coverage
still imposed in the identity. -/
structure Value (M : Bands R P) (W : V → ℝ) (u b c : ℝ) : Prop where
  pure i : 0 < W i
  proper i : (M.rays i).val.Nonempty
  pins i j : j∈ (M.rays i).val → M.origins j ∈ M.support i
  borel i : Measurable (M.H i)
  localH i : LocalOn (M.support i) (M.H i)
  symmetry i : GaugeInvariant (M.H i)
  occurs i j : (M.marks i j).val.Nonempty
  stays i j : M.entries i j ≠ 0 → ∀ s∈(M.marks i j).val,M.origins s∈ (P.activities.forced i).support
  reads i j : UsesFinal P.p.threshold (P.activities.forced i).support (M.entries i j)
  keeps i j (x : Config G n) : M.entries i j x≠0 → (P.activities.forced i).eligible P.p.threshold x
  meas i j : Measurable (M.entries i j)
  invariant i j : GaugeInvariant (M.entries i j)
  units i : W i * ‖M.units i‖ ≤ u
  bulk : ∃ t : ℕ → ℝ, (∀ i, 0≤t i ∧ ∀ U : Config G n, Healthy P.p.threshold (M.support i) U →
        ‖M.H i U‖ ≤ t i) ∧
    ∀ i : V, SumBudget (fun j => if i∈ (M.rays j).val then Poly.toll W (M.rays j)*t j else 0) b
  hits : ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤t (i,j) ∧ ∀ x, ‖M.entries i j x‖ ≤ t (i,j)) ∧
    ∀ i : V, SumBudget (fun k => if i∈ (M.marks k.1 k.2).val then
      Poly.toll W (M.marks k.1 k.2)*t k else 0) c

variable {W : V → ℝ} {u b c w d σ A Λ : ℝ} {M : Bands R P}
private lemma weaken_budget {ι : Type*} {f g : ι → ℝ} {D : ℝ} (h : SumBudget g D) (hf : ∀ i, 0≤f i) (H : ∀ i, f i ≤ g i) : SumBudget f D := by
  have he := h.2.1.of_nonneg_of_le hf H
  exact ⟨hf, he,(he.tsum_le_tsum H h.2.1).trans h.2.2⟩

omit [Fintype V] in
lemma of_radial {m p : ℝ} (h : M.Active) (H : M.Radial W u b m p) : Value M W u b (m*p) := by
  refine ⟨H.pure,h.proper,h.pins,fun i => (h.regular i).borel,fun i => (h.regular i).sites,
    fun i => (h.regular i).symmetry,h.occurs,h.retained,h.inspects,h.keeps,h.meas,h.invi,H.localU,?_,?_⟩
  · obtain ⟨t,ht,hb⟩ := H.bulk
    refine ⟨t,?_,?_⟩
    · intro i
      obtain ⟨x,hx⟩ := h.proper i
      exact ⟨(ht i).1, fun U hU => ((ht i).2 x hx).2 U hU [] (by simp) (by simp)⟩
    intro i; refine weaken_budget (hb i) ?_ ?_
    · intro j; split; exact mul_nonneg (Poly.worth H.pure _).le (ht _).1; exact le_rfl
    intro j; split_ifs; exact mul_le_mul_of_nonneg_left (P.p.loMass _ _ (ht _).1) (Poly.worth H.pure _).le; exact le_rfl
  obtain ⟨t,ht,hb⟩ := H.hits
  refine ⟨t,ht,fun i => weaken_budget (hb i) ?_ ?_⟩
  · rintro ⟨j,k⟩; split; exact mul_nonneg (Poly.worth H.pure _).le (ht j k).1; exact le_rfl
  rintro ⟨j,k⟩; split_ifs; exact mul_le_mul_of_nonneg_left (P.p.loMass _ _ (ht j k).1) (Poly.worth H.pure _).le; exact le_rfl

variable (hv : Value M W u b c)

-- Here using weak VALUE ONLY budgets, bootstrapping to the physical
-- absolute sums (cf. Overlay.Pays for the regular/derivative hypotheses).
lemma Value.totalE (hv : Value M W u b c) (U : Config G n) : Summable (fun i => M.ray i U) ∧
    Poly.price W (M.extra U) ≤ Fintype.card V*(u+b) := by
  obtain ⟨t,ht,hw⟩ := hv.bulk
  have he := per_system (fun i => mul_nonneg (Poly.worth hv.pure (M.rays i)).le (ht i).1) hv.proper hw
  have hh (i) : Poly.price W (M.ray i U) ≤ Poly.toll W (M.rays i)*t i := by
    rw [Bands.ray,Poly.solo]; refine mul_le_mul_of_nonneg_left ?_ (Poly.worth hv.pure _).le
    by_cases hx : Healthy P.p.threshold (M.support i) U
    · rw [masked_eq _ _ _ _ hx]; exact (ht i).2 U hx
    rw [masked_ne _ _ _ _ hx,norm_zero]; exact (ht _).1
  obtain ⟨hp,hP⟩ := Poly.budgeted hv.pure he.2.1 hh
  refine ⟨hp,(Poly.addition hv.pure _ _).trans ?_⟩
  rw [mul_add]; apply add_le_add ((Poly.batch hv.pure ..).trans ?_) (hP.trans he.2.2)
  simp_rw [Poly.solo,Poly.solo_toll]
  exact (Finset.sum_le_sum (f:=fun i => W i * ‖M.units i‖) fun i _ => hv.units i).trans (by simp)

lemma Value.totalK (hv : Value M W u b c) (H : P.activities.Valid P.p d w) (U : Config G n) :
    (∀ i : ℕ, Summable (fun j => M.tagged i j U)) ∧ SumBudget (fun i => Poly.price W (M.each i U))
      (Fintype.card (Site n)*w+Fintype.card V*c) := by
  obtain ⟨q,hq,hi⟩ := H.boundK
  have ha (i) : (P.activities.forced i).support.Nonempty :=
    (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
  have he : Summable q := Activities.summable_charge ha (fun i => (hq i).1) hi
  obtain ⟨t,ht,hh⟩ := hv.hits
  let T (i : ℕ × ℕ) := Poly.toll W (M.marks i.1 i.2)*t i
  have hT := per_system (f:=T) (fun i => mul_nonneg (Poly.worth hv.pure _).le (ht i.1 i.2).1)
    (P:=fun i => M.marks i.1 i.2) (fun i => hv.occurs i.1 i.2) hh
  obtain ⟨hx,hR⟩ := (summable_prod_of_nonneg (show 0 ≤ T from hT.1)).mp hT.2.1
  have hs i : Summable (fun j => M.tagged i j U) ∧ Poly.price W (∑' j, M.tagged i j U) ≤ ∑' j,T (i,j) := by
    apply Poly.budgeted hv.pure (hx i); intro j
    rw [Bands.tagged,Poly.solo]; exact mul_le_mul_of_nonneg_left ((ht i j).2 U) (Poly.worth hv.pure _).le
  refine ⟨fun i => (hs i).1,weaken_budget (g:=fun i => q i+∑' j,T (i,j)) ?_ (fun i => Poly.nonnegative hv.pure _) ?_⟩
  · refine ⟨fun i => add_nonneg (hq i).1 (tsum_nonneg fun _ => hT.1 _), he.add hR,?_⟩
    rw [Summable.tsum_add (g:=fun i => ∑' j,T (i,j)) he hR,← hT.2.1.tsum_prod]
    exact add_le_add (sumRoot ha (fun i => (hq i).1) hi) hT.2.2
  intro i; refine (Poly.addition hv.pure _ _).trans (add_le_add ?_ (hs i).2)
  simp only [Poly.solo,Poly.quiet_toll,Complex.norm_real,one_mul]
  exact (hq i).2 U

lemma Value.full (hv : Value M W u b c) (H : P.activities.Valid P.p d w) (U : Config G n) :
    Summable (fun i => M.packet i U) ∧ Poly.price W (M.cluster U) ≤
    Real.exp (Fintype.card (Site n)*w+Fintype.card V*c) := by
  obtain ⟨-,hn,hs,hg⟩ := hv.totalK H U
  let f (i) := Poly.price W (M.each i U)
  have HH : Summable fun t => ∏ i∈t,f i := summable_finsetProd_of_summable_nonneg hn hs
  have hp (s : Finset ℕ) : Poly.price W (M.packet s U)≤ ∏ i∈s,f i := by
    unfold Bands.packet; split
    · exact Poly.multiple hv.pure _ _
    rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _ => hn i
  have hh := Poly.budgeted hv.pure HH hp
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply le_of_tendsto HH.hasSum; refine Filter.Eventually.of_forall fun s => ?_
  let l := s.biUnion id
  calc
    _ ≤ ∑ v∈l.powerset, ∏ i∈v,f i := Finset.sum_le_sum_of_subset_of_nonneg (fun x hx =>
      Finset.mem_powerset.mpr fun i hi => Finset.mem_biUnion.mpr ⟨x,hx,hi⟩) (fun i _ _ => Finset.prod_nonneg fun i _ => hn i)
    _ = ∏ i∈l, (1+f i) := (Finset.prod_one_add l).symm
    _ ≤ ∏ i∈l, Real.exp (f i) := Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (hn i))
      (fun i _ => le_trans (le_of_eq (add_comm _ _)) (Real.add_one_le_exp (f i)))
    _ = Real.exp (∑ i∈l, f i) := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_monotone ((hs.sum_le_tsum _ fun i _ => hn i).trans hg)

-- Signed H rotations are included when costing `P.path.principal`.
theorem Value.extent (hv : Value M W u b c) (H : P.Lawful σ A Λ d w) {l s : ℝ} (hl : 0 < l) (hs : 0 < s)
    (hp : 0 < P.beta) (ht : s≤P.p.threshold) (hw : 4*l ≤ P.beta*P.clip.linear*s^2) (U : Config G n) :
    Poly.price W (M.density U) ≤
      Real.exp (P.scalar+(Fintype.card (Site n):ℝ)*(P.exCost A Λ d+Fintype.card PlaqAxes*(4*l)+w) + Fintype.card V*(u+b+c))*
      ∏ p : Face (Per n), link G l (s/4) (faceValue U p) := by
  rw [Bands.density,Poly.adapted,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  let N : ℝ := Fintype.card (Site n)
  have hh : Real.exp (P.exponent U) ≤ Real.exp (P.scalar+ N*(P.exCost A Λ d+Fintype.card PlaqAxes*(4*l))-per l s U) :=
    Real.exp_monotone (le_sub_iff_add_le.mpr (suppress P H hl hs hp ht hw _))
  have he := (Poly.multiplication hv.pure (Poly.pass (M.extra U)) (M.cluster U)).trans (mul_le_mul
    ((Poly.pass_budget hv.pure _).trans (Real.exp_monotone (hv.totalE U).2))
    (hv.full H.labels U).2 (Poly.nonnegative hv.pure _) (Real.exp_pos _).le)
  refine (mul_le_mul hh he (Poly.nonnegative hv.pure _) (Real.exp_pos _).le).trans_eq ?_
  rw [← retained]; simp_rw [← Real.exp_add]
  dsimp only [N]; congr 1; ring
end Value
end YM.Push.Corrected.Endpoint
