import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inherited
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.PathPrices

/-!
# E, paths/true tails and incoming K meet the connected budget requirements

The phase in `expo` already includes both actual β costs. Test actual `expo`
and actual K coefficients under the old sup norms. No marking reserve needed
from any later phases. Orientations by actual path support; families countable;
extra lengths and old covers give room for additional polynomial marks. The same
prices apply when profiles of magnitude ≤1 come **inside** the exponent. At V
not on a coherent component these are still upper bounds -- not claiming the
full estimates without coherency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}

private lemma coreL (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0 < ε)
    (ha : 0 ≤ a) (hr : 4*ε < P.top.supportExponent) :
    ∃ n : ℕ, ∀ (c f : Side) (p : Ratio c f), n ≤ p.count.val →
      reserve (P.top.supportExponent-2*ε) a (conversion p (l+5)) ε :=
  Fees.exponent (l+5) he ha (by linarith)

/-- Both classes of Activity on *their own* aperture. -/
lemma core_bills (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a) (hr : 4*ε<P.top.supportExponent) :
    ∃ n : ℕ, ∀ L : Side, n≤L.val → ∀ (u v : ℝ), -(11/10:ℝ)<u → ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L → Intake P T x R →
      let p := S.ratio; let B := radiusB x
      ∃ E K : ℕ → ℝ, (∀ i U, |R.activities.regularOccurrence R.p i U| ≤ E i) ∧
        Sales B a ε (regularFoot p l B R) E (regularExtra R) ((betaF G x L)^u) ∧
        (∀ i U, |R.activities.K i U| ≤ K i) ∧ Sales B a ε (forcedFoot p l B R) K (forcedExtra R) ((betaF G x L)^v) := by
  obtain ⟨n,hn⟩ := coreL P l he ha hr
  refine ⟨n,fun L hL u v hv => ?_⟩
  let J (x : ℝ) := extentCost (l+5) (radiusB x)
  let bill (x d : ℝ) := Footprint.payment (L.val^4) (J x) 0 ε 1 d a (preCost (l+5))
  have hk {r : ℝ} {z : ℝ → ℝ} (h : Rate G L r z) : Rate G L r (fun x => bill x (z x)) := by
    have hh : Rate G L 0 (fun x : ℝ => (J x:ℝ)) := by simpa [extentCost,J] using
      (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
    simpa only [zero_add,bill] using! Rate.payment (Rate.const 1) h hh (L.val^4) 0 ε a _
  filter_upwards [hk (incomingE_rate G L) u hv, hk (incomingK_rate G L (v-1)) v (by linarith),
    Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent by linarith)] with x hx hy hh
  intro c f S T R hP hR p B
  have hP' : p.count=L := hP
  obtain ⟨b,hw,h⟩ := hR.cap.labels.boundE
  obtain ⟨d,hD,h'⟩ := hR.cap.labels.boundK
  refine ⟨b,d,fun i U => ?_,?_,fun i U => (hD i).2 _,?_⟩
  · by_cases he' : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [Activities.regularOccurrence, masked_eq _ _ _ _ he']; exact (hw i).2 _ he' [] (Nat.zero_le _) (by simp)
    rw [Activities.regularOccurrence,masked_ne _ _ _ _ he',abs_zero]; exact (hw i).1
  · let Y i := (R.activities.reg i).support
    have hY : Anchored (fun i => (R.activities.reg i).site) b (regularExtra R) (P.top.supportExponent)
        (incomingE G L x) := by
      rw [hR.exponent]; rw [hP] at h
      intro x; convert h x using 1; ext i; simp only [BudgetPoint.mass,regularExtra]; rw [mul_comm]
    have hm := Sales.anchored_sale (z := b) (l:=l+5) (M := R.p.B) p (fun i => (R.activities.reg i).site) (Y := Y)
      (fun i => (R.activities.reg i).anchor) hY (fun i => (hw i).1)
      (X:=regularFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
      (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
      (fun i => ⟨(hw i).1,by simp⟩)
    apply hm.raise; rw [hP']; exact (le_abs_self _).trans hx
  · let Y i := (R.activities.forced i).support
    choose o ho using fun i => (R.activities.forced i).inventory_ne
    have ht i : o i ∈ Y i := (R.activities.forced i).inventory_sup (ho i)
    have hk : Ac.Hit Y R.p.B d P.top.supportExponent (incomingK G L x) := by
      rw [hR.exponent]; rw [hP] at h'
      intro x; convert h' x using 1; ext i
      unfold Y BudgetPoint.mass; rw [mul_comm]
    have hm := Sales.anchored_sale (z := d) (l:=l+5) p o ht (Labels.anchor_weaker Y _ (fun i => (hD i).1) hk _ ht)
      (fun i => (hD i).1) (X:=forcedFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
      (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
      (fun i => ⟨(hD i).1,by simp⟩)
    apply hm.raise; rw [hP']; exact (le_abs_self _).trans hy

/-- Atom cost with factor test. E.g. β w∘f fits `D x`, cap `γ`
may include post-L loop power. Rooted at every output site. -/
lemma atoms_meet (G : Gauge) (L : Side) (k l : ℕ) {σ a ε : ℝ} {u v r : ℝ}
    (he : 0<ε) (ha : 0 ≤ a) (hw : 4*ε < σ) {D γ : ℝ → ℝ}
    (hc : Rate G L u D) (hv : Rate G L v γ) (hr : u - (1/2:ℝ)*k + v < r) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (p : Ratio c f), p.count=L →
      ∀ T : ℕ → Atom G k, SumBudget (fun i => (T i).budget σ) (γ x) → ∀ η : ℝ, |η| ≤ D x →
      ∀ q : BudgetPoint, q.threshold=fiery G x L →
        ∃ z : Trans f → ℝ, (∀ i U, |translateValue q T η U i| ≤ z i) ∧
          Sales (radiusB x) a ε (atomFoot p l (radiusB x) T) z (atomCharge T) ((betaF G x L)^r) := by
  let A x := D x*(fiery G x L)^k
  obtain ⟨s,hs,hS⟩ := exists_between hr
  have hh := Rate.mul hc (Rate.flame (G:=G) (L:=L) |>.pow k)
  have he' := Rate.power (G:=G) (L:=L) (a:=s) |>.mul_left (Fintype.card Signed : ℝ)
  filter_upwards [atom_bills G L L k 0 l he hw ha hh hv (show u+-(1/2:ℝ)*k+v<s by linarith), he' r hS]
    with x hx h
  intro c f p hp T hT η ht q hq
  have hD := (abs_nonneg η).trans ht
  have hp' : 0 < fiery G x L := hq ▸ q.threshold_pos
  have hz' : 0 ≤ A x := by unfold A; positivity
  let z (i : Site f × ℕ) := A x*(T i.2).magnitude
  let W (i : Trans f) := z i.2
  have hz i : 0 ≤ z i := mul_nonneg hz' (by unfold Atom.magnitude; positivity)
  refine ⟨W,fun i U => ?_,?_⟩
  · unfold translateValue; rw [abs_mul]
    apply le_trans (mul_le_mul ht (healthy_atom (T i.2.2) ..) (abs_nonneg _) hD)
    unfold W z A; rw [hq]; exact le_of_eq (by ring)
  have hr' := hx c f p hp T hT z hz' (fun i => ⟨hz i, by simp [z,A]⟩)
  have hm := Sales.price_fst W (atomFoot p l _ T) (atomCharge T) (fun _ => _) (fun s => hr'.rotated s 0 ha)
  apply hm.raise
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact (le_abs_self _).trans h

lemma tails_meet (G : Gauge) (L L' : Side) (d l : ℕ) {s : Clip} {σ a ε C u : ℝ} (he : 0<ε)
    (hd : 0 < d) (ha : 0 ≤ a) (hw : 8*ε < σ) {D : ℝ → ℝ} (hc : Rate G L u D) (r : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (p : Ratio c f), p.count=L' →
      ∀ (T : PathData G) (Λ : ℝ), T.Bounds s σ C Λ → ∀ η : ℝ, |η| ≤ D x →
      ∃ w : Pairs f → ℝ, (∀ i t (U : Config G f), |pairValue T s t (till x) d η U i| ≤ w i) ∧
        Sales (radiusB x) a ε (bothFoot p l (radiusB x) T) w (bothCharge T) ((betaF G x L)^r) := by
  have he' := (((Rate.power (G:=G) (L:=L) (a:=r-1)).mul_left (Fintype.card PlaqAxes : ℝ)).mul_left
    (Fintype.card Signed : ℝ))
  filter_upwards [tail_bills (s:=s) (C:=C) G L L' 0 l d hd he hw ha hc (r-1), he' r (by linarith)] with x hx hh
  intro c f p hp T Λ hT η ht
  have hD := (abs_nonneg η).trans ht
  let w i (j : Site f × (ℕ×ℕ)) := D x*pairPrice T (till x) d i j.2
  let W (i : Pairs f) := w i.2.1 i.2.2
  have hr i := hx c f p hp T Λ hT i (w i) hD
    (fun j => ⟨mul_nonneg hD (pairPrice_nonneg ..),by simp [w]⟩)
  refine ⟨W,fun i t U => ?_,?_⟩
  · unfold pairValue; rw [abs_mul]
    exact mul_le_mul ht (pair_le ..) (abs_nonneg _) hD
  have hu i (z : Signed) := (hr i).rotated z 0 ha
  have hv := Sales.price_fst W (bothFoot p l _ T) (bothCharge T) (fun _ => ∑ _ : PlaqAxes, betaF G x L ^ (r-1))
    (fun z => Sales.price_fst _ _ _ (fun _ => _) (fun i => hu i z))
  apply hv.raise
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact (le_abs_self _).trans hh

theorem inherit_bills (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) z (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
  obtain ⟨n,hn⟩ := core_bills P l he ha hx
  refine ⟨n,fun L hL r hv r' => ?_⟩
  obtain ⟨s,hm,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  filter_upwards [hn L hL s r' (by linarith), atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith),
    atoms_meet G L 4 l he ha hp ht hr (r := s) (by push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=s) (by push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht s,
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht s,
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hb hc hq hK hU hD h
  intro c f S T R hS hR
  let p := S.ratio
  have hl : p.count = L := hS
  obtain ⟨w,b,H1,H2,H3,H4⟩ := hb S T R hS hR
  let θ := -orientation*R.beta
  have ho : |-orientation|≤1 := by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  obtain ⟨hlh,hy'⟩ := hR.window
  have hθ : |θ| ≤ 2*betaF G x L := by
    rw [← hS]; unfold θ; rw [abs_mul, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le ho) hy'
  have hpaths := hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hS]
  obtain ⟨w₁,e₁,B₁⟩ := hc c f p hl R.path.cubic hpaths.three θ hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩ := hq c f p hl R.path.quartic hpaths.four θ hθ R.p hF
  rw [hS] at hpaths
  obtain ⟨w₀,e₀,B₀⟩ := hK c f p hl R.path.loop hpaths.two (-orientation) ho R.p hF
  have hu : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hu] at hpaths
  obtain ⟨w₃,e₃,B₃⟩ := hU c f p hl R.path _ hpaths θ hθ
  obtain ⟨_,_,_,hk⟩ := hR.ready.feeds
  obtain ⟨w₄,e₄,B₄⟩ := hD c c (atOne _) rfl T.down _ hk (-θ) (by simpa only [abs_neg] using hθ)
  let z := Sum.elim w (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  refine ⟨z,?_, (H2.together (B₁.together (B₂.together (B₀.together (B₃.together B₄))))).raise ?_,b,H3,H4⟩
  · intro U V i
    rcases i with i| (i | (i | (i | (i | i))))
    · dsimp only [z,expo,Sum.elim]; rw [abs_neg]; exact H1 i U
    · exact e₁ ..
    · exact e₂ ..
    · exact e₀ ..
    · dsimp only [expo,z,Sum.elim]; rw [hu]; exact e₃ ..
    dsimp only [expo,z,Sum.elim]
    rw [hR.ready.low,hS]; exact e₄ ..
  linarith only [h,le_abs_self (6*betaF G x L^s)]

private lemma enlarged_ne {n : Side} (p : Ratio c n) (l B : ℕ) (Y : Support n) (h : Y.Nonempty) :
    (enlargement p l B Y).Nonempty := (h.image _).mono (halo_subset _ _)

lemma space_ne (S : StepData c f) (T : Tube G S) (l B : ℕ) (R : Rep G f) (i) : (space T l B R i).Nonempty := by
  let p := S.ratio
  have hp {d} (A : ℕ→Atom G d) (i) : (atomFoot p l B A i).Nonempty := by
    refine Finset.Nonempty.image (enlarged_ne p l B (inspected _) (Finset.Nonempty.mono (fun z hz => mem_union_left _ hz) ?_)) _
    exact Nonempty.image ⟨0,mem_insert_self ..⟩ _
  have hb {c n} (p : Ratio c n) (T : PathData G) (i : Pairs n) : (bothFoot p l B T i).Nonempty := by
    refine Finset.Nonempty.image (enlarged_ne p l B _ ?_) _
    exact ⟨_,mem_union_right _ (mem_insert_self ..)⟩
  rcases i with i|(i|(i|(i|(i|i))))
  · exact enlarged_ne _ _ _ (inspected _) ⟨_,mem_union_left _ (R.activities.reg i).anchor⟩
  · exact hp _ _
  · exact hp _ _
  · exact hp _ _
  · exact hb _ _ _
  · exact hb _ _ _

lemma mayer_abs {r w ξ : ℝ} (h : |r|≤w) (he : w ≤ 1) (hξ : |ξ| ≤ 1) : |Real.exp (r*ξ)-1| ≤ 2*w := by
  have hy : |r*ξ| ≤ w := by rw [abs_mul]; exact le_trans (mul_le_of_le_one_right (abs_nonneg _) hξ) h
  exact (Real.abs_exp_sub_one_le (hy.trans he)).trans (by gcongr)


end YM.ConnectedActivityE6.Raw
