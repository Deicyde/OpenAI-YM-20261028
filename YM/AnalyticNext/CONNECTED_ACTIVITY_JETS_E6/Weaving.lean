import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch

/-!
# Actual mass expenditure on Y and z

These integrals may hold on a fixed Data co-sector. They include all
fields kept in Optical Step. Defer factoring log polygons except
when pricing supports with Tests. Use absolute value in molecule before
Haar integral on F; No leaps to a normalized free density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {W μ C x : ℝ} {R : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {I : Rep G f}
variable (H : Cash W x μ L R o C T I)

def opt (i : Alphabet c f) := rates H.v H.w (H.alarms * topStorm S.patch) i

def text (i : Head S) :=
    Mixed.costs S R.halo (radiusB x) (steamP S (R.costs L μ I.beta x C)) H.opt i

/-- Suppressing zero-probability factors in this product separately.
Before integration. -/
def fair (i : Head S) : ℝ := Mixed.costs S R.halo (radiusB x) (steamP S (R.costs L μ I.beta x C))
    (rates H.v H.w (topStorm S.patch)) i

lemma earns (i : Alphabet c f) : 0≤ H.opt i := H.fares.nonneg _
lemma armed : Mixed.Accounts S R.halo (radiusB x) (R.costs L μ I.beta x C) (footprints T I R.halo (radiusB x)) H.opt
    (ConnectedActivityE6.lengths T I) (steamP S (R.costs L μ I.beta x C)) := by
  refine ⟨fun i _ => ⟨?_,le_rfl⟩, H.earns, fun _ => Nat.cast_nonneg _, H.fares.hit⟩
  unfold steamP Packets.income; exact mul_nonneg H.laws.acquired.capture (Real.exp_pos _).le

lemma positive (k : Head S) : 0 ≤ H.text k := by
  rcases k with k|k
  · unfold text Mixed.costs; dsimp only [Sum.elim]; split
    next he => exact (H.armed.packetBound k he).1
    exact le_rfl
  exact H.earns k
lemma fair_price (k : Head S) : 0 ≤ H.fair k := by
  rcases k with k|k|k|k
  · exact H.positive (Sum.inl k)
  · exact H.positive (Sum.inr (Sum.inl k))
  · exact H.positive (Sum.inr (Sum.inr (Sum.inl k)))
  exact zero_le_one.trans (topStorm_one _)

lemma combined (p : Molecule S) : (∏ i∈p,H.text i) = H.alarms^(blaze p).card*(∏ i∈p,H.fair i) := by
  rw [cumulate p H.text, cumulate p H.fair]
  let X := p.toRight; let Y := X.toRight
  have hx : (∏ i∈X,H.text (.inr i)) = H.alarms^(blaze p).card*(∏ i∈X,H.fair (.inr i)) := by
    rw [cumulate X,cumulate X]
    let f (i) := H.text (Sum.inr (Sum.inr i)); let g i := H.fair (Sum.inr (Sum.inr i))
    have he : (∏ i∈Y,f i) = H.alarms^(blaze p).card*(∏ i∈Y,g i) := by
      rw [cumulate Y,cumulate Y, ← Finset.prod_const]
      change _ = (∏ _i∈Y.toRight, _)*((∏ i ∈ Y.toLeft, H.w i)* ∏ i∈Y.toRight, _)
      change (∏ i∈Y.toLeft, H.w i)* (∏ _i∈ Y.toRight, H.alarms * topStorm S.patch) =
        (∏ _i∈Y.toRight, H.alarms)* ((∏ i∈Y.toLeft,H.w i)*∏ _i∈Y.toRight,topStorm S.patch)
      rw [Finset.prod_mul_distrib]; ring
    change (∏ i∈X.toLeft,H.v i)*(∏ i∈Y,f i)=_* ((∏ i∈X.toLeft,H.v i)*∏ i∈Y,g i)
    rw [he]; ring
  rw [hx]; rw [mul_left_comm]; rfl

variable (X : Coat T F) (ht : X.x=x) (hy : X.width=o.K) (hp : X.manifest) (k : Finset ℕ) (p : Molecule S)

include ht hy hp H
lemma voice (i : Head S) (z : Air f G) : |X.vertex I R.table W o.a k R.halo z i|≤ H.fair i := by
  have he := H.quotes F X ht hy hp
  rcases i with A|i|i|i
  · by_cases hk : Packets.connected S R.halo (radiusB x) A
    · have hr : Packets.connected S R.halo X.B A := by unfold Coat.B; rwa [ht]
      simp only [vertex,fair,Mixed.costs,Sum.elim, if_pos hr, if_pos hk]; exact he.2.2.1 ..
    have hr : ¬Packets.connected S R.halo X.B A := by unfold Coat.B; rwa [ht]
    simp only [vertex,fair,Mixed.costs,Sum.elim, if_neg hk, if_neg hr, abs_zero, le_rfl]
  · exact he.1 ..
  · exact (he.2.1 ..).2
  exact X.fires_at ..

lemma every (Y : F.Slice G) (z : Air f G) : |X.body I R.table W o.a k R.halo p (Y,z)| ≤ ∏ i∈p,H.fair i := by
  unfold body term; rw [abs_prod]; exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun i _ => H.voice (X.wrapY Y) ht hy hp k i z)

lemma lease (Y : F.Slice G) (z : Air f G) (h : X.body I R.table W o.a k R.halo p (Y,z)≠0) :
    z ∈ X.catastrophe o.ξ I.beta (blaze p) := by
  apply (H.quotes F (X.wrapY Y) ht hy hp).2.2.2 (blaze p)|>.2 k z
  intro i hi he
  unfold blaze at hi
  exact h <| Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi)))
    (show (X.wrapY Y).vertex I R.table W o.a k R.halo z (.inr (.inr (.inr i))) = 0 from he)

lemma integrated : Integrable (X.body I R.table W o.a k R.halo p) ((F.order G).prod X.dice) := by
  have he := H.laws.data.access; rw [← ht, ← hy] at he
  have hp := X.body_b R.table_exists (ht.symm ▸ H.laws.intake) he o.a k R.halo p
  exact (memLp_top_of_bound hp.aestronglyMeasurable _ (Eventually.of_forall
    (fun w => H.every X ht hy ‹X.manifest› k p w.1 w.2))).integrable le_top

lemma statements : ∫ i : F.Slice G × Air f G, ‖X.body I R.table W o.a k R.halo p i‖ ∂((F.order G).prod X.dice)
    ≤ ∏ i∈p,H.text i := by
  let J := X.catastrophe o.ξ I.beta (blaze p); let Y:= ∏ i∈p,H.fair i
  let W' (i : F.Slice G × Air f G) := J.indicator (fun _ => Y) i.2
  let μ := (F.order G).prod X.dice
  have hc : MeasurableSet J := Poll.sounded ..
  have hh : Integrable W' μ := by
    have he := (integrable_const Y (μ:=X.dice)).indicator hc
    exact he.comp_snd _
  have ht' (i : F.Slice G× Air f G) : ‖X.body I R.table W o.a k R.halo p i‖ ≤ W' i := by
    rcases i with ⟨Y,z⟩; by_cases he : z∈ J
    · unfold W'; rw [Set.indicator_of_mem he]; exact H.every X ht hy hp k p Y z
    have hj := mt (H.lease X ht hy hp k p Y z) he
    unfold W'; rw [not_ne_iff.mp hj,Set.indicator_of_notMem he,norm_zero]
  apply (integral_mono (H.integrated X ht hy hp k p).norm hh ht').trans
  rw [H.combined p, integral_prod _ hh]
  have hw (i : F.Slice G) : ∫ z,W' (i,z) ∂X.dice=X.dice.real J * Y := integral_indicator_const Y hc
  simp_rw [hw]; rw [integral_const]; simp only [probReal_univ,one_smul]
  exact mul_le_mul_of_nonneg_right ((H.quotes F X ht hy hp).2.2.2 (blaze p)).1
    (Finset.prod_nonneg fun i _ => H.fair_price i)
end YM.ConnectedActivityE6.Cash
