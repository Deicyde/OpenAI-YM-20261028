import YM.Next.MULTISOURCE.Lanes
import YM.Work.I03


/-!
# Conditional production of `Mix.Circle`

Can even ask for different label in every cell of the replication! Same lane
for all joint submoments. Only one engineering weight here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Function Filter Finset Marker Overlay Stock Cells MeasureTheory Source Labels Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} (C : Family G)

namespace Fleet

def whirl (d : ℕ) (s : Signed × Bool) (v : C.label d) : C.label d :=
    let u := (C.labels.level d).act s.1.ortho v
    if s.2 then star u else u

lemma coherent (d : ℕ) (s : Signed × Bool) (v : C.label d) :
    Extraction.Spin.token C.book ⟨d,v⟩ s=⟨d,whirl C d s v⟩ := by
  cases s with | mk t h => cases h <;> simp only [whirl,Extraction.Spin.token,Bool.false_eq_true,↓reduceIte] <;> rfl

set_option maxRecDepth 4000 in
lemma ceiling (d : ℕ) (r : ℝ) : ∃ y : ℝ,0≤y ∧
    ∀ s : Signed × Bool, ∀ v : C.label d, ‖v‖ ≤ r → (C.labels.level d).coeffSize (whirl C d s v) ≤ y := by
  let f s (v : C.label d) := (C.labels.level d).coeffSize (whirl C d s v)
  have he i : Continuous (f i) := by
    have ht : Continuous (fun v : C.label d => whirl C d i v) := by
      have ht := ((C.labels.level d).act i.1.ortho).continuous_of_finiteDimensional; unfold whirl; split
      · exact ht.star
      exact ht
    unfold f Frame.coeffSize; fun_prop
  have hh i : BddAbove ((f i) '' Metric.closedBall 0 r) := ((isCompact_closedBall _ _).image (he i)).bddAbove
  choose a ha using fun i => hh i
  refine ⟨∑ i,max 0 (a i), Finset.sum_nonneg (fun i _ => le_max_left ..),?_⟩
  intro s v hv
  exact (ha s ⟨v,by simpa using hv,rfl⟩).trans ((le_max_right ..).trans (
    single_le_sum (fun i _ => (le_max_left 0 (a i))) (mem_univ s)))

lemma open_through (A : Levels G) (a : ℕ) : ∃ b : ℝ, 1 ≤ b ∧ ∀ i j : ℕ,Tabs.opens A b i j → a ≤ j := by
  let b := 1 + (A.S.a a)⁻¹
  have he j := A.S.a_pos j
  have hb : 1 ≤ b := by unfold b; simp [(he a).le]
  refine ⟨b,hb,fun i j hj => ?_⟩
  by_contra! hh
  have hg : b ≤ A.S.a i / A.S.a j := (show b ≤ b * ((A.clock.coverSize j:ℝ)^2) from
    le_mul_of_one_le_right (zero_le_one.trans hb) (one_le_pow₀
      (show (1:ℝ) ≤ A.clock.coverSize j by exact_mod_cast (A.budget _).B_pos))).trans hj.2
  have hp : A.S.a i ≤ 1 := by simpa using A.S.strictAnti.antitone (Nat.zero_le i)
  have hu := A.S.strictAnti hh
  have hC : (A.S.a a)⁻¹ < b := lt_add_of_pos_left _ zero_lt_one
  apply not_le_of_gt hC; apply hg.trans
  rw [← one_div]; gcongr; exact he _

variable {d N p m i : ℕ}

def foam (hm : m≤N) (v : Site (C.side m p) → C.label d) (i : Site (C.side m p)) :=
    (Cells.center C.S p hm 0).copy i (C.O N p (v i) 0)

/-- In this direction we accept ANY profiles from that cylinder ball. -/
def formation (C : Family G) (d : ℕ) (u : ℝ) (k : ℕ) (t : ℝ) := ∀ m i, C.ref d ≤ m →
    Tabs.opens C.path.levels t m i → ∀ᶠ N : ℕ in atTop, ∃ hN : m ≤ N, ∀ p : ℕ,
      ∀ v : Site (C.side m p) → C.label d, (∀ i,‖v i‖ ≤ u) →
        ∃ L : Lane C.path (census (Site (C.side m p))) N p,
          Passage (i:=i) (d:=d) C (width C 1 k) (camp C p m) (foam C hN v) L

lemma forms (d : ℕ) (h : G.Simple) (H : C.Makes) (HT : Tabs C.path.levels)
    (he : Margins C.path.levels) (hs : Addresses C) (A : Responsive C d) :
    ∃ k, ∀ R : ℝ, 0 ≤ R → ∃ t, (1:ℝ) ≤ t ∧ formation C d R k t := by
  obtain ⟨k,hk⟩ := sectioning C d h H HT he hs A
  refine ⟨k,fun r hr => ?_⟩
  obtain ⟨M,hM,I⟩ := ceiling C d r
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hk M hM)
  obtain ⟨t, ht, h'⟩ := open_through C.path.levels J
  refine ⟨t,ht,fun m i hm hi => ?_⟩
  filter_upwards [eventually_ge_atTop i, hs.1] with N hN hQ
  have hx := hi.1.trans hN; refine ⟨hx,fun p v hv => ?_⟩
  obtain ⟨Hc,-,HH⟩ := Work.I03.answer G C t ht HT m i hi N hN p hx
  let T := Cells.center C.S p hx (0:Site (C.side N p))
  let U j := whirl C d (Extraction.Spin.way T j) (v j)
  have hc : foam C hx v=fun j => C.O N p (U j) (camp C p m N j) := by
    funext j
    have e := Extraction.Spin.uses H (Cells.center C.S p hx 0) j 0 ⟨d,v j⟩ (hm.trans hx)
    rw [Hc j, coherent] at e
    exact e
  have hl (j : ℕ) (hj : i ≤ j) (_ : j ≤ N) := hJ j ((h' m i hi).trans hj)
  have hu : ∀ j, i≤j → j ≤ N → Spaced (camp C p m j) (C.path.levels.clock.coverSize j) := by
    intro j hj hN a b he
    have hh := HH j hj hN a b he; change _ ^2*t ≤ _ at hh
    have hs := (le_mul_of_one_le_right (sq_nonneg _) ht).trans hh
    exact_mod_cast hs
  have hy j (hj : i≤j) (_ : j<N) (x) := Work.I03.camp_step C p (hi.1.trans hj) x
  obtain ⟨X,HX⟩ := rolling (census (Site (C.side m p))) H (camp C p m) U (fun i => I _ _ (hv i))
    (hm.trans hi.1) hN hl (hQ p) hu hy
  rw [hc]; exact rides H HX hl hu hN hy (hm.trans hx)

/-- RMixed conditional theorem. Requires the singleton Family, exponent/address
receipts and one-step analytic response gate on *its actual choices*. -/
theorem mixed_circle (d : ℕ) (r : ℝ) (h : G.Simple) (H : C.Makes) (HT : Tabs C.path.levels)
    (he : Margins C.path.levels) (hs : Addresses C) (A : Responsive C d) (hr : 0 < r) : Circle C d r := by
  obtain ⟨k,hk⟩ := forms C d h H HT he hs A
  obtain ⟨t,ht,X⟩ := hk r hr.le
  refine ⟨1,t,k, zero_lt_one, ht, fun m i he hv => ?_⟩
  filter_upwards [X m i he hv] with N hf
  obtain ⟨hn,Hp⟩ := hf
  refine ⟨hn,fun p h u hu => ?_⟩
  obtain ⟨L,hL⟩ := Hp p (fun _ => u) (fun _ => hu)
  have hi := hv.1; have hh := hL.scope
  exact ⟨L, ⟨hi,hh.admits,fun i => ⟨congr_fun hL.stance i,congr_fun hL.exactF i⟩, fun i hi ht k => congr_fun
    (hL.anchored _ hi ht) k,hL.holds, hh.reads,hh.first, fun j s hi hf => hh.step j hi hf s⟩⟩
end Fleet
end YM.Multi
