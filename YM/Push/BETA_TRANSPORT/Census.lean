import YM.Push.BETA_TRANSPORT.Curve

/-!
# From per-address uniform estimates and a dominating census to `Curve`'s deviation

All finite period supports, even winding, priced at the **requested** exponent.
The dominating list can be provided on a further subsequence, not necessarily
on a neighborhood. Fixed label records include every predicate in `forced`.
Per-address uniformity is at common U (no continuity in U of K is assumed).
Also a more concrete Lipschitz-per-address test; no summability of the individual
Lipschitz constants is needed there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG RG.Activities RG.Shoot MeasureTheory Filter Function Set
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff NNReal
variable {n : Side} {G : Gauge} {P : BudgetPoint}

lemma uniform_charge {Y : Type*} {f : Filter Y} {V : ℕ → Type*} (X : ℕ → Support n)
    (D : Y → ∀ i, V i → ℝ) {e : ℕ → ℝ} (he : Summable e) (hn : ∀ i, 0 ≤ e i)
    (hh : ∀ᶠ y in f, ∀ i v, D y i v ≤ e i)
    (hd : ∀ i (ε : ℝ), 0 < ε → ∀ᶠ y in f, ∀ v, D y i v ≤ ε) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in f, ∃ b : ℕ → ℝ, (∀ i, 0 ≤ b i ∧ ∀ v, D y i v ≤ b i) ∧
      SumBudget (fun i => P.mass (X i) (b i)) ε := by
  let r y i := insert 0 (range (D y i))
  let b y i := sSup (r y i)
  have hu y i c (hc : 0 ≤ c) (h : ∀ v, D y i v ≤ c) :
      (0 ≤ b y i ∧ ∀ v, D y i v ≤ b y i) ∧ b y i ≤ c := by
    have hx : ∀ z ∈ r y i, z ≤ c := by
      rintro z (hz|⟨v,rfl⟩)
      · rw [show z=(0:ℝ) from hz]; exact hc
      · exact h v
    exact ⟨⟨le_csSup ⟨_,hx⟩ (mem_insert ..),fun v => le_csSup ⟨_,hx⟩ (mem_insert_of_mem _ (mem_range_self _))⟩,
      csSup_le (insert_nonempty ..) hx⟩
  let g y i := P.mass (X i) (b y i)
  have hs := summable_mass P X hn he
  have ht : ∀ᶠ y in f, ∀ i, (0 ≤ b y i ∧ ∀ v, D y i v ≤ b y i) ∧ ‖g y i‖ ≤ P.mass (X i) (e i) := by
    filter_upwards [hh] with y hy i
    obtain ⟨h1,h2⟩ := hu y i (e i) (hn i) (hy i)
    exact ⟨h1,(Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le h1.1)).trans_le
      (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)⟩
  have hc i : Tendsto (fun y => b y i) f (𝓝 0) := tendsto_order.mpr ⟨fun ε hε => ht.mono fun y hy => hε.trans_le (hy i).1.1,
    fun ε hε => (hd i (ε/2) (half_pos hε)).mono fun y hy => (hu y i _ (half_pos hε).le hy).2.trans_lt (half_lt_self hε)⟩
  have hm i : Tendsto (fun y => g y i) f (𝓝 0) := by
    simpa only [g, BudgetPoint.mass,mul_zero] using (hc i).const_mul (Real.exp (P.supportExponent * coverNumber P.B (X i)))
  have hl := tendsto_tsum_of_dominated_convergence hs hm (ht.mono fun y hy i => (hy i).2)
  filter_upwards [ht, hl.eventually_le_const (show (∑' _ : ℕ, (0:ℝ)) < ε by simpa using hε)] with y hy hz
  exact ⟨b y, fun i => (hy i).1, fun i => mul_nonneg (Real.exp_pos _).le (hy i).1.1,
    .of_norm_bounded hs fun i => (hy i).2, hz⟩

/-- Uniform (across parameters under comparison) absolute *individual*
address majorants, costs separate. Not an assertion that pointwise
`Valid` supplies these uniformly along a full curve. -/
structure Majorizes (P : BudgetPoint) (e k : ℕ → ℝ) (S : Activities G n) : Prop where
  smooth i : P.supBounds (S.reg i).site (S.reg i).support (S.E i) (e i)
  hard i : 0 ≤ k i ∧ ∀ x, ‖S.K i x‖ ≤ k i

variable {Y : Type*} {S : Activities G n} {F : Y → Activities G n} {f : Filter Y}

/-- `∀ i`, *then* uniform parameter comparison on this address only. -/
structure AtEach (P : BudgetPoint) (S : Activities G n) (F : Y → Activities G n) (f : Filter Y) : Prop where
  E (i) (ε) : 0 < ε → ∀ᶠ y in f, variesRegular P (S.reg i) (S.E i) ((F y).E i) ε
  K (i) (ε : ℝ) : 0 < ε → ∀ᶠ y in f, ∀ U, ‖S.K i U - (F y).K i U‖ ≤ ε

lemma AtEach.map (h : AtEach P S F f) {Z : Type*} {l : Filter Z} {y : Z → Y} (hy : Tendsto y l f) :
    AtEach P S (F ∘ y) l := ⟨fun i ε hε => hy.eventually (h.E i ε hε),fun i ε hε => hy.eventually (h.K i ε hε)⟩

lemma deviation_filter (hreg : ∀ᶠ y in f, (F y).reg = S.reg) {e k : ℕ → ℝ} (he : Summable e) (hk : Summable k)
    (hS : Majorizes P e k S) (hF : ∀ᶠ y in f, Majorizes P e k (F y)) (hc : AtEach P S F f)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in f, deviation P S (F y) ε := by
  let X i := {p : Config G n × List (Directions G n) // Healthy P.threshold (S.reg i).support p.1 ∧
    p.2.length ≤ P.order ∧ ∀ a∈p.2, P.dirBound (S.reg i).site a}
  let r y i (v : X i) := ‖leftDerivs (S.E i) v.val.2 v.val.1 - leftDerivs ((F y).E i) v.val.2 v.val.1‖
  let d y i (v : Config G n) := ‖S.K i v - (F y).K i v‖
  have h₁ : ∀ᶠ y in f, ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i ∧ ∀ v, r y i v ≤ c i) ∧
        SumBudget (fun i => P.mass (S.reg i).support (c i)) ε := by
    refine uniform_charge _ r (he.add he) (fun i => add_nonneg (hS.smooth i).1 (hS.smooth i).1) ?_ ?_ hε
    · filter_upwards [hreg,hF] with y hy hh i v
      have hi := hh.smooth i; rw [hy] at hi
      obtain ⟨⟨p,l⟩,hv,hl,hd⟩ := v
      exact (norm_sub_le ..).trans (add_le_add ((hS.smooth i).2 p hv l hl hd) (hi.2 p hv l hl hd))
    intro i δ hδ; filter_upwards [hc.E i δ hδ] with y hy v
    obtain ⟨⟨p,l⟩,hv,hl,hd⟩ := v; exact hy.2 p hv l hl hd
  have h₂ := uniform_charge (P:=P) (fun i => (S.forced i).support) d (hk.add hk)
    (fun i => add_nonneg (hS.hard i).1 (hS.hard i).1) (hF.mono fun y hh i v => (norm_sub_le ..).trans
      (add_le_add ((hS.hard i).2 v) ((hh.hard i).2 v))) hc.K hε
  filter_upwards [h₁,h₂] with y hy hz
  obtain ⟨c,hc,hcs⟩ := hy; obtain ⟨b,hb,hbs⟩ := hz
  exact ⟨c,b,fun i => ⟨(hc i).1,fun U hv l hl hd => (hc i).2 ⟨(U,l),hv,hl,hd⟩⟩,hb,hcs,hbs⟩

/-- Further-subsequence criterion as used at a *single fixed period*. Not
an extraction of physical kernels or a new order. -/
def Submajorized (P : BudgetPoint) (S : Activities G n) (F : Y → Activities G n) (f : Filter Y) :=
  ∀ y : ℕ → Y, Tendsto y atTop f → ∃ (r : ℕ → ℕ) (e k : ℕ → ℝ), Tendsto r atTop atTop ∧ Summable e ∧ Summable k ∧
    Majorizes P e k S ∧ ∀ᶠ j in atTop, Majorizes P e k (F (y (r j)))



lemma deviation_submajorized [f.IsCountablyGenerated] (hreg : ∀ᶠ y in f, (F y).reg = S.reg)
    (hc : AtEach P S F f) (hm : Submajorized P S F f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in f, deviation P S (F y) ε := by
  by_contra h
  obtain ⟨y,hy,hY⟩ := frequently_iff_seq_forall.mp (show ∃ᶠ y in f, ¬ deviation P S (F y) ε from fun H => h (by simpa using H))
  obtain ⟨r,e,k,hr,he,hk,hS,hF⟩ := hm y hy
  obtain ⟨j,hj⟩ := (deviation_filter ((hy.comp hr).eventually hreg) he hk hS hF (hc.map (hy.comp hr)) hε).exists
  exact hY (r j) hj





lemma stable_from_census {s : Set ℝ} {T : ℝ → Rep G n}
    (hreg : ∀ x∈s, ∀ y∈s, (T x).activities.reg = (T y).activities.reg)
    (hforced : ∀ x∈s, ∀ y∈s, (T x).activities.forced = (T y).activities.forced)
    (hc : ∀ x∈s, AtEach P (T x).activities (fun y => (T y).activities) (𝓝[s] x))
    (hm : ∀ x∈s, Submajorized P (T x).activities (fun y => (T y).activities) (𝓝[s] x)) :
    StableActivities P T s := ⟨hreg,hforced,fun _ hε x hx => deviation_submajorized (eventually_of_mem self_mem_nhdsWithin
      (fun y hy => hreg y hy x hx)) (hc x hx) (hm x hx) hε⟩
end YM.Push.BetaTransport
