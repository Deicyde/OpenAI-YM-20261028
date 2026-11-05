import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Desk
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Package


/-!
# Spending the nonextensive annulus payment on an integral

On intact permits. No integrability required of an unprotected external
multiplier where packet defaults impossible (not in general reasonable!);
test on protected arguments only. Don't assume optional factors on disjoint
packets use independent Gaussian variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations Next.Fluctuations.Sector
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Sockets for the pre-L/post-L route. Including fixed size convention
500 in examples later. Can pay for all for a given l,D after buying
aperture, B local log pair price and extra ancillary log credits. -/
structure Budget (P : Teller G) (N : Side) (w κ : ℝ) (Z : ChartRatio G) (K E : ℝ) (l D n : ℕ) (B e' : ℝ) (x : ℝ) : Prop where
  large : 0<w
  rebate : 0<κ
  slots : 0<K
  cap : 0≤E
  localNonneg : 0≤B
  frames : Aperture P N w K x
  stamp : Sponsored Z P N w K E x
  funds (P0 : Patch) : P0.L=N → P0.J=P.j →
    ∃ H C, Ledger P N w κ (2*K) H n D x ∧ 0 ≤ C ∧
      (∀ β : ℝ, β∈Set.Icc (Scales.y G N x/2) (2*Scales.y G N x) →
        -Real.log (spare Z β) ≤ C*(1+Real.log (Scales.y G N x))) ∧
      AnnulusRatioInsertions.tally C E N l + (tagCurrency P0 l + B*(vans N l:ℝ) + e') ≤ H
  location (c f : Side) (S : StepData c f) (T : Tube G S) : S.patch.L=N →
    100*(1+radiusB x)≤c.val → P.Funds S T → PointCharge T x w κ

/-- Can actually pay at late heights. Only physical input of this purchase:
LocalRatio, used also for buying all SectorChange inputs here. Not
buying some arbitrary larger geometry radius and spending after the fact.
-/
lemma fare (Z : ChartRatio G) (hZ : LocalRatio Z) (P : Teller G) : ∃ i : ℕ, ∀ N : Side, i≤N.val → ∀ᶠ w : ℝ in atTop,
    ∃ κ K E, ∀ (l D n : ℕ) (B e' : ℝ), 0≤B → ∀ᶠ x : ℝ in atTop, Budget P N w κ Z K E l D n B e' x := by
  obtain ⟨i,h⟩ := before_local P
  refine ⟨i,fun N hi => ?_⟩; filter_upwards [h N hi] with w hw
  obtain ⟨hm,κ,hκ,hb⟩ := hw
  obtain ⟨K,E,hK,hE,h⟩ := openings P Z hZ N w hm
  obtain ⟨C,hC,hc⟩ := slots Z (L:=N) hZ
  refine ⟨κ,K,E,fun l D n B e' hB => ?_⟩
  by_cases ht : ∃ P0 : Patch,P0.L=N ∧ P0.J=P.j
  swap
  · filter_upwards [h] with x hx
    refine ⟨hm,hκ,hK,hE.le,hB,hx.1,hx.2,fun P0 hr hg => (ht ⟨P0,hr,hg⟩).elim,fun c f S T hs _ hx => ?_⟩
    exact (ht ⟨S.patch,hs,hx.atStep⟩).elim
  obtain ⟨P0,h0,h1⟩ := ht
  let H := AnnulusRatioInsertions.tally C E N l + (tagCurrency P0 l+B*(vans N l:ℝ)+e')
  filter_upwards [h,hb (2*K) H D n] with x hx he
  refine ⟨hm,hκ,hK,hE.le,hB,hx.1,hx.2,?_,he.2⟩
  intro S0 hi ht
  have hh : P0 = S0 := by
    cases P0; cases S0; congr <;> first | exact h1.trans ht.symm | exact h0.trans hi.symm
  have hβ (β : ℝ) (hl : β ∈ Set.Icc (Scales.y G N x/2) (2*Scales.y G N x)) : 0<β :=
    lt_of_lt_of_le (div_pos (by linarith only [he.1.1]) (by norm_num)) hl.1
  exact ⟨H,C,he.1,hC.le,fun β hh => hc _ _ he.1.1.le (hβ β hh) hh.2, hh ▸ le_refl _⟩

/-- Geometry convention at the buys. -/
structure Mooring (D l : ℕ) (x : ℝ) (r R : ℕ) : Prop where
  region : 2 ≤ D
  throughDefault : (D+5)*radiusB x ≤ r
  throughChart : (D+1)*radiusB x ≤ R
  room : r+1 ≤ l*radiusB x
  rents : R ≤ l*radiusB x
  grand : D+5 ≤ l



variable (O A : Stores S) (T : Tube G S) (x w : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (Z : ChartRatio G) (p : Rep G f) (F : Forest S.ratio)
  (L : Bond f → ℝ) (m : Mean (G:=G) A x F)
variable {P : Teller G} {κ K E B e' : ℝ} {l D n R R' : ℕ} {N : Side}
  (hZ : LocalRatio Z) (hP : P.Funds S T) (hh : Budget P N w κ Z K E l D n B e' x)
  (he : S.patch.L = N) (hm : 100*(1+radiusB x) ≤ c.val) (hd : d=K*fiery G x N)
  (hV : A.flags=RG.flags (temp x) V) (hr : Mooring D l x R R') (hn : 4≤n)
  (hβ : p.beta∈Set.Icc (Scales.y G N x/2) (2*Scales.y G N x))
  (hlog : ∀ i∈qLogs O (D*radiusB x), L i ≤ B) (hO : Isle O A l (radiusB x))


section budgets
variable {X : Type*} [MeasurableSpace X]
/-- Handy integral mechanism on multipliers still to be reconstructed. Hold
Y and z jointly. Does not even require an integration hypothesis on g
where packet tests fail. Doesn't claim **any** g has nonextensive bound. -/
lemma apply_receipt (μ : Measure X) (P g : X → ℝ) {R A : ℝ}
    (h : ∀ x, Real.exp R*‖P x‖ ≤ A) (he : Measurable P) :
    let M := {x| P x ≠ 0}
    let t := Set.indicator M g
    Integrable t μ → Integrable (fun x => P x*g x) μ ∧ Real.exp R*(∫ x, ‖P x*g x‖ ∂μ) ≤ A*∫ x, ‖t x‖ ∂μ := by
  intro M t ht
  have hi : Envelope P := ⟨he,A/Real.exp R,fun x => (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le (h x))⟩
  have h1 := Env.smul_L1 hi ht
  have hx (x : X) : P x • t x=P x*g x := by by_cases he : x∈M; unfold t; rw [Set.indicator_of_mem he,smul_eq_mul]; rw [show P x=0 from Classical.not_not.mp he,zero_smul,zero_mul]
  have hy x : Real.exp R * ‖P x*g x‖ ≤ A*‖t x‖ := by rw [← hx x,smul_eq_mul,norm_mul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)
  simp_rw [hx] at h1
  rw [← integral_const_mul,← integral_const_mul]; exact ⟨h1,integral_mono (h1.norm.const_mul _) (ht.norm.const_mul _) hy⟩
end budgets
include hh hP he hm hd hV hβ

/-- Output stamp to both upstream and downstream. Can ask at `meanLog`
and the physical fog as-is. NOTE: no promise of `Licenses` on data
already Gaussian when **deleting** a multiplier; that would need to
first realize a new Allocation etc. The charge, in contrast, can be
used even on those factors while keeping the original `W,A,F,q,...`.
-/
theorem arrival (B : Allocation G S x w) {σ C Λ δ ω₀} (hR : p.Lawful σ C Λ δ ω₀) :
    0 < d ∧ 2*d < firstRadius G ∧ 4*d<Z.radius ∧
      Admitted A F x V k Z B d ∧
      (Rows.gram T x V k (shots S x) A F).PosDef ∧
      (fog A F T x V k).PosDef ∧
      Licenses T x V k A p (shots S x) F B q Z d (fog A F T x V k) (meanLog A F T x V k q d) := by
  obtain ⟨-,h1,h2,h3,h4⟩ := hh.stamp
  obtain ⟨a,t⟩ := h4 _ _ S T he hm hP A F k V B q
  rw [← hd] at a t h1 h2
  have hβ' := hh.funds S.patch he hP.atStep
  obtain ⟨H,c,L,hC,Hc,hl⟩ := hβ'
  have hv : 0 < p.beta := lt_of_lt_of_le (show 0 < Scales.y G N x/2 from half_pos (by linarith only [L.1])) hβ.1
  obtain ⟨P',hQ,-⟩ := t hV p.beta hv
  exact ⟨hd ▸ hh.frames.2.1,h1,h2,a,hQ,P'.nativePos,authorized_change _ _ _ _ _ _ _ _ _ _ _ _ P' hR hP⟩

include hr hn hlog hO hZ
/-- The local, nonextensive packet receipt in useful L¹ multiplied
form. Integrable on the actual joint Gaussian law incl probHaar frozen
coordinates. Plus price *even* if bringing in any external multiplier,
which can then be charged separately for its remaining L¹. No claim
that g (e.g. real ratio letters) costs harmless powers of packet size
without additional work. See also absolute piece consumption at
ANCHORS and the restoration formula in Trip. Order 0, not all-jet.
-/
theorem order (uniform : Bool) (b : Finset ℕ) (hM : Measurable m) :
    let Z' := (piHaar G (Frozen A x F)).prod (cloud (fog A F T x V k))
    let v := wrapper O A T x w V k q d Z p F L m uniform b D R R'
    let t := coin G N e' n x * O.shares
    let z := -κ/4*(Scales.p G N x)^2 * O.shares
    Measurable v ∧ (∀ y, Real.exp t*‖v y‖ ≤ Real.exp z) ∧ Integrable v Z' ∧
      ∀ g : GaussArgs (G:=G) A x F → ℝ, let u := Set.indicator {x|v x ≠ 0} g
        Integrable u Z' → Integrable (fun x => v x*g x) Z' ∧ Real.exp t * ∫ x, ‖v x*g x‖ ∂Z' ≤
          Real.exp z * ∫ x, ‖u x‖ ∂Z' := by
  intro S0 v t z
  obtain ⟨H,Y,hL,hC,hK,hs⟩ := hh.funds S.patch he hP.atStep
  have hx : 0 < fiery G x S.patch.L := he.symm ▸ hh.frames.1
  obtain ⟨h0,h1,h2,h3,h4⟩ := hh.stamp
  obtain ⟨hb,hg⟩ := h4 _ _ S T he hm hP A F k V (q.profiles G S x w hh.large hx) q
  rw [← hd] at h0 h1 h2 h3
  obtain ⟨P',hQ,z',hq',hQ'⟩ := hg hV 1 one_pos
  have hk : 0<d := hd ▸ hh.frames.2.1
  have hv y : Real.exp t*‖v y‖ ≤ Real.exp z := valued O A T x w V k q d Z p F y.1 y.2 L m uniform b l D R R' he hm hP
    hh.large hr.region hr.throughDefault hr.throughChart hr.room hr.rents hr.grand hO hh.frames hd h0 hh.cap h3 n hn hL
    (hh.location _ _ S T he hm hP) hβ hC (hK _ hβ) (fun s => wholeIssued _ _ _ _ _ hQ' _ s) hh.localNonneg hlog hs
  have hi : Measurable v := packet_meas O A T x w V k q d Z p F L m uniform b _ _ _ hP hZ hk h1 h2 hM
  refine ⟨hi,hv,?_ , fun g => apply_receipt S0 v g hv hi⟩
  have he : Envelope v := ⟨hi,Real.exp z/Real.exp t,fun y => (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le (hv y))⟩
  exact he.integrable _

end YM.AnalyticBridge.AnnulusRatioInsertions
