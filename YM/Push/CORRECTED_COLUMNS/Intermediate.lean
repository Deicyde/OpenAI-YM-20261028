import YM.Push.CORRECTED_COLUMNS.Invited
import YM.Push.CORRECTED_COLUMNS.Rest
/-!
# : inserting, restoring and reprinting the corrections
at *l* (intermediate endpoint)

See `print`. This is **not** already an assertion at h. Input K/H
estimates *on the actual representations* BEFORE inserting any Y
corrections, with smaller source radius on mixed and K. Authority
hypotheses (separated geometry at this level, numerical inequalities)
stated at use. Includes exactly the failed-mask factors on the bias,
no assumption of small weights on those failure letters alone. One use
per `k,i,c` entire marker calculation; `Pad.enlarge` is independent of
which of the rows are used here. Work directly on the transfer in
`Wire.station`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Endpoint
open Filter Function Set Lattice RG Marker Overlay Prepare Width Wilson MeasureTheory Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius

section intermediate
variable {G : Gauge} {C : Family G} {S : Table C.book} {d : ℕ} {X : Columns C S d}
variable (Y : Tests X)

-- Not-yet-corrected. Microscope and symbols still fixed throughout.
def uncorrected (i : Row X) (c : AxisX X) (k N p) (U : Config G (C.side N p)) :=
    Marks.ordinary fun s => Y.letter k N p i c s U
lemma regular (i c k N p) (u) : Continuous (fun U => (uncorrected Y i c k N p U).part u) := by
  have ht s : Continuous (Y.letter k N p i c s) := C.continuousO ..
  have he : Continuous (uncorrected Y i c k N p) := by
    unfold uncorrected Marks.ordinary; refine continuous_finsetProd _ (fun j _ => ?_)
    exact continuous_const.add ((Bands.sends _).comp (ht j))
  exact (Poly.part_cont _).comp he

variable (k N p : ℕ) (i : Row X)
abbrev Copies := Site (C.side (Y.B.side k) p)
-- include N-index of fine tiling for the *hands*. Use orientation in all bound hypotheses.
def free (c : AxisX X) (h : Y.B.side k≤N) (u : Copies Y k p) :=
    Marks.atHand (center C.S p h 0) u (Y.cumulant k i c)
lemma flat_free (c h j) : Marks.part (free Y k N p i c h j) ∅=0 := Marks.at_zero (Y.cumulant k i c) _ _ (Y.none ..)

section
variable (c : AxisX X) {l : ℕ} {Z : Type*} (B : Wire C (Y.B.side k) (Y.B.depth k) N p)
variable {H : Rep G (C.side l p)} {y : Copies Y k p × Mark X i → Site (C.side l p)}
variable (A : Heads H.p y G)
variable (F : Original H y (Marks.all (Copies Y k p × Mark X i)))
variable (L : Atoms H.p (Marks.all (Copies Y k p × Mark X i)) y G Z)

/-- Hypotheses for restoring *uncorrected* density. Need vacuum and multiple
insertions valued together. `out` assigns main uncentered reading per cube,
on its good mask; `near` compares the actual reading with free connected values,
also on that mask. `K` budgets here do not need W, only w. All mark tags and
W-scale signs fixed in all reads before applying. κ_old for K includes any
strengthening for reserves required (no automatic flag gain).

All reals, l actual calendar level, length in native lattice uses `M=H.p.B`.
X/K support exponent `a` can be any selected at this invocation, consumed
along earlier estimates as indicated. Old atoms need budget even with
indicator failures. Threshold movement already accounted before `out`.
Numbers have no hidden dependence on number of cells. Need uniformly
usable bounds over N,p and compatible rates/thresholds for applications.
Here cost tests on data at one N,p.
-/
structure Meeting (ht : Y.B.side k≤N) (hp : l≤N)
    (w W D κ b η ζ a J R : ℝ) (q₀ m : ℕ) : Prop where
  start : H.eval=B.vacuum l hp
  out U : B.station ht hp (uncorrected Y i c k N p) U=(Real.exp (H.exponent U):ℂ) •
    (Poly.pass (L.sum U+∑ j, A.uncenter j U) * ∑' z, UnionK.oldEval F z U)
  uniform j : Poly.price (fun _=>1) (free Y k N p i c ht j)≤D
  near j t : t.Nonempty → ∀ U : Config G _, Healthy H.p.threshold (A.sites j) U →
    ‖Marks.part (A.look j U-free Y k N p i c ht j) t‖ ≤ η
  cash : 0 < w
  restores : w ≤ W
  room : 1 ≤ W
  covers : ∀ j, coverNumber H.p.B (A.sites j) ≤ q₀ ∧ (A.sites j).card ≤ m
  tight : ∀ j s : Copies Y k p,j≠s → ∀ x∈ A.sites j,∀ z∈ A.sites s,H.p.B^2≤separation x z
  large : 8 ≤ H.p.B
  old : ∃ T : ℕ → Poly (Marks.all (Copies Y k p × Mark X i)),
    (∀ k U, Width.Covered (F.value k U) (T k)) ∧
    (∀ i s, Marks.part (T i) s ≠ 0 → ∀ x∈s, y x∈oldSites H i) ∧
    Ac.Hit (oldSites H) H.p.B (fun i => Poly.price (fun _=>w) (T i)) (a+2) κ
  radii : L.Cost (fun _=>w) H.p.B (a+1) b
  intra : ∃ g : Z→ℝ, (∀ i, ¬L.mixed i → 0 ≤ g i ∧ ∀ U : Wilson.Config G _,
    Healthy H.p.threshold (L.sites i) U → ‖L.H i U‖ ≤ g i) ∧
    (∀ x, SumBudget (fun j => if x∈(L.tag j).val ∧ (Atoms.across L j).card<2 then
      Poly.toll (fun _=>W) (L.tag j)*g j*emit H.p.B a (L.sites j) else 0) ζ)
  stable : (64:ℝ)*(Real.log (W/w)*Fintype.card (Mark X i)) ≤ H.p.B
  entropy0 : Real.log (W/w)*Fintype.card (Mark X i)+(a+1)*q₀+R ≤ J
  entropy1 : 64*J ≤ H.p.B
  scale : 1+ W^Fintype.card (Mark X i)*(Real.exp D+1) ≤ Real.exp R
  positive : 0≤κ ∧ 0≤ η ∧ 0≤ a ∧ 0 ≤ J
  green :
    (H.p.B+H.p.B+1:ℕ)^4 * ((1+(m:ℝ))*Real.exp J*κ) ≤ 1

abbrev rewardE (A : Type*) [Fintype A] [DecidableEq A] (a b c W η : ℝ) (q₀ : ℕ) :=
    (b+c)+Fintype.card (Heads.Tags A)*(W^Fintype.card A*η*Real.exp (a*q₀))
abbrev rewardK (J κ : ℝ) (m : ℕ) := Real.exp ((1+(m:ℝ))*Real.exp J*κ)-1

/-- The new K representation including all coefficients of the correction,
on the **same** comparison image so far. Price through restored W on
all supports at this level; *no* claim of the next steps already. -/
theorem print {ht hp w W D κ b η ζ a J R q₀ m} [Countable Z]
    (U : Meeting Y k N p i c B A F L ht hp w W D κ b η ζ a J R q₀ m) :
    (Pad.enlarge H).eval=B.vacuum l hp ∧
    ∃ M : Bands (Marks.all (Copies Y k p × Mark X i)) (Pad.enlarge H),
      M.origins=y ∧ (M.units=0) ∧ M.density=B.station ht hp (Y.pattern k N p i c) ∧
      Further M (fun _=>W) H.p.B a 0 (rewardE (Mark X i) a b ζ W η q₀) (rewardK J κ m) := by
  classical
  let f := free Y k N p i c ht
  let e := flat_free Y k N p i c ht
  let Q := A.issues f e
  obtain ⟨T,hT,hA,hK⟩ := U.old
  have hc i : 0 ≤ Poly.price (fun _=>w) (T i) := Poly.nonnegative (fun _=> U.cash) _
  let C' (i : Copies Y k p) := Width.up (Marks.into (Poly.pass (-f i)-1) i)
  let V := Sum.elim T C'
  have hE i W' : Covered (UnionK.value F Q i W') (V i) := by cases i; exacts [hT _ _,Heads.issueCost f A e _ _]
  obtain ⟨hκ,hη,ha,hJ⟩ := U.positive
  have hW : 0 < W := U.cash.trans_le U.restores
  have hN i : 0 ≤ UnionK.faceBill V (fun _=>W) Q i := mul_nonneg (Poly.nonnegative (fun _=>hW) _) <|
    Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (Poly.nonnegative (fun _=>hW) _)
  let q := (1+(m:ℝ))*Real.exp J*κ
  have hq : 0≤q := by unfold q; positivity
  have hv : Ac.Hit (UnionK.inflate Q) H.p.B (UnionK.faceBill V (fun _=>W) Q) (a+1) q := by
    have hk i : 1+Poly.price (fun _=>W) (V (Sum.inr i)) ≤ Real.exp R :=
      (add_le_add_right (Heads.payable f _ U.room D U.uniform i) 1).trans U.scale
    apply UnionK.swollen Q m hN (Real.exp_pos _).le hκ (fun i => (U.covers i).2) _ hK
    intro j
    exact UnionK.remap Q V U.cash U.restores ha q₀ _ hJ U.large U.tight (fun i => (U.covers i).1) hk
      A.covers (hA _) U.entropy0 U.entropy1
  obtain ⟨T',hp',hφ⟩ := UnionK.rigid F Q _ hE (UnionK.fiscal V (fun _=>hW) ha hv hq U.green)
  let S := L.append (A.collect f)
  haveI : Countable (Z ⊕ Copies Y k p × Heads.Tags (Mark X i)) := inferInstance
  haveI : Nonempty (Mark X i) := ⟨0⟩
  have H' := A.budget f η U.room hη a ha (fun i=> (U.covers i).1) (fun j U' h t ht => U.near _ _ ht _ h)
  obtain ⟨s,h,hv⟩ := U.intra
  have hu := L.rest U.cash U.restores U.radii A U.large U.tight U.stable s h hv
  let MM := Prepare.construct (UnionK.issue F Q) S
  refine ⟨(funext (Pad.unchanged H)).trans U.start,MM,rfl,rfl,funext fun x => ?_,
    Prepare.after _ _ (fun _=>hW) hp' hφ (L.liquidity (A.collect f) _ hu H') ha⟩
  have htau := B.station_one (Poly.pass (-Y.cumulant k i c)) (uncorrected Y i c k N p)
    (regular Y i c k N p) ht hp x
  let t := Cells.center C.S p ht (0 : Site (C.side N p))
  have hF (j : Copies Y k p) : Marks.into (Marks.atHand t j (Poly.pass (-Y.cumulant k i c))) j=
      Marks.into (Poly.pass (-f j)) j := by
    have hs : Marks.part (-f j) ∅=0 := by change -Marks.part (f j) ∅=0; rw [show Marks.part (f j) ∅=0 from e j,neg_zero]
    rw [Marks.pass_into _ _ hs,show Marks.into (-f j) j = -Marks.into (f j) j from map_neg (Marks.emb j) _]
    exact Marks.sign _ _ _ (Y.none ..)
  change (construct (UnionK.issue F Q) S).density x=B.station ht hp (fun X => _*uncorrected Y i c k N p X) x
  rw [Prepare.evaluated, show S= L.append (A.collect f) from rfl]
  change (Real.exp (H.exponent x) : ℂ) • (Poly.pass ((L.append (A.collect f)).sum x)* _) = _
  rw [Atoms.sum_append _ _ _ (Atoms.summablePortions _ (fun _=>hW) hu ha _) (Atoms.summablePortions _ (fun _=>hW) H' ha _),
    Heads.together _ _ e x, UnionK.post_sum, ← UnionK.rassemble _ _ _ (UnionK.assess F hT (fun _=>U.cash) hK (by linarith) _),htau,U.out]
  have hV : ∏ j:t.Cell, Marks.into (Marks.atHand t j (Poly.pass (-Y.cumulant k i c))) (show Site (C.side (Y.B.side k) p) from j) =
      ∏ j : Copies Y k p, Marks.into (Poly.pass (-f j)) j := Finset.prod_congr rfl fun i _ => hF i
  rw [hV,Algebra.mul_smul_comm,← mul_assoc _ _ (tsum ..), Heads.scale _ _ e x (L.sum x) (L.no_unit (fun _=>hW) hu ha _)]
  rw [mul_assoc _ _ (∑' z, UnionK.oldEval F z x),mul_comm _ (∏ i, (1+Q.value i x))]; rfl
end
end intermediate
end YM.Push.Corrected.Endpoint
