import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Caps
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inherited
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mean
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rewards
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tax

/-!
# Short exponent family (remaining row energy & paired log and Haar)

Signs stored as in integrand (= means use exp(Short) not - when
forming 1+h). Subtraction ends at actual calibrated mean in β.
Use masks gamma for U-reads, not requiring hard membership before
estimating `short`. Geometric support in shortBand factor extends with
halo parameter l, no eligibility cut count here. Do not pay a volume
term as though it were local. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y b : ℝ} {L : Side}

variable (X : Coat T F)

abbrev Stream (c f : Side) := Signed × Spot c f
abbrev Miniature (c f : Side) := Stream c f ⊕ Bond f ⊕ Bond f

def rowSite (S : StepData c f) (i : Stream c f) := i.1.act (lead S i.2)
def caption (S : StepData c f) : Miniature c f → Site c := Sum.elim (rowSite S) (Sum.elim (atEdge S) (atEdge S))
def sleeve (S : StepData c f) (B l : ℕ) : Miniature c f → Support c :=
    Sum.elim (fun i => Animals.neighbors (l*B) (rowSite S i)) (Sum.elim (town S B l) (town S B l))

def voyage (A : Stores S) (d : ℕ) (i : Bond f) := ¬Disjoint (A.dome d) (ends S i)
def visit (A : Stores S) (d : ℕ) := univ.filter (voyage A d)

lemma lives_in (i : Bond f) (A : Stores S) {d : ℕ} (h : voyage A d i) : Inside (atEdge S i) A (d+1) := by
  obtain ⟨x,hx,he⟩ := Finset.not_disjoint_iff.mp h
  exact touch_extend hx (by gcongr; exact stride i he)
lemma without (i : Bond f) (A : Stores S) {d : ℕ} (h : ¬voyage A d i) : ¬ Inside (atEdge S i) A d := fun hp =>
  h <| Finset.not_disjoint_iff.mpr ⟨_,hp,center_end _⟩

lemma touch_price (S : StepData c f) (d : ℕ) (A : Stores S) : (visit A d).card ≤
    A.shares * Animals.ballCost ((d+1)+1) * Itinerary.density S.patch.L := offset_bound (S:=S) (perch S) _ _ _ fun i hi => lives_in i A (mem_filter.mp hi).2

/-- Full row exponent minus compulsory energy/affine cut, including the
centered *residual square* outside main integral. -/
def speck (u : Directions G f) (β a : ℝ) (p : Stream c f) :=
    if Inside (rowSite S p) X.seeds (200*X.B) then 0 else
      -β*Raw.orientation*(X.enforce (2*a) u (X.booth (rowSite S p)) * X.light u p.1 p.2+
        X.extracted X.μ p.1 p.2)

def undercurrent (p : Bond f) := if voyage X.seeds (200*X.B) p then 0 else X.condensation p

def solo (u : Directions G f) (Ñ : ChartRatio G) (a : ℝ) (i : Bond f) :=
    if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then X.gentry Ñ a u i else 0

def Short (u : Directions G f) (Ñ : ChartRatio G) (β a : ℝ) : Miniature c f → ℝ :=
    Sum.elim (X.speck u β a) (Sum.elim X.undercurrent (X.solo u Ñ a))

/-- Intact sector BEFORE any optional drops. E Drow stencil alive through
radius including at boundaries, even if X.seeds empty. -/
lemma original (h : Room P S T X.x) (p : Stream c f) (u : Directions G f) {W : ℝ}
    (he : Seeded X.seeds (X.input u) X.k X.V X.x W) (ha : Alive S (X.input u) X.k)
    (ht : ¬ Inside (rowSite S p) X.seeds (200*X.B)) : X.light u p.1 p.2=X.debit u p.1 p.2 := by
  rcases p with ⟨s,b | b⟩
  swap; · rfl
  let V := pull s 0 X.V
  let U := pull s 0 (X.input u)
  let k := choice s X.k
  have hf : ¬Inside (S.ratio.parent b.1) (turnStore s X.seeds) X.B := fun H => ht <|
    Corona.halo_mono (show X.B ≤ 200*X.B by omega) (Finset.Subset.refl _) ((rotates_dome ..).mp H)
  have hm := funds_branch h.accepted
  have hk : Alive S U k := by
    simpa only [Alive,U,k, (carry s hm X.k (X.input u)).1] using! ha
  have hh : Interior S X.x W (S.ratio.parent b.1) X.B U k V := Interior.of_actual U V k _ (pull_seeded s hm he) hk hf
  have hp : X.t / 2 ≤ X.t := by linarith [show 0<X.t from h.fiery]
  have hb : PathData.kept T.high X.t b.1 U := by
    intro p; by_cases ht' : X.t*Real.exp (separation b.1 p.1 / T.high.relaxation) < 2
    · have he := h.laneU _ ht'
      apply ((hh.fine p ((Work.E04.parent_separation S.ratio b.1 p.1).trans (by change _ ≤ radiusB X.x; omega))).trans hp).trans
      exact le_mul_of_one_le_right h.fiery.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.high.radius_pos.le))
    exact (G.chord_le_two _).trans (le_of_not_gt ht')
  unfold light debit; dsimp only
  rw [show X.energy u s (.inl b)=T.workF X.R U V X.t (Pressure.temp X.x) b from rfl,
    splitF T X.x U V k b ((hh.fine b (separation_self _ ▸ Nat.zero_le _)).trans hp) hb]; rfl

lemma lamplight (p : Spot c f) (s : Signed) {u : Directions G f} {C : ℝ} (_hC : 0≤C)
    (he : ∀ i∈parents p, ‖X.realPath s i u‖ ≤ C) : |X.extracted u s p| ≤ 2*(C^2/2) := by
  rw [abs_of_nonneg (X.extracted_nn ..)]
  apply le_trans (b:= ∑ _i∈parents p, C^2/2)
  · apply Finset.sum_le_sum; intro i hi; change X.surcharge s i u ≤ _
    unfold surcharge; split
    next hk => gcongr; exact he i hi
    next ht => positivity
  rcases p with b|b; · simp [parents, two_mul]
  rcases b with j|j
  · simp only [parents,sum_singleton]; nlinarith
  simp only [parents,sum_empty]; positivity



theorem minute (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (M V H : ℝ) (hM : 0<M) (hH : 0<H)
    (h : Torch η r Q) {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) :
    ∃ E : ℝ → ℝ, Rate G L (-(1/2)) E ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
      (F : Forest S.ratio) (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Rotator P L η r Q V X →
      Rotator P L η r Q V X.blank → (∀ z, Rotator P L η r Q V (X.rinse z)) → Stamp T →
      (∀ v, Maximum M T x v) → X.manifest → 0 ≤ E x ∧
      ∀ u i, ∀ (β : ℝ), 0<β → β ≤ 2*betaF G x L → |X.Short u Ñ β H i| ≤ E x := by
  obtain ⟨E,hE,H₁⟩ := condenses P L D hd η r Q V
  obtain ⟨C,hC,h₃⟩ := germ_charge hÑ L hH
  obtain ⟨A,hA,h₂⟩ := pressure_mean P D hd L η r Q V h
  let b x := (2*(2*H))*Pressure.fiery G x L
  obtain ⟨J,hJ,h₄⟩ := light_costs P L D hd M hM (w:=b) (Rate.flame.mul_left _)
    (Eventually.of_forall fun x => mul_nonneg (by positivity) (by unfold Pressure.fiery temp; positivity))
  let C₁ x := C * Pressure.fiery G x L
  let V x := J x + (A x)^2
  let W x := 2*betaF G x L*V x
  have hw : Rate G L (-(1/2)) W := by
    convert ((Rate.hat.mul_left 2).mul (hJ.add ((hA.pow 2).weaken (by norm_num)))) using 1; norm_num
  let B x := E x + C₁ x + W x
  refine ⟨_,(hE.add (Rate.flame.mul_left C)).add hw,?_⟩
  filter_upwards [H₁,h₃,h₂,h₄,Delay.shift_pos G L] with x h₁ h₃ h₂ h₄ hY c f S T F X he hS hL hr hp hA hd hv hX
  obtain ⟨hg,hC⟩ := h₁ c f S T F X he hS hL hr hX hA hp
  have hm := hr.room
  subst x
  have hz := h₃ c f S T F X rfl hL hm.fiery
  obtain ⟨hs,hA⟩ := h₂ c f S T hS hL hd F X rfl hr hX
  have he := h₄.1
  have ht : Pressure.fiery G X.x L=X.t := hL ▸ rfl
  have hx : 0 < H*X.t := mul_pos hH hm.fiery
  have hC₁ : 0≤C₁ X.x := mul_nonneg (by positivity) (ht ▸ hm.fiery.le)
  have hV : 0 ≤ V X.x := add_nonneg he (sq_nonneg _)
  refine ⟨(by change 0 ≤ B X.x; have h := mul_nonneg (b:=V X.x) (show 0≤2*betaF G X.x L by positivity) hV; unfold B W; linarith),fun u i β hβ hQ => ?_⟩
  have hW : 0 ≤ W X.x := mul_nonneg (hβ.le.trans hQ) hV
  have hhT : C*X.t=C₁ X.x := by unfold C₁; rw [ht]
  change |X.Short u Ñ β H i| ≤ B X.x
  rcases i with p|i|i
  · let o := rowSite S p; unfold Short; dsimp only [Sum.elim]; unfold speck; split
    next he' => rw [abs_zero]; unfold B; linarith
    next he' =>
      have hx' : ¬Inside o X.seeds (11*X.B+1) := clear he' (by change 11*X.B+1+separation o o ≤ _; rw [separation_self]; have hh : 100 ≤ X.B := hm.sight.1; omega)
      have ho : Clean X.V X.x o X.B := (clean_far X.seeds X.V hX hx').shrink (by rw [separation_self]; omega)
      let g := X.enforce (2*H) u (X.booth o)
      have hl : |g*X.light u p.1 p.2| ≤ J X.x := by
        by_cases hf : g=0
        · rwa [hf,zero_mul,abs_zero]
        have hf' : X.selected p.1 p.2 := clear hx' (by change 6*X.B+separation o o≤_; rw [separation_self]; omega)
        have hu : Grafted X.V (X.input u) (X.signal u) o X.B (b X.x) S := by
          refine X.distant u o (by unfold b; rw [ht]; have hf := hm.fiery; positivity) hx' (fun j hj hk => ?_)
          unfold b; rw [ht]; exact X.protection _ (show 0<2*H*X.t by rw [mul_assoc]; positivity) u hf _ (X.ages j o hk hj)
        rw [abs_mul,abs_of_nonneg (X.conserve ..).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (X.conserve (X.booth o) (2*H) u|>.2)).trans
          ((h₄.2 c f S T F X rfl hS hL hm u p.2 p.1 ho hu (hv _)).2 hf')
      have hX : |X.extracted X.μ p.1 p.2| ≤ (A X.x)^2 := by
        apply (lamplight X _ _ hs (fun i hi => ?_)).trans_eq
        · ring
        have ht : root S (p.1,i)=o := by unfold root; rw [cost_is_here i,(parent_iff i _).mp hi]; rfl
        apply hA (p.1,i)
        rw [ht]; apply clear he' (by change 30*X.B+separation o o≤_; rw [separation_self]; omega)
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hβ.le, abs_of_nonneg Raw.orientation_range.1.le]
      apply le_trans (b:=W X.x) _ (by unfold B; linarith)
      exact mul_le_mul ((mul_le_of_le_one_right hβ.le Raw.orientation_range.2).trans hQ)
        ((abs_add_le ..).trans (add_le_add hl hX)) (abs_nonneg _) (hβ.le.trans hQ)
  · change |X.undercurrent i| ≤ _; unfold undercurrent; split
    next hp => rw [abs_zero]; unfold B; linarith
    next hx =>
      have hy : ¬ Inside (atEdge S i) X.seeds (30*X.B) := clear (without i X.seeds hx) (by rw [separation_self]; omega)
      apply (hC i hy).trans; unfold B; linarith
  change |X.solo u Ñ H i| ≤ _; unfold solo; split
  next hu => apply (hz.2 ..).trans; rw [hhT]; unfold B; linarith
  next hu => rw [abs_zero]; unfold B; linarith
end YM.ConnectedActivityE6.Coat
