import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Quires
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Shawl
/-!
# All log-head and Ember catalog costs at a Π. W moves with β. Does not
 consume Stock via this neglect. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {Pt : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G Pt} {o : Target.Order G W} {R I : RG.Rep G f} {P : Facing R I}
    {p μ C v M d r D K' : ℝ} {i : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} (Ξ : Utopia H i v d r D χ)

def films (c f : Side) (w : ℕ→ℝ) (x:LogIndex c f):= match x with
  | .inl (.inl i) => w i
  | _ => 0
lemma filmed {w : ℕ→ℝ} (h : SumBudget w M) : SumBudget (films c f w) M:= by
  have he i : 0 ≤ films c f w i := by unfold films; split; exact h.1 _; exact le_rfl
  let F : ℕ ↪ LogIndex c f:= Embedding.inl.trans Embedding.inl
  apply Beam.wallet (f:=films c f w) F h; rintro (s|s) h
  · rcases s with s|s; · exact False.elim (h ⟨s,rfl⟩)
    rfl
  rfl
local notation "u" => coin Ξ
local notation "Y" => Q.table
include Ξ
theorem feather : ∃ K: ℝ,0 ≤ K∧∀ (I : RG.Rep G f) (a b : ℕ→ℝ) (t:ℝ), (Equalized (Y) R I a b t) → t ≤ 1 → ∀ {F : Forest S.ratio} (X:Coat T F), X.width=o.K→ X.x=p→ X.manifest→ X.χ=χ→∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (z:Air f G) (U:E→ Config G c) (V:E→ Directions G f) (Z:E→Air f G) (x:E),
    Mode U x i v→ Clutch X z o.a R.beta d x i U V Z→∀ (s:LogIndex c f) (k:Finset ℕ), Healthy (Pressure.temp X.x) (H.supportP (logKey S s)) X.V →
      let W' B y:= wraps T X R.beta o.a W Q.table y Q.halo B k z U V Z (logKey S s)
      Brush i (K*(films c f a s+t*u (logKey S s))) 1 (W' I (low R I) - W' R 1) x := by
  obtain ⟨g,hG,hH⟩:= lint S χ p o.a (mul_pos o.large H.laws.data.room.fiery) i d
  let k:= ∑' x, u x; have h':0≤k:= tsum_nonneg (coin_pos Ξ); have hk' x : u x≤k:= Summable.le_tsum (retail Ξ) _ (fun i _=> coin_pos Ξ _)
  obtain ⟨B,hB,hb⟩:= profits Ξ
  let t:=g+B; have ht : 0 ≤ t:= by linarith only [hB,hG,show g+B=t from rfl]
  let K:= t*(1+k); have hK :0≤K:=by unfold K; positivity
  obtain ⟨D,hD,hd⟩:= confound i h' hK
  refine ⟨D*t,mul_nonneg hD ht,?_⟩; intro I a b p' H' hI F X hQ hx hM hχ E _ _ _ z U V Z x h he s w hs g'
  let k':= logKey S s
  let L:= low R I
  let V':= X.input (worldZ X R.beta z)
  have hΨ:= hb X E z U V Z x s hQ hx hM hχ h he hs
  let fX j:= logMoment (vary X (U j)) o.a R (Y) (V j) V' (Z j) s; let f' j:= logMoment (vary X (U j)) o.a I (Y) (V j) V' (L • Z j) s
  have hm : g' R 1= up fX:= funext fun i=> by unfold g' wraps; rw [one_smul]; rfl
  have hV := sung X Ξ z U V Z x hQ hx hχ hM h he w k' hs; change Brush i _ _ (g' R 1) _ at hV; rw [hm] at hV
  have hy:= H'.fund_pos; have hT: SumBudget (films c f a: LogIndex c f → ℝ) p':= filmed H'.ae
  let y : ℝ := films c _ a s+p'* coin Ξ k'
  have h : Brush i (t*y) 1 (f'-fX) x:= by
    by_cases hk: oldVac c _ s
    · let r':= if flips c _ s then L^2-1 else 0; have hh: r'+1=(if flips c _ s then L^2 else 1):= by unfold r'; split_ifs<;> ring
      have H : |r'| ≤ p':= by unfold r'; split; exact H'.heat; simpa only [abs_zero] using hy
      have he:f'-fX=(fun i=> r' • fX i):= by
        funext i
        change logMoment (vary X (U i)) _ I _ _ _ (low R I • Z i) s-fX i=r'*fX i; unfold fX; rw [flicker o.a H'.toFacing _ _ _ _ _ _ hk, ← hh]; ring
      rw [he]; apply (hΨ.smul r').climb _ le_rfl
      refine (mul_le_mul_of_nonneg_right H (mul_nonneg hB (coin_pos _ _))).trans ?_; unfold y; change _ ≤ t* (films c _ a s + p'*u k')
      have hT:= hT.1 s; have hv: 0 ≤ p' * coin Ξ k':=by have hp:= coin_pos Ξ k'; positivity
      calc _ = B * (p' * coin Ξ k') := by change p'*(B*coin Ξ k')=_; ring
           _ ≤ t * (films c _ a s + p' * coin Ξ k') := by gcongr; linarith only [show g+B=t from rfl,hG]; exact le_add_of_nonneg_left hT
    unfold oldVac at hk; push Not at hk; obtain ⟨j,rfl⟩:=hk
    let S' :=X.plaza (Raw.space T 0 X.B R (.inl j)); let N:= H'.toFacing; have he' := hH F X hχ hx E R.beta _ _ _ _ _ he S'
    let c':= R.activities.regularOccurrence R.p j V' - I.activities.regularOccurrence I.p j V'
    have hC:|c'|≤ a j:= H'.high _ _
    apply ((he'.smul c').climb _ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
    · apply le_trans (mul_le_mul_of_nonneg_right hC (zero_le_one.trans hG)); change a j*g≤t*(a j+p'*_); rw [mul_comm (a j)]; have hf:0 ≤ a j:= H'.ae.1 j; have ht' := (show 0 ≤ p'*coin Ξ k' from mul_nonneg hy (coin_pos _ _))
      apply mul_le_mul (by unfold t; linarith) (le_add_of_nonneg_right ht') hf ht
    change -I.activities.regularOccurrence I.p j V' * X.enforce (2*o.a) (V i) (X.plaza (Raw.space T 0 X.B I (.inl j)))- (- R.activities.regularOccurrence R.p j V' * X.enforce (2*o.a) (V i) S') = c'*X.enforce (2*o.a) (V i) S'
    unfold c' S'; rw [← location H'.toFacing]; ring
  have he' := hd E x fX f' _ _ hV h (hk' _) (show t*y ≤ K from mul_le_mul_of_nonneg_left (add_le_add ((budget_single hT _).trans hI) ((mul_le_of_le_one_left (coin_pos _ _) hI).trans (hk' _))) ht)
  rw [hm]; exact he'.climb (le_of_eq (by change t*y*D=D*t*y; ring)) le_rfl
end YM.PhysicalNext.Repeat.Alabaster
