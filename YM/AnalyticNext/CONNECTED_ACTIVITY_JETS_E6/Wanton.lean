import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Coven
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unified

/-!
# Whole compulsory product locality incl `A` seeds and charges when given

`A` address fixed. Existence neither changed by packet merging elsewhere
nor inferred from optional U choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Borough
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {x : Site c} {X X' : Coat T F} {a d : ℕ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G} {L : ℕ}
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x)
variable {A : Stores S} (he : A.dome (500*X.B) ⊆ Z)

include he in
private lemma expands (x : Site c) (hk : x∈A.dome d) (ha : d≤400*X.B) : Cleanroom Z (50*X.B) x :=
    fun _ hi=> he (touch_extend hk (by omega))
include H p he

private lemma surf (b : ℝ) :
    let f z i:= if mandatory A X.B i then z i else (1:ℝ)
    ∏ i, f (X.rawStorm (X.liftA R.beta w) b A R k) i = ∏ i,f (X'.rawStorm (X'.liftA R.beta v) b A R k') i := by
  intro f; apply prod_congr rfl; intro i _; unfold f; split
  next h =>
    obtain ⟨y,hk,hv⟩ := Finset.not_disjoint_iff.mp h
    have hr := expands he y hk (show 300*X.B ≤ 400*X.B by omega)
    apply H.ushers p A A i _ b (fans hr ?_)
    · rcases i with i|i|i
      · exact Iff.rfl
      · exact Iff.rfl
      exact True.intro
    rw [separation_comm]; have he := alarm_base S i y hv; have hx : 100≤X.B := p.sight.1; omega
  rfl

lemma checks : X.existSeeds A 300 ↔ X'.existSeeds A 300 := by
  unfold existSeeds; rw [← H.B]
  have hp i (hi : i∈A.place) := H.places _ (he (halo_subset _ _ hi))
  refine and_congr ⟨fun h i hi=> (hp i hi).1 (h hi), fun h i hi=> (hp i hi).2 (h hi)⟩ ?_
  have hz i (hi : i∈A.dome (300*X.B)) : i∈RG.flags (Pressure.temp X.x) X.V ↔ i∈RG.flags (Pressure.temp X'.x) X'.V := by
    rw [← H.weather]
    exact H.marksOut p _ i (fun j hj => expands he i hi (by omega) j (hj.trans (by omega)))
  exact forall_congr' fun i => forall_congr' fun hi => by rw [hz i hi]

private lemma turbine (a : ℝ) (Ñ : ChartRatio G) :
    X.steamLog R Ñ a A (X.liftA R.beta w) = X'.steamLog R Ñ a A (X'.liftA R.beta v) := by
  let U:=X.liftA R.beta w; let V:=X'.liftA R.beta v
  have hg s i (hk : i∈posted (turnStore s A) (200*X.B)) :
      X.debit U s i=X'.debit V s i ∧ X.extracted X.μ s i=X'.extracted X'.μ s i := by
    have hv := (Channel.rotates_dome ..).mp (mem_filter.mp hk).2
    obtain ⟨hc,-,hz⟩ := H.rowWorks p (s,i) (fun j hj=> expands he (s.act (lead S i)) hv (by omega) j (hj.trans (by omega)))
    exact ⟨hc,hz⟩
  have hh s : X.assigned A U s=X'.assigned A V s := by
    unfold assigned; rw [← H.B]; refine sum_congr rfl fun i hi=> (hg _ _ hi).1
  have ht : X.far_bills A=X'.far_bills A := by
    unfold far_bills; rw [← H.B]; apply congr_arg averaged; funext s; exact sum_congr rfl fun i hi=> (hg s _ hi).2
  let Y:=A.dome (304*X.B)
  have hx : 100 ≤ X.B := p.sight.1
  have hn i (hi : i∈ visit A (200*X.B)) : X.condensation i=X'.condensation i := H.boxes p i (by
    have ht := lives_in i A (mem_filter.mp hi).2
    intro j hj; exact expands he (atEdge S i) ht (by omega) j (hj.trans (by omega)))
  have hy i (hi : i∈X.plaza Y) : X.gentry Ñ a U i=X'.gentry Ñ a V i := by
    obtain ⟨x,hx',he'⟩ := Finset.not_disjoint_iff.mp (mem_filter.mp hi).2.2
    exact H.vale p (fans (expands he x hx' (by omega)) (by
      have hv := stride i he'; unfold distAt at hv; omega)) Ñ a
  unfold steamLog; rw [ht,show X.quoteNear A U = X'.quoteNear A V from congr_arg averaged (funext hh)]
  unfold pens; rw [← H.B, ← H.passes p Y (fun i hi j hj => expands he i hi (by omega) j (hj.trans (by omega)))]
  rw [Finset.sum_congr rfl hn, Finset.sum_congr rfl hy]

lemma papyrus (a W : ℝ) (Ñ : ChartRatio G) : X.Pack R Ñ k W a A (X.liftA R.beta w)=X'.Pack R Ñ k' W a A (X'.liftA R.beta v) := by
  unfold Pack; rw [H.checks p he]; split
  next hE =>
    let U:=X.liftA R.beta w; let V:=X'.liftA R.beta v
    have hp := X.forceds A R k W U
    have hr := X'.forceds A R k' W V
    change (_=(Contract.order .. * _)* _) at hp hr
    let f := (A.dome (304*X.B))
    have hb : A.dome (304*X'.B)=f := by rw [← H.B]
    unfold steam; dsimp only; rw [H.turbine p he a Ñ,hb, ← H.enforces p f (fun i hi j hj =>
      expands he i hi (by omega) j (hj.trans (by omega)))]
    congr 1
    -- reassoc multipliers
    rw [mul_assoc] at hp hr; rw [mul_assoc,mul_assoc, ← hp,mul_assoc,mul_assoc, ← hr]; rw [← H.B]; exact congr_arg (Real.exp _ * ·) (H.surf p he W)
  rfl
end YM.ConnectedActivityE6.Borough
