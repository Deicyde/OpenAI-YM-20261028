import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.CurrentL
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Locality of short priced factors
Compute assignment even on bad points. Complete query halos ensuring
esto charges. -/
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
variable {k k' : Finset ℕ} {w v : Air f G}
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x)
include H p
lemma boxes (b : Bond f) (he : Cleanroom Z (25*X.B) (atEdge S b)) : X.condensation b=X'.condensation b := by
  have hp := H.social (x:=atEdge S b) (a:=17*X.B) (fun i hi=> he i (by have hx : 100 ≤ X.B := p.sight.1; omega))
  cases isEmpty_or_nonempty G.ColorIndex with
  | inl h => simp [condensation,Batch.joint]
  | inr h => obtain ⟨z⟩ := h; exact hp.condensates p (b,z) rfl le_rfl

lemma intake (he : Cleanroom Z (30*X.B) x) : AgreeNear S.ratio.parent x (3*X.B) (X.input (X.liftA R.beta w))
      (X'.input (X'.liftA R.beta v)) := fun i hi=> H.quarters p (fans he (by change separation x (atEdge S i) ≤ _ at hi; omega))
lemma targeting (he : Cleanroom Z (30*X.B) x) : AgreeNear id x X.B (S.prediction (X.input (X.liftA R.beta w)) X.k)
    (S.prediction (X'.input (X'.liftA R.beta v)) X'.k) := by
  have hh : 100≤X.B ∧ 4* X.R+4+predReach S.patch ≤ X.B/100 := p.sight
  apply (H.social (x:=x) (a:=20*X.B) (fun i hi=> he i (by omega))).predicts x (by rw [separation_self]; omega) _ _
    ((H.intake p he).shrink (by rw [separation_self]; omega)) p
lemma rowWorks (i : Stream c f) (he : Cleanroom Z (30*X.B) (rowSite S i)) :
    let u:=X.liftA R.beta w; let u':= X'.liftA R.beta v
    X.debit u i.1 i.2=X'.debit u' i.1 i.2 ∧ X.light u i.1 i.2=X'.light u' i.1 i.2 ∧
      X.extracted X.μ i.1 i.2=X'.extracted X'.μ i.1 i.2 := by
  intro u u'; rcases i with ⟨s,i⟩
  let o:= lead S i; let t := s.act o
  have hh : 100 ≤ X.B := p.sight.1
  have hS : Zone X X' t (20*X.B) := H.social (x:=t) (fun j hj=> he j (by change separation t j≤_; omega))
  have hc (g b : Directions G f) (ht : ∀ j : Bond f, distAt S j t≤ X.B → X.Hot j → g j=b j) :
      X.extracted g s i=X'.extracted b s i := by
    unfold Coat.extracted; refine sum_congr rfl fun j hj=> ?_
    have hk := (parent_iff (S:=S) j i).1 hj
    have hy := hS.real p s j (by unfold t o; rw [cost_is_here j,hk]) (by omega) g b ht
    unfold surcharge; rw [hk,hS.shifting s i rfl (by omega),hy]
  have hz (i : Bond f) (hi : distAt S i t ≤ X.B) : Cleanroom Z (25*X.B) (atEdge S i) := by
    apply fans he; unfold distAt at hi; change separation t _+_ ≤_; omega
  have hT := funds_branch p.accepted
  let U:= X.input u; let U':= X'.input u'
  have hv : AgreeNear id o (radiusB X.x/2) (pull s 0 X.V) (pull s 0 X'.V) :=
    Zone.nearV s (hS.pay.shrink (by change separation t t + (X.B/2+1)≤_; rw [separation_self]; omega))
  have hp : AgreeNear S.ratio.parent o (X.B/2) (pull s 0 U) (pull s 0 U') := Zone.nearU S s
    ((H.intake p he).shrink (q':=t) (by change separation t t + (X.B/2+1)≤_; rw [separation_self]; omega))
  have hQ : AgreeNear id o (X.B/2) (S.prediction (pull s 0 U) (choice s X.k))
      (S.prediction (pull s 0 U') (choice s X'.k)) := by
    rw [(carry s hT _ _).2,(carry s hT _ _).2]
    exact Zone.nearV s ((H.targeting p he).shrink (q':=t) (by change separation t t+(X.B/2+1)≤ _; rw [separation_self]; omega))
  have hg := hc u u' fun j hj _=> H.house p (hz j hj) _
  dsimp only; unfold debit Coat.energy Coat.light; rw [← H.weather]
  exact ⟨congrArg₂ (· - ·) (broad p i hv hQ hp) hg, congrArg₂ (· - ·) (cloudy p _ _ _ hv hQ hp) hg,
    hc X.μ X'.μ fun j hj _=> (H.lodge p (hz j hj)).1⟩

lemma marquee (i : Stream c f) (a β : ℝ) (he : Cleanroom Z (400*X.B) (rowSite S i)) :
    X.speck (X.liftA R.beta w) β a i=X'.speck (X'.liftA R.beta v) β a i := by
  let q := rowSite S i
  have hp : 100≤ X.B := p.sight.1
  obtain ⟨-,hv,hb⟩ := H.rowWorks p i (fun j hj=> he j (by omega))
  let T := Animals.neighbors X.B q
  have ht := H.social (x:=q) (a:=350*X.B) (fun j hj=> he j (by change separation q j≤_; omega))
  have he' : ∀ j∈T, Cleanroom Z (30*X.B) j := by
    intro j hj; have hh : separation q j ≤ X.B := (Animals.neighbors_mem ..).mp hj
    apply fans he; change separation q j+_≤_; omega
  have hy : Inside (rowSite S i) X.seeds (200*X.B) ↔ Inside (rowSite S i) X'.seeds (200*X.B) := ht.covert q (by rw [separation_self]; omega)
  unfold speck booth; rw [← H.B,hv,hb,H.enforces p T he' (2*a)]; simp_rw [hy]; congr

lemma domeLight (b : Bond f) (he : Cleanroom Z (400*X.B) (atEdge S b)) : X.undercurrent b=X'.undercurrent b := by
  let q:=atEdge S b; have hp : 100≤X.B := p.sight.1
  have hT := H.social (x:=q) (a:=350*X.B) (fun j hj=> he j (by change separation q j≤_; omega))
  unfold undercurrent; rw [← H.B,hT.forward b (by change separation q q+_+_ ≤_; rw [separation_self]; omega),
    H.boxes p b (fun i hi=> he i (by omega))]
lemma occupied (b : Bond f) (he : Cleanroom Z (400*X.B) (atEdge S b)) :
    (b∈ X.plaza (X.seeds.dome (304*X.B)) ↔ b∈ X'.plaza (X'.seeds.dome (304*X'.B))) ∧ (X.Hot b ↔ X'.Hot b) := by
  let q:=atEdge S b; have hp : 100 ≤ X.B := p.sight.1
  have hT:= H.social (x:=q) (a:=350*X.B) (fun j hj=> he j (by change separation q j≤_; omega))
  have hf := hT.tides b (by change separation q q+1+_≤_; rw [separation_self]; omega)
  refine ⟨?_,hf⟩
  simp only [plaza,mem_filter,mem_univ,true_and]; rw [hf]; apply and_congr_right; intro _
  change voyage X.seeds _ _↔ voyage X'.seeds _ _; rw [← H.B]
  exact hT.forward _ (by change separation q q+1+_≤_; rw [separation_self]; omega)

lemma minuteL {l : ℕ} (hl : 500 ≤ l) (a : ℝ) (Ñ : ChartRatio G) (i : Miniature c f) (he : sleeve S X.B l i⊆ Z) :
    X.Short (X.liftA R.beta w) Ñ R.beta a i=X'.Short (X'.liftA R.beta v) Ñ R.beta a i := by
  have hF : 400*X.B ≤ l*X.B := Nat.mul_le_mul_right _ (by omega)
  rcases i with i|i|i
  · exact H.marquee p i _ _ (fun _ hi=> he ((Animals.neighbors_mem ..).mpr (hi.trans hF)))
  · exact H.domeLight p i (fun j hj => town_circle (S:=S) he j (hj.trans hF))
  have hh (b c) (hc : c ≤ 400*X.B) (hb : separation (atEdge S i) b≤c) : b∈Z := town_circle he b ((hb.trans hc).trans hF)
  obtain ⟨hp,hz⟩ := H.occupied p i fun j=>hh j _ le_rfl
  unfold Short solo; dsimp only [Sum.elim]
  simp_rw [hp,hz,H.vale p (fun j hj=> hh j _ (by omega) hj)]
end YM.ConnectedActivityE6.Borough
