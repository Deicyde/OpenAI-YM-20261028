import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Stamps on Borough, V-dependent kernel, complete route
Not assuming nonzero support or chord guards! -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Borough
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {x : Site c} {X X' : Coat T F} {a d B L : ℕ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G} {n : ℕ} {s t : ℝ}

private lemma backL (p : Bond f) (l : Itinerary f n) : town S B L p⊆ visited S B L p l := by
  cases n
  · exact Finset.Subset.refl _
  next n => exact Finset.subset_union_left
private lemma finalL (p : Bond f) (l : Itinerary f n) : town S B L (arrive p l)⊆visited S B L p l := by
  induction n generalizing p
  · exact Finset.Subset.refl _
  next n ih => exact Finset.Subset.trans (ih (Itinerary.next l) (Itinerary.after l)) Finset.subset_union_right
lemma combL (A A' : ℕ→Mat f G) (p : Bond f) (l : Itinerary f n) (he : visited S B L p l⊆Z)
    (hv : ∀ i (j j' : Bond f), town S B L j⊆ Z → town S B L j'⊆ Z → restrict (A i) j j'=restrict (A' i) j j') :
    combo p l A=combo p l A' := by
  induction n generalizing A A' p
  · rfl
  next n ih =>
    let i:= Itinerary.next l; let z:= Itinerary.after l
    have hp : visited S B L i z ⊆ Z := Finset.Subset.trans Finset.subset_union_right
      (show town S B L p ∪ _ ⊆ Z from he)
    rw [combo,combo,hv 0 p i ((backL p l).trans he) ((backL i z).trans hp),ih (fun k=> A (k+1)) (fun k=> A' (k+1)) i z hp (fun j=> hv (j+1))]
lemma plateCombo (H H' : ℝ→ℕ→Mat f G) (p : Bond f) (l : Itinerary f n) (he : visited S B L p l⊆ Z)
    (h : ∀ s i (j j'),town S B L j⊆Z → town S B L j'⊆ Z → restrict (H s i) j j'=restrict (H' s i) j j') :
    stamp H p l=stamp H' p l := by
  unfold stamp checkIn; simp_rw [combL _ _ p l he (h _)]

variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x) (he : 50≤L)
include H p he

lemma minable (i : Bond f) (hi : town S X.B L i ⊆ Z) : Zone X X' (atEdge S i) (30*X.B) := by
  have hp := Nat.mul_le_mul_right X.B he
  apply H.social; intro j hj; exact town_circle hi j (hj.trans (by have hr : 100 ≤ X.B := p.sight.1; omega))
lemma starA {j : Ledger f 3} (hi : receipt S X.B L 3 j⊆ Z) :
    ArmA X.shutter X.plate j= ArmA X'.shutter X'.plate j := by
  refine plateCombo _ _ _ _ hi fun s i l r hl hr=> ?_; ext m n
  change aSeq _ _ s i (l,m) (r,n)=aSeq _ _ s i _ _
  match i with
  | 0 => simp only [aSeq, Matrix.sub_apply]; rw [(H.minable p he l hl).plateL p (l,m) rfl (by omega)]
  | 1 => exact (H.minable p he r hr).inverse_w p (r,n) rfl _ (by omega) s
  | k+2 => simp only [aSeq, Matrix.neg_apply]; rw [(H.minable p he r hr).glideL p (r,n) rfl (by omega)]

lemma starS {j : Ledger f 1} (hi : receipt S X.B L 1 j⊆ Z) : ArmS X.shutter X.plate j= ArmS X'.shutter X'.plate j := by
  refine plateCombo _ _ _ _ hi fun s i l r _ hr=> ?_; ext m n
  change sSeq _ _ s i (l,m) (r,n)=sSeq _ _ s i _ _
  have hp : X.shreds (l,m) (r,n)=X'.shreds (l,m) (r,n) := (H.minable p he r hr).scrapsL p (r,n) rfl (by omega) _
  unfold shreds at hp; cases i <;> simp only [sSeq,hp, Matrix.smul_apply,Matrix.neg_apply]

lemma arches (i : Bond f) (hi : town S X.B L i⊆Z) (a : ℝ) :
    X.aperture R.beta w a i=X'.aperture R.beta v a i ∧ ∀ j:G.ColorIndex,w (i,j)=v (i,j) := by
  have hx := H.minable p he i hi
  have hF : Cleanroom Z (25*X.B) (atEdge S i) := fun _ hj => town_circle hi _ (hj.trans
    (Nat.mul_le_mul_right _ (show 25≤L by omega)))
  refine ⟨?_,fun j=> H.airs (i,j) (mem_filter.mpr ⟨mem_univ _,hF⟩)⟩
  unfold aperture; rw [hx.tides i (by unfold distAt; rw [separation_self]; have he : 100≤X.B := p.sight.1; omega),H.coin p hF]

lemma hats (i : Bond f) (hi : town S X.B L i⊆Z) (a : ℝ) : X.qfirst R.beta w a i=X'.qfirst R.beta v a i := by
  obtain ⟨hr,hj⟩ := H.arches p he i hi a
  have hx := H.minable p he i hi
  unfold qfirst qlinear; rw [hr]; apply congr_arg₂ (·*·) rfl; apply sum_congr rfl; intro j _; rw [hj];
  let b : Tubular f G := (i,j)
  apply congr_arg (v b * ·)
  have hg : (X.plate *ᵥ X.driftM) b=(X'.plate *ᵥ X'.driftM) b := by
    unfold mulVec dotProduct; refine sum_congr rfl fun q _=> ?_
    by_cases hp : separation (atEdge S i) (along S q) ≤ X.B/2
    · rw [(hx.tune_down (q:= along S q) (b:=17*X.B) (by omega)).driftL p q rfl le_rfl]
      dsimp only; rw [hx.plateL p b rfl (by omega)]
    have hu : X.B/2 < separation (along S b) (along S q) := lt_of_not_ge hp
    dsimp only; rw [X.span p b q hu,X'.span (H.weather ▸ p) b q (by rw [hx.B]; exact hu),zero_mul,zero_mul]
  unfold hatted; rw [Pi.smul_apply,Pi.add_apply, Pi.smul_apply,Pi.add_apply,hg,hx.billL p b rfl (by omega)]

lemma cable {i : Ledger f 2} (hi : receipt S X.B L 2 i⊆Z) (a : ℝ) : X.chain R.beta w a i=X'.chain R.beta v a i := by
  obtain ⟨hl,hk⟩ := H.arches p he _ ((backL i.2.1 i.2.2).trans hi) a
  obtain ⟨hc,hK⟩ := H.arches p he _ ((finalL i.2.1 i.2.2).trans hi) a
  have hg : combo i.2.1 i.2.2 (X.finale i.1)= combo i.2.1 i.2.2 (X'.finale i.1) := by
    refine combL _ _ _ _ hi fun t x y hu hv => ?_
    have hd := H.minable p he y hv; ext m n
    unfold finale; split
    next ht => change -(X.shreds _ _) = -(X'.shreds _ _); rw [hd.scrapsL p (y,n) rfl (by omega)]
    next hz => exact (H.minable p he x hu).plateL p (x,m) rfl (by omega) _
  unfold chain qunique circle; rw [hg,hl,hc]; dsimp only; simp_rw [hk,hK]

lemma fuelL {i : ChainIndex f} (hi : basisFoot S X.B L i ⊆ Z) (a : ℝ) : X.fuel a R.beta w i=X'.fuel a R.beta v i := by
  rcases i with i|i|i|i|i
  · unfold Coat.fuel; dsimp only [Sum.elim]; rw [H.starA p he (j:=i) hi]
  · unfold Coat.fuel shutter; dsimp only [Sum.elim]; rw [H.B,neutral X X' H.weather]
  · unfold Coat.fuel; dsimp only [Sum.elim]; rw [H.starS p he hi]
  · exact H.hats p he i hi a
  exact H.cable p he hi a
end YM.ConnectedActivityE6.Borough
