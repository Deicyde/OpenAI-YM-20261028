import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Governor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Motion

/-! # Keep actual packet branches; rotation identities on attempted tags

No running a character at each uses/pulling coarse Y to turn the link
where actually only the pin location moved. Fold and hold. Even off-likelihood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows Pulse Itinerary Control Window Mask
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}

section rotate
variable (s b)
lemma visits (A : Stores S) (r : ℕ) (i : Bond f) : i ∈ visit (Locations.book s b A) r ↔ diagram s b S i ∈ visit A r := by simp only [visit,mem_filter,mem_univ,true_and,travels]
lemma visiting (A : Stores S) (i : Site f) (n : ℕ) : i∈vias S (Locations.book s b A) n ↔ StepData.sendSites s (S.ratio.embed b) i ∈ vias S A n := by
  simp only [vias,mem_filter,mem_univ,true_and,Shell.Inside,Locations.dome_map]; rw [← Locations.parent_map]; rfl
lemma toured (u : ℝ) (V : Config G c) (i : Site c) : i∈RG.flags u (pull s b V) ↔ affine s b i∈RG.flags u V :=
  (display (StepData.sendSites s b) _ _).1 (Work.H03.flags_send ..).symm i
lemma atCost (A : Stores S) (i : Cell f) : i∈(Locations.book s b A).costs ↔ Locations.shiftFaces s (S.ratio.embed b) i∈A.costs := by simp [Locations.book]
lemma atA (A : Stores S) (i : Bond c) : i∈(Locations.book s b A).aisles ↔ StepData.sendBonds s b i∈A.aisles := by simp [Locations.book]
lemma atF (A : Stores S) (i : Site c) : i∈(Locations.book s b A).flags ↔ affine s b i ∈ A.flags := Finset.mem_map_equiv
lemma pin_wire (Q V : Config G c) (i : Bond c) : wire (pull s b Q) (pull s b V) i=wire Q V (StepData.sendBonds s b i) := by
  unfold wire; rw [Channels.read_back,Channels.read_back]; split
  · let a:=V (sendEdge s b i); let u:=Q (sendEdge s b i); change G.chord (a⁻¹*u⁻¹⁻¹)=G.chord (a*u⁻¹)
    rw [← G.chord_inv (a*u⁻¹),show (a*u⁻¹)⁻¹=a*(a⁻¹*u⁻¹⁻¹)*a⁻¹ by group,G.chord_conj]
  rfl
lemma movingMark (A : Stores S) (χ : Chi) (t : ℝ) (U : Config G f) (i : Cell f) : fine (Locations.book s b A) χ i t (pull s (S.ratio.embed b) U)= fine A χ (Locations.shiftFaces s (S.ratio.embed b) i) t U := by
  have hp : toll (pull s (S.ratio.embed b) U) i=toll U (Locations.shiftFaces s (S.ratio.embed b) i) := Face.send_price U i s (S.ratio.embed b) G.chord G.chord_inv fun k g=> G.chord_conj g k
  unfold fine; rw [hp]; dsimp only; exact if_congr (atCost ..) rfl rfl
lemma accepts_cost (R : Rep G f) (e : R.activities.Moves s (S.ratio.embed b)) (l : Finset ℕ) (U : Config G f) (i : Site f) : Contract.charges R l (pull s (S.ratio.embed b) U) i=Contract.charges R (e.kp.finsetCongr l) U (StepData.sendSites s (S.ratio.embed b) i) := by
  let p:=StepData.sendSites s (S.ratio.embed b)
  unfold Contract.charges
  have he : i ∈ Contract.covered R l ↔ p i ∈ Contract.covered R (e.kp.finsetCongr l) := by
    unfold Contract.covered; simp only [mem_biUnion]
    conv_rhs=> rw [← e.kp.exists_congr_right]
    simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv,Equiv.symm_apply_apply, e.forced_support]
    have hr : affine s (S.ratio.embed b)=p := rfl
    simp [hr]
  exact if_congr (and_congr (not_congr he) (toured ..)) rfl rfl

variable (k : S.Choices) (U : Config G f) (hp : S.patch.Branches S.kernel G)
include hp
lemma barNoise (A : Stores S) (χ : Chi) (t W : ℝ) (V : Config G c) (i : Bond c) :
    noise (Locations.book s b A) χ i t W (pull s (S.ratio.embed b) U) (Channels.ticket s b k) (pull s b V)=noise A χ (StepData.sendBonds s b i) t W U k V := by
  unfold noise; rw [S.prediction_channel hp]; unfold Channels.ticket; rw [Equiv.apply_symm_apply,pin_wire]; dsimp only; exact if_congr (atA ..) rfl rfl
lemma portSite (x : Site c) : Tags.siteMass (pull s (S.ratio.embed b) U) (Channels.ticket s b k) x=Tags.siteMass U k (StepData.sendSites s b x) := by
  let m := Channels.ticket s b k; have hh : S.withinSites s b m.1=k.1 := congr_arg Prod.fst ((S.withinChoice s b).apply_symm_apply k)
  unfold Tags.siteMass; rw [expandAt_pull,S.port]; apply congr_arg
  change _= S.patch.frameMass _ (expandAt (S.ratio.embed _) U) (k.1 (affine s b x))
  change S.patch.frameMass _ _ (m.1 x) = _; rw [← hh,S.port_site]; exact (S.patch.frames_channel hp ..).1
lemma portPin (x : Bond c) : Tags.pinMass (pull s (S.ratio.embed b) U) (Channels.ticket s b k) x=Tags.pinMass U k (StepData.sendBonds s b x) := by
  let v : S.Choices:= Channels.ticket s b k
  have hh: S.withinChoice s b v=k:= (S.withinChoice s b).apply_symm_apply _
  obtain ⟨x,i⟩:=x; unfold Tags.pinMass; apply congr_arg
  change S.patch.predictorMass _ (S.connector _ v.1 (x,i)) (v.2 _) = _
  rw [← hh]; change _=S.patch.predictorMass _ (S.connector U (S.withinSites s b v.1) _) (S.withinBond s b v.2 (sendEdge s b (x,i))); rw [S.port_bond]
  cases he : s.flip i
  · rw [S.positive hp _ _ _ _ _ _ he]; exact (S.patch.bond_pull (h:=hp) ..).1
  rw [S.negative hp _ _ _ _ _ _ he]; exact (S.patch.bond_inv (h:=hp) ..).1
end rotate

namespace Tuned
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (h : Tuned s b X Y) {η A' r Q : ℝ} {L : Side} (hx : Port P L η r Q A' X) (hy : Port P L η r Q A' Y)
    (hp : P.Funds S T) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
include h
lemma plazas {Z O : Support c} (he : ∀ i,i∈Z ↔ affine s b i∈O) (j) : j∈Y.plaza Z ↔ diagram s b S j ∈ X.plaza O := by
  simp only [plaza,mem_filter,mem_univ,true_and]
  exact and_congr (h.toParked.eligible j) (not_congr (assign_guard (StepData.sendSites s b) he ((display _ _ _).1 (ends_full ..))))
lemma steamy (A : Stores S) (w : ℕ) : Y.existSeeds (Locations.book s b A) w ↔ X.existSeeds A w := by
  unfold Coat.existSeeds; rw [h.x,h.seeds,h.toParked.aligned.2.1,h.v]; apply and_congr
  · change (∀ ⦃i⦄, i∈_→i∈_)↔ ∀ ⦃j⦄, j∈_→j∈_; simp_rw [Locations.place_map]; exact (Equiv.forall_congr_right (q:=fun j=> j∈A.place → j∈X.seeds.place) (StepData.sendSites s b))
  conv_rhs => rw [← Equiv.forall_congr_right (StepData.sendSites s b)]
  simp only [atF, Locations.dome_map]; simp_rw [toured]; rfl
lemma imposes (a : ℝ) {Z O : Finset (Bond f)} (he : ∀ i,i∈Z ↔ diagram s b S i∈O) (u : Directions G f) :
    Y.enforce a (wheels (S:=S) s b X.V u) Z=X.enforce a u O := values (diagram s b S) Z O he _ _ fun i _=> h.cone_eq a u i
include hp ht
lemma averaged_work (A : Stores S) (u : Directions G f) : Y.quoteNear (Locations.book s b A) (wheels (S:=S) s b X.V u)=X.quoteNear A u := by
  have he i : Y.assigned (Locations.book s b A) (wheels (S:=S) s b X.V u) i=X.assigned A u (s*i) := by unfold assigned; rw [h.toParked.aligned.2.1]; exact bills _ _ _ (posted_roll s b A i · _) _ _ (fun j _=> h.debit_eq hp ht u i j)
  unfold quoteNear Oriented.averaged; simp_rw [he]; apply congr_arg; exact Equiv.sum_comp (Equiv.mulLeft s) (X.assigned A u)
lemma minted (A : Stores S) : Y.far_bills (Locations.book s b A)=X.far_bills A := by
  let f(q:Signed) := ∑ p∈posted (turnStore q A) (200*X.B), X.extracted X.μ q p
  have he (q : Signed) : (∑ i∈posted (turnStore q (Locations.book s b A)) (200*Y.B), Y.extracted Y.μ q i)=f (s*q) := by
    have hm : Y.μ=wheels (S:=S) s b X.V X.μ := congr_arg (erect G) ((h.means hp ht).trans (tapeRev s b X.V X.μ).symm)
    rw [hm,h.toParked.aligned.2.1]; exact bills _ _ _ (fun j=> posted_roll (S:=S) s b A q j _) _ _ fun i _=> h.ex hp ht q i _
  unfold far_bills Oriented.averaged; simp_rw [he]; apply congr_arg; exact Equiv.sum_comp (Equiv.mulLeft s) f

include hx hy
lemma revved (u : Directions G f) (A : Stores S) {Ñ : ChartRatio G} (hn : LocalRatio Ñ) (a : ℝ) (R : Rep G f)
    (hu : 0 < a*X.t) (he : 4*a*X.t<Ñ.radius) : Y.steamLog R Ñ a (Locations.book s b A) (wheels (S:=S) s b X.V u)=X.steamLog R Ñ a A u := by
  have hw i : i∈Y.pens (Locations.book s b A) ↔ diagram s b S i∈X.pens A := by
    rw [pens,pens,h.toParked.aligned.2.1, mem_filter,mem_filter]; exact and_congr (visits ..) (not_congr (Locations.trunk_map ..))
  have hvA : (X.pens A).card = (Y.pens (Locations.book s b A)).card := by rw [(given _ _ _).2 hw, card_map]
  unfold steamLog; rw [h.averaged_work hp ht,h.minted hp ht,hvA,h.toParked.aligned.2.1]; apply congr_arg₂ (·-·) _ rfl; apply congr_arg₂ (·+·)
  · apply congr_arg; exact bills _ _ _ (visits s b A (200*X.B)) _ _ fun i _ => h.condensate hp hx hy i
  exact bills (diagram s b S) _ _ (h.plazas (Locations.dome_map s b A _)) _ _ fun i _=> h.gentry_eq _ _ i hn hu he

lemma fired (u : Directions G f) (A : Stores S) {Ñ : ChartRatio G} (hn : LocalRatio Ñ) (a : ℝ) (R : Rep G f)
    (hu : 0 < a*X.t) (he : 4*a*X.t<Ñ.radius) (l : Finset ℕ) (e : R.activities.Moves s (S.ratio.embed b)) :
    Y.Pack R Ñ l W a (Locations.book s b A) (wheels (S:=S) s b X.V u)=X.Pack R Ñ (e.kp.finsetCongr l) W a A u := by
  unfold Coat.Pack; rw [if_congr (h.steamy A 300) rfl rfl]; split
  swap; · rfl
  unfold steam; dsimp only; rw [h.revved hx hy hp ht u A hn a R hu he]; rw [h.toParked.aligned.2.1,h.completed]
  let D:=300*X.B; let v:=X.input u; let M:=Locations.book s b A; let p:= pull s (S.ratio.embed b) v
  have hm : Contract.order R l (vias S M D) p=Contract.order R (e.kp.finsetCongr l) (vias S A D) v := values (StepData.sendSites s (S.ratio.embed b)) _ _ (fun i=> visiting s b A i _) _ _ (fun i _=> accepts_cost ..)
  have hj : ∀ i,i∈readBonds (M.dome D) ↔ StepData.sendBonds s b i∈readBonds (A.dome D) := by
    intro i; simp only [readBonds, mem_filter,mem_univ,true_and]
    exact not_congr (assign_guard (StepData.sendSites s b) (Locations.dome_map s b A D) ((display _ _ _).1 (pointers ..)))
  have hp : S.patch.Branches S.kernel G := funds_branch hp
  have hh : tickets M D p Y.k = tickets A D v X.k := congr_arg₂ (·*·)
    (values (StepData.sendSites s b) _ _ (Locations.dome_map s b A D) _ _ (fun i _=> by rw [h.way]; exact portSite s b X.k v hp i))
    (values (StepData.sendBonds s b) _ _ hj _ _ (fun i _=> by rw [h.way]; exact portPin s b X.k v hp i))
  have ht : profiles M Y.χ D Y.x W p Y.k Y.V=profiles A X.χ D X.x W v X.k X.V := by
    rw [h.χ,h.way,h.v,h.x]; unfold profiles; dsimp only; apply congr_arg₂ (·*·)
    · apply values (Locations.shiftFaces s (S.ratio.embed b))
      · intro i; simp only [readFine,mem_filter,mem_univ,true_and]
        exact not_congr (assign_guard (StepData.sendSites s b) (Locations.dome_map s b A D) ((display _ _ _).1 (Locations.start_map ..)))
      intro i hi; exact movingMark ..
    exact values (StepData.sendBonds s b) _ _ hj _ _ fun i _=> barNoise s b X.k v hp A X.χ _ W X.V i
  rw [hm,hh,ht,h.imposes _ (h.plazas (Locations.dome_map s b A _))]
end Tuned
end YM.PhysicalNext.Repeat.Turn
