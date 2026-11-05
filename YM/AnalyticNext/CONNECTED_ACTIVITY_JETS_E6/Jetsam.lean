import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unfrozen

/-!
# Full arguments for Polar. Manifest-independent even off domain.

 Pre-β pole tests along contours are already Pad data on this V (off it, actual
 defaults `Ring.inverse, integral` still local). Use η,x before every.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Raw Matter Blaze.Scroll Blaze.Vine Blaze.Polar Blaze.Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {x : Site c} {X X' : Coat T F} {l m : ℕ} {k k' : Finset ℕ} {R : Rep G f} {Z : Support c}
variable {w v w' v' : Air f G}
namespace Borough

variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x) (hl : 500 ≤ l)
include H p hl
-- reading in old coordinate U=align and w' are new sector arms
lemma season (Ñ : ChartRatio G) (a : ℝ) {i : Miniature c f} (he : sleeve S X.B l i⊆ Z) :
    let u:=X.liftA R.beta w; let u':=X'.liftA R.beta v
    whelp X a R Ñ u (X.input u) i= whelp X' a R Ñ u' (X'.input u') i := by
  intro u u'; rcases i with i|i|i
  · have hz : 500*X.B ≤ l*X.B := Nat.mul_le_mul_right _ hl
    have hh : Cleanroom Z (400*X.B) (rowSite S i) := fun j hj=> he ((Animals.neighbors_mem ..).mpr (hj.trans (by omega)))
    obtain ⟨hv,hk⟩:= H.cornice p i (fun _ hi=> hh _ (hi.trans (by omega)))
    let o:=rowSite S i
    have hu (y) (hi : y∈ Animals.neighbors X.B o) : Cleanroom Z (30*X.B) y := fans hh
      (by have hh := (Animals.neighbors_mem ..).1 hi; change separation o y+_≤_; omega)
    have hF : Inside o X.seeds (200*X.B) ↔ Inside o X'.seeds (200*X.B) := (H.social (x:=o) (a:=250*X.B) (fun j hj=> hh j
      (by change separation o j ≤ _; have hx : 100 ≤ X.B := p.sight.1; omega))).covert o (by rw [separation_self]; omega)
    unfold whelp; simp only [Sum.elim]; unfold Blaze.Polar.hover booth; dsimp only
    rw [← H.B,hv,hk true,H.enforces p _ hu]; simp_rw [show rowSite S i=o from rfl, hF]; rfl
  · exact H.domeLight p i (fun j hj => town_circle (S:=S) (l:=l) (p:=i) (B:=X.B) he j (hj.trans (Nat.mul_le_mul_right _ (by omega))))
  have hf (j : Site c) (hj : separation (atEdge S i) j≤400*X.B) := town_circle (S:=S) (l:=l) (B:=X.B) (p:=i) he j
    (hj.trans (Nat.mul_le_mul_right _ (by omega)))
  obtain ⟨hp,hz⟩:= H.occupied p i hf
  unfold whelp solo; dsimp only [Sum.elim]; unfold u u'
  simp_rw [hp,hz,H.vale p (p:=i) (fun j hj=> hf j (hj.trans (by omega)))]
lemma regime (b : ℝ) (h : Intake P T X.x R) {i : LogLetter c f} (he : space T l X.B R i⊆Z) :
    let u:=X.liftA R.beta w; let u':=X'.liftA R.beta v
    Blaze.Polar.frost X b R u (X.input u) i=Blaze.Polar.frost X' b R u' (X'.input u') i := by
  intro u u'; have hv := H.province p (l:=l) (by omega) i he h b
  rcases i with i|i|i|i|i|i
  · exact hv
  · exact hv
  · exact hv
  · exact hv
  · exact hv
  let U:= X.plaza (bothFoot (atOne _) 0 X.B T.down i); let s := i.1; let j:= i.2.2.2; let g : Cell c := (i.2.2.1,i.2.1)
  have hD : Agrees (pairFoot X.B T.down g j) (pull s 0 X.V) (pull s 0 X'.V) := H.turnV p (l:=l) (by omega) _ _ he
  let q:= Push.AbsoluteSums.Paths.duplex T.down i.2.1 j
  have hh (i : Fin 2) : (q i).atSite (pull s 0 X.V) g.1=(q i).atSite (pull s 0 X'.V) g.1 := slot_local _ _ _ _ (agrees_mono hD
    (fun z hz=> Finset.mem_union_right _ (mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ _,hz⟩))))
  have hA : ∀ y∈ bothFoot (atOne _) 0 X.B T.down i,Cleanroom Z (30*X.B) y := by
    intro y hy z hz; obtain ⟨x,hx,rfl⟩:= mem_image.mp hy
    obtain ⟨r,rfl⟩:= s.actEquiv.surjective z
    change s.act r∈ Z; rw [← affine0]; apply he; apply mem_image_of_mem
    obtain ⟨p,hp,hx⟩:= halo_spec.mp hx; refine halo_spec.mpr ⟨p,hp,(separation_triangle p x r).trans ?_⟩
    have hl := Nat.mul_le_mul_right X.B hl
    change separation (affine s 0 x) (s.act r) ≤ 30*X.B at hz; rw [affine0,separation_signed] at hz; omega
  have hF (B d : ℕ) : twin T.down g B d (pull s 0 X.V) j=twin T.down g B d (pull s 0 X'.V) j := by
    unfold Blaze.Polar.twin PathData.ellTerms; rw [show (T.down.row _ j.1).2.atSite _ g.1=_ from hh 0,
      show (T.down.row _ j.2).2.atSite _ g.1=_ from hh 1]; rfl
  unfold Blaze.Polar.frost; rw [← H.B, ← H.weather]
  exact congrArg₂ (·*·) (congr_arg ((-(- Raw.orientation * R.beta))*·) (hF (till X.x) S.patch.L.val)) (H.enforces p _ hA (2*b))

omit H p hl in
private lemma lastLeg (G : StepData c f) (p : Bond f) (z : Itinerary f m) (B l : ℕ) :
    town G B l (arrive p z)⊆ visited G B l p z := by
  induction m generalizing p
  · exact Finset.Subset.refl _
  next m ih => exact Finset.Subset.trans (ih (Itinerary.next z) _) Finset.subset_union_right

lemma centres (a : ℝ) (i : ChainIndex f) (K : Borough X X' Z w' v' k k' R) (hx : basisFoot S X.B l i⊆ Z) :
    spins X a R (X.liftA R.beta w) w' i=spins X' a R (X'.liftA R.beta v) v' i := by
  let q : ℕ:= l; have hq : 50≤l := by omega
  rcases i with i|i|i|i|i
  · exact congrArg (fun s=> (-s)/(2:ℝ)) (H.starA p hq hx : ArmA X.shutter X.plate i=_)
  · unfold spins; simp only [Sum.elim]; rw [neutral X X' H.weather]; unfold shutter; rw [H.B]
  · exact congrArg (fun s=> s/(2:ℝ)) (H.starS p hq hx : ArmS X.shutter X.plate i=_)
  · change major _ _ _ _ _ _ = major _ _ _ _ _ _; unfold major
    have hv:= H.minable p hq i hx; have hh := (K.arches p hq i hx a).2
    rw [show Blaze.Polar.patch X a (X.liftA R.beta w) i=Blaze.Polar.patch X' a (X'.liftA R.beta v) i from (H.arches p hq i hx a).1]
    apply congrArg; apply sum_congr rfl; intro j hj
    simp_rw [hh,hv.shinesP p (i,j) rfl (by omega)]
  change entangled _ _ _ _ _ = entangled _ _ _ _ _; unfold entangled; let x:= arrive i.2.1 i.2.2
  have hb : town S X.B l i.2.1⊆ Z := Finset.Subset.trans Finset.subset_union_left hx
  have hy : town S X.B l x⊆ Z := (lastLeg _ _ _ _ l).trans hx
  have hl := (K.arches p hq _ hb a).2; have hz := (K.arches p hq _ hy a).2
  have h r (hr : town S X.B l r⊆Z) : Blaze.Polar.patch X a (X.liftA R.beta w) r=Blaze.Polar.patch X' a (X'.liftA R.beta v) r := (H.arches p hq _ hr a).1
  rw [h _ hb,h x hy]; apply congrArg
  have hg : combo i.2.1 i.2.2 (X.finale i.1)= combo i.2.1 i.2.2 (X'.finale i.1) := by
    refine combL _ _ _ _ hx fun t x y hu hv => ?_
    have hd := H.minable p hq y hv; ext m n
    unfold finale; split
    next ht => change -(X.shreds _ _) = -(X'.shreds _ _); rw [hd.scrapsL p (y,n) rfl (by omega)]
    next => exact (H.minable p hq x hu).plateL p (x,m) rfl (by omega) _
  unfold qunique circle; rw [hg]; dsimp only; unfold x at hz; simp_rw [hl,hz]
end Borough
end YM.ConnectedActivityE6
