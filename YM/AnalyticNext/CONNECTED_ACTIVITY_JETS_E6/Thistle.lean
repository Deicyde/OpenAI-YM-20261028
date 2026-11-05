import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Duster
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unfrozen

/-!
# Localization in the integration coordinates to compact families

 When not suppressing chart transport but using it to hold `U`
 across its stencil. `carry` allows replacing all large arguments in all
 terms EXCEPT the fixed `U`, Y, and density/score. Good even for detached
 psi’s. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets   Poll Pond  
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {R : Rep G f} {A a α β B C p : ℝ} {x : Site c}

def sweepZ (X : Coat T F) (β : ℝ) (w : Directions G f) : Air f G := WithLp.toLp 2 (stand ((gStep β)⁻¹ • (w-voltage X)))


-- Point comparison inside one sector
structure Transfer (X : Coat T F) (u v : Directions G f) (p : ℝ) : Prop where
  both i : u i=v i ∨ (p<‖u i‖ ∧ p<‖v i‖)
namespace Transfer
variable (X : Coat T F) {u v : Directions G f} {a : ℝ} (h : Transfer X u v (4*a*X.t))
include h
lemma grain (_ha : 0<a*X.t) (i : Bond f) (d : ℝ) (hz : 0 < d*X.t) (he : d*X.t≤ 2*a*X.t) :
    X.cone d u i=X.cone d v i ∧ (X.cone d u i≠0→ u i=v i) := by
  rcases h.both i with he'|⟨hx,hv⟩; · exact ⟨by unfold cone; rw [he'],fun _=> he'⟩
  have hU : X.cone d u i=0 := by by_contra hh; exfalso; have hh:=X.amount hz u i hh; nlinarith
  have hY : X.cone d v i=0 := by by_contra hh; exfalso; have hh:=X.amount hz v i hh; nlinarith
  exact ⟨hU.trans hY.symm,fun ht=> (ht hU).elim⟩
lemma plumeJ (ha : 0<a*X.t) (i : Bond f) (Ñ : ChartRatio G) : X.gentry Ñ a u i=X.gentry Ñ a v i := by
  obtain ⟨hp,hx⟩:= grain X h ha i (2*a) (by rw [mul_assoc]; positivity) le_rfl
  unfold gentry; rw [← hp]; by_cases hj : X.cone (2*a) u i=0
  · rw [hj,zero_mul,zero_mul]
  rw [hx hj]
omit h in lemma taxed (i : Spot c f) (s : Signed) (p : Room P S T X.x)
    (he : ∀ j,distAt S j (s.act (lead S i)) ≤ X.B→ X.Hot j→ u j=v j) : Vine.costs X u s i=Vine.costs X v s i := by
  refine sum_congr rfl fun j hj=>?_; unfold Vine.pot; split
  next hh =>
    let x:=root S (s,j); have ht : Zone X X x (12*X.B) := ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
    have hy: x=s.act (lead S i) := by change s.act (focus S j)=_; rw [cost_is_here j,(parent_iff j i).1 hj]
    rw [ht.needle p s j rfl le_rfl u v (hy.symm ▸ he)]
  next hh=> rfl

lemma outfit (Y : Stores S) (p : Room P S T X.x) (ha : 0<a*X.t) (Ñ : ChartRatio G) (U : Config G f)
    (W : ℝ) (R : Rep G f) (k : Finset ℕ) : Polar.stock X a R W Ñ u U k Y=Polar.stock X a R W Ñ v U k Y := by
  let P:= X.plaza (Y.dome (304*X.B)); let D b:= X.enforce a b P
  have hp i := grain X h ha i a ha (by nlinarith)
  have hv:D u=D v:=Finset.prod_congr rfl fun i _=> (hp i).1
  unfold stock; split
  next hA =>
    dsimp only; unfold D at hv; rw [← hv]
    by_cases hP:D u=0
    · rw [show X.enforce _ _ _=0 from hP,mul_zero,mul_zero]
    have hx i (hi:i∈P):u i=v i := (hp i).2 fun hh=> hP (prod_eq_zero hi hh)
    suffices hf: plumeLog X a R Ñ u U Y=plumeLog X a R Ñ v U Y by rw [hf]
    unfold plumeLog; rw [sum_congr rfl (fun i (_:i∈P)=>plumeJ X h ha i Ñ)]
    suffices ht:chalky X u U Y=chalky X v U Y by rw [ht]
    apply congr_arg Oriented.averaged; funext s; refine sum_congr rfl fun i hi=> ?_
    unfold rootface; rw [taxed X i s p (fun j hj hU => hx j (mem_filter.mpr ⟨mem_univ _,hU,Finset.not_disjoint_iff.mpr
      ⟨_, touch_extend ((rotates_dome ..).mp (mem_filter.mp hi).2) (by change separation (s.act (lead S i)) _ ≤ X.B at hj; omega), center_end _⟩⟩))]
  next hA=> rfl

lemma spinning (ha : 0<a*X.t) (p : X.Noncrystal) (hF : P.Funds S T) (R : Rep G f) (i : ChainIndex f) :
    spins X a R u (sweepZ X R.beta u) i=spins X a R v (sweepZ X R.beta v) i := by
  let Z b:= sweepZ X R.beta b
  have hx i (hi : u i=v i) j : Z u (i,j)= Z v (i,j) := by unfold Z sweepZ stand; simp only [Pi.smul_apply, Pi.sub_apply]; rw [hi]
  have hh i: Polar.patch X a u i=Polar.patch X a v i ∧ (X.Hot i→ Polar.patch X a u i≠0 → ∀ j, Z u (i,j)=Z v (i,j)) := by
    unfold Polar.patch; split
    next hi=> obtain ⟨he,hv⟩:=grain X h ha i (2*a) (by rw [mul_assoc]; positivity) le_rfl; exact ⟨he,fun _ h=> hx _ (hv h)⟩
    next hi=> exact ⟨rfl,fun h=> (hi h).elim⟩
  unfold spins; rcases i with i|i|i|i|i <;> simp only [Sum.elim]
  · have hi i':= hh i'; unfold major; rw [← (hi _).1]; by_cases hm: Polar.patch X a u i=0
    · rw [hm,zero_mul,zero_mul]
    by_cases hf:X.Hot i
    · have hv k : sweepZ X R.beta u (i,k)=sweepZ X R.beta v (i,k):= (hh _).2 hf hm k
      rw [sum_congr rfl (fun k (_: k∈ (univ:Finset G.ColorIndex))=> congr_arg (· * shimmer X R.beta (i,k)) (hv k))]
    have hv k:= X.calm_crys p hF R.beta (i,k) hf; simp [hv]
  let x:= i.2.1; let y:= arrive x i.2.2
  unfold entangled; rw [← (hh x).1, ← (hh y).1]; let A:= Polar.patch X a u
  by_cases hz:A x*A y=0
  · change (A x*A y)*_=(A x*A y)*_; rw [hz,zero_mul,zero_mul]
  by_cases hs:X.Hot x ∧ X.Hot y
  swap; · have he (v):X.qunique v i=0:= by by_contra hn; exact hs (X.emitting_crys p hF v i hn)
          simp_rw [he,mul_zero]
  unfold qunique circle; dsimp only; unfold y x Z at *
  simp_rw [(hh i.2.1).2 hs.1 (left_ne_zero_of_mul hz),(hh (arrive i.2.1 i.2.2)).2 hs.2 (right_ne_zero_of_mul hz)]

lemma flutter (ha:0<a*X.t) (R : Rep G f) (U : Config G f) (p : Room P S T X.x) (Ñ : ChartRatio G)
    (hn : X.Noncrystal) (i : LogIndex c f) :
    logMoment X a R Ñ u U (sweepZ X R.beta u) i= logMoment X a R Ñ v U (sweepZ X R.beta v) i := by
  have hv j:=grain X h ha j (2*a) (by rw [mul_assoc]; positivity) le_rfl
  have hP' i : X.enforce (2*a) u i=X.enforce (2*a) v i := prod_congr rfl fun j hj=> (hv j).1
  rcases i with i|i|i
  · change frost _ _ _ _ _ _=frost _ _ _ _ _ _; unfold frost; rw [hP']
  · unfold logMoment whelp; rcases i with i|i|i <;> simp only [Sum.elim]
    · unfold Polar.hover; dsimp only; rw [← hP']; by_cases ht : X.enforce (2*a) u (X.booth (rowSite S i))=0
      · simp only [ht,zero_mul]
      have hh:= taxed X i.2 i.1 p (fun j hj hU=> (hv j).2 fun hh=> ht (prod_eq_zero (X.ages j _ hU hj) hh))
      unfold rootface; rw [hh]
    unfold solo; rw [plumeJ X h ha i Ñ]
  exact spinning X h ha hn p.accepted R i
lemma carries (ha : 0<a*X.t) (p : Room P S T X.x) (ht : X.Noncrystal) (U : Config G f) (Ñ : ChartRatio G)
    (R : Rep G f) (W : ℝ) (l : ℕ) (k : Finset ℕ) (i : Head S) :
    ember X a R W Ñ u U (sweepZ X R.beta u) k l i= ember X a R W Ñ v U (sweepZ X R.beta v) k l i := by
  have hv i:= (grain X h ha i a ha (by nlinarith)).1
  have hP' i : X.enforce (2*a) u i=X.enforce (2*a) v i := prod_congr rfl fun j hj=> (grain X h ha j (2*a) (by rw [mul_assoc]; positivity) le_rfl).1
  unfold ember; rcases i with i|i|i|i
  · simp only [Sum.elim]; rw [outfit X h i p ha Ñ U W R k]
  · simp only [Sum.elim,sheath]; rw [hP']
  · simp only [Sum.elim,flutter X h ha R U p Ñ ht i]
  unfold sprinkle; cases i <;> simp only [Sum.elim]
  · unfold flare; rw [hP']
  unfold aura; rw [hv]
end Transfer
end YM.ConnectedActivityE6.Blaze.Flux
