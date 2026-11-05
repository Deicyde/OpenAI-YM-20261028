import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Archives
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Siren
import YM.Push.RELAY_DIFFERENCE.Dictionary
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.Push.STRESS_FLUX.Orbits


/-!
# Use `Route/Desk` as an actual PORT (log-column readability)

Not claiming input's θ is `fiery`: to use the priced port (debit&smoky through
Voice's PA, which don't need those E/K data), present a blank copy of E costs with
flags reset to exactly `fiery`, only for this lemma! Keep physical β and the SAME
T,k,x etc. Not touching Branch densities. Cannot substitute this for real K or
pull E's Crown legality across. We only ever use this THROUGH its consequences
on measurable and local fields that are the actual same columns; even tag scrolls
not asserting Blueprint σ matcher.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
open Dictionary Dictionary.Geo
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {v : Dyed G S} {d : AnalyticBridge.LocalGaussian.Desk G S} {x W : ℝ} {p q : Pilot G S x} {X X' : Support c}

private def faded (a : Activities G f): Activities G f:= {a with forced:=fun i=>{a.forced i with extraTest:=fun _=>True},K:=0,E:=0}
private lemma fades (Y : Activities G f) (bp : BudgetPoint) (h : ∀ e q,Nonempty (Y.Moves e q)): (faded Y).Valid bp 0 0:= by
  let hW(Z : Support f):= WilsonStartup.Start.zero_reg (G:=G) (b:=bp) (X:=Z)
  refine ⟨⟨fun i=> hW _,fun i=>rfl,fun i _ _ _ _ _=>?_⟩,⟨fun _ _ _=>rfl,fun _ _ _=>Iff.rfl, fun _=>measurable_const, fun i=>MeasurableSet.univ, fun _ _ _ _ _=>rfl,fun _ _ _ _ _=>rfl, fun i j hz=> ?_⟩,fun e q=>?_,⟨0,fun i=> WilsonStartup.Start.zero_bound,fun i=>?_⟩, ⟨0,fun i=>⟨le_rfl,fun V=> norm_zero.trans_le le_rfl⟩,fun i=>?_⟩⟩
  · simp [logHessian,faded]
  · exact (hz rfl).elim
  · obtain ⟨f⟩ := h e q; exact ⟨⟨f.ep,f.kp,f.reg_site,f.reg_support,f.forced_support,f.forced_inventory,fun _ _=> Iff.rfl,fun _ _=>rfl,fun _ _=>rfl⟩⟩
  all_goals simp only [BudgetPoint.mass,Pi.zero_apply,mul_zero,ite_self]; exact ⟨fun _=>le_rfl,summable_zero, tsum_zero.trans_le le_rfl⟩

-- Form the side desk only after there is an actual Rep and pose chart.
structure Chips (v : Dyed G S) (P : Teller G) (W x : ℝ) : Prop where
  lawful : ∃ a C L Δ w, v.source.Lawful a C L Δ w
  arc_pos :0<v.arc
  inner : 4*v.arc < v.ratio.radius
  vista : 2*v.arc < firstRadius G
  paths : v.things.up=v.source.path
  clips : v.things.high=v.source.clip
  data : LocalRatio v.ratio
  boost : Boosted v.things P x
  heated : 0<W
  lives : 0<fiery G x S.patch.L
  lev : fiery G x S.patch.L≤1
  tall : v.bp.threshold=temp x
  beta : 0<v.source.beta
private def introduce (h : Chips v P W x) : AnalyticBridge.LocalGaussian.Desk G S :=
  let b:= {v.bp with threshold:=fiery G x S.patch.L, threshold_le:=h.lev, threshold_pos:=h.lives}
  let p:= {v.source with activities:=faded v.source.activities,p:=b}; ⟨v.things,x,W,p,v.bp,v.arc,v.ratio,v.chi,v.chi,h.heated,h.lives⟩
private lemma blank (h : Chips v P W x) : Route.Badge.App (introduce h):= by
  refine ⟨⟨⟨P,h.boost.funded⟩,?_,⟨h.paths.symm,h.clips.symm,rfl⟩,h.beta,h.tall,h.data,h.arc_pos,h.inner⟩,h.boost.produced,h.vista, h.boost.license, h.boost.enough⟩
  obtain ⟨a,b,c,l,d,he⟩:= h.lawful; exact ⟨a,b,c,0,0,he.paths,fades _ _ he.labels.moves⟩

lemma glance {i:Bond f} (hB : 120≤radiusB x) (h : Hears X p q) (hz : Shields X (S.ratio.parent i.1) (22*radiusB x)): let w:=Print.backdrop x p.key p.park p.y; let z:= Print.backdrop x q.key q.park q.y
    w.1 i=z.1 i ∧ w.2 i=z.2 i:= by
  intro w z; have hx := tight (x:=x) (hz.shrink (by omega)) (i:=i); have hm := portrait_of (S.ratio.parent i.1) (r:=0) h (hz.shrink (by omega)); have hT := hm.trunks i (show separation _ _≤0 by rw [separation_self])
  unfold w z Print.backdrop fresh; dsimp only
  by_cases ht:i∉p.park.trunks; swap; · rw [dif_neg ht,dif_neg (mt hT.not.mpr ht),dif_neg ht,dif_neg (mt hT.not.mpr ht)]; exact ⟨rfl,rfl⟩
  let a:p.park.Free:= ⟨i,ht⟩; let b:q.park.Free:=⟨i,hT.not.mp ht⟩; rw [dif_pos ht,dif_pos b.property,dif_pos ht,dif_pos b.property]; have he: chill p.key x p.park a↔ chill q.key x q.park b:= hm.freeze_same (by exact le_of_eq (separation_self _)) rfl
  by_cases hv : chill p.key x p.park a
  · rw [dif_pos hv,dif_pos (he.mp hv),dif_neg (not_not.mpr hv),dif_neg (not_not.mpr (he.mp hv))]; exact ⟨hug (i:=⟨_,hv⟩) (j:=⟨_,he.mp hv⟩) h hx rfl,rfl⟩
  rw [dif_neg hv,dif_neg (he.not.mp hv),dif_pos hv,dif_pos (he.not.mp hv)]; exact ⟨rfl,hark (i:=⟨a,hv⟩) (j:=⟨b,he.not.mp hv⟩) h hx rfl⟩
private def paper (d : AnalyticBridge.LocalGaussian.Desk G S) {E:Type} (m : Voice.Formula G S E) (p : Pilot G S d.betaHat) :=m p.park p.key ∅ p.tag p.view (Print.backdrop d.betaHat p.key p.park p.y)
private lemma persimmon {m : Voice.Formula G S ℝ} (i : Site c) (hf : Voice.Care d {i} m) (hB : 120≤radiusB d.betaHat) (he : Shields X i (64*radiusB d.betaHat)) : Pulled (paper d m) X:= by
  refine ⟨fun B F k=> ?_,fun p q _ _ h=>hf.comp ?_⟩
  · let V:=fun p : Config G c × RoomView B d.betaHat F G=> (p.1,Print.backdrop d.betaHat B F p.2); exact ⟨_,(hf.noted ..).comp (show Measurable V from measurable_fst.prodMk ((recording d.betaHat B F).comp measurable_snd)),fun _ _ _=>rfl⟩
  have hx (p) (hp:p∈Voice.ambient d {i}): separation i p ≤ 40*radiusB d.betaHat:= by simpa only [Voice.ambient,halo_spec,mem_singleton,exists_eq_left] using hp
  refine ⟨Geo.Reads.mono h.reads (fun k hk=> he k ((hx k hk).trans (by omega))),⟨fun j hj _=>?_,fun j hj _=>?_⟩,fun _ _=>Iff.rfl⟩
  · exact (glance hB h (he.shift (by have ht:= hx _ hj; omega))).1
  have ht : separation i (S.ratio.parent j.1) ≤ 15*radiusB d.betaHat:= by simpa only [Voice.floor,halo_spec,mem_singleton,exists_eq_left] using hj
  exact (glance hB h (he.shift (by omega))).2
lemma Pulled.conforme {z g : Pilot G S x →ℝ} (h : Pulled z X) (he :∀ p,Matched p→z p=g p) : Pulled g X:= by
  refine ⟨fun b₁ F k=> ?_,fun p q ht hl hp=> (he p ht).symm.trans ((h.agreed ht hl hp).trans (he q hl))⟩
  obtain ⟨u,hu,H⟩:= h.enter b₁ F k; exact ⟨u,hu,fun V h y=> (he ⟨b₁,F,k,V,y⟩ h).symm.trans (H V h y)⟩
open AnalyticBridge.Annulus.Map Dictionary.Wires
-- Project mean and full color z first -- distinct records at each rate.
def Dyed.combo (v : Dyed G S) (p : Pilot G S x) (r : ℝ):= meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1+r • p.y.2

def Dyed.faresQ (v : Dyed G S) (j : Slots S) (r : ℝ) (p : Pilot G S x):= if keep x (shots S x) p.key p.park j then ‖lands v.things x p.view p.tag (shots S x) p.key p.park v.chi v.arc p.y.1 (v.combo p r) j‖^2/2 else 0
lemma Dyed.fares_read (h : Chips v P W x) (i : Slots S) (r : ℝ) (he : Shields X (spot S i) (64*radiusB x)): Pulled (v.faresQ (x:=x) i r) X:= by
  let d:=introduce h
  have hp: Pulled (paper d (Voice.debit d r i)) X:= persimmon _ (Voice.dispatch d (blank h) r i) h.boost.produced.scale he
  refine hp.conforme fun p hx=>?_
  unfold paper; rw [Voice.debits d (blank h) p.tag p.view hx _ r,show Print.see _ _ _ _=_ from Print.rollback ..]; rfl
-- project η. only at supplied β.

def Dyed.issue (v : Dyed G S) (i : Bond f) (p : Pilot G S x):=
  let m:= meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1; let q:= p.y.2; let e:=eta v.things x p.view p.tag (shots S x) p.key p.park v.chi v.arc p.y.1 m (coupling v.source.beta)
  if h:i∈AnalyticNext.ConnectedActivity.Aff.activeB p.key p.park (radiusB x) then ∑ j:G.ColorIndex,e (Milk.fundedB i h,j)*q (Milk.fundedB i h,j) else 0
lemma Dyed.issue_at (v : Dyed G S) (p : Pilot G S x) (i : Active p.key x p.park) : v.issue i.val.val p=∑ j:G.ColorIndex,(eta v.things x p.view p.tag (shots S x) p.key p.park v.chi v.arc p.y.1 (meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1) (coupling v.source.beta) (i,j))*p.y.2 (i,j) := dif_pos ((Milk.stillActive ..).mpr i.property)
set_option maxHeartbeats 400000 in
lemma Dyed.issue_read (h : Chips v P W x) (i : Bond f) (he : Shields X (S.ratio.parent i.1) (64*radiusB x)): Pulled (v.issue (x:=x) i) X:= by
  let d:=introduce h; have hp: Pulled (paper d (Voice.smoky d i)) X:= persimmon _ (Voice.smoky_care d (blank h) i) h.boost.produced.scale he
  refine hp.conforme fun p hx=>?_
  unfold paper; by_cases ht:i∈AnalyticNext.ConnectedActivity.Aff.activeB p.key p.park (radiusB x)
  · let j:=Milk.fundedB (x:=x) i ht
    let c:=Print.backdrop d.betaHat p.key p.park p.y; have hv:= Voice.clouded d (blank h) p.tag p.view hx c ∅ j
    change Voice.smoky d j.val.val .. =v.issue j.val.val p; rw [show Print.backdrop _ _ _ _=c from rfl]
    refine hv.trans ?_
    have hm : Print.see d.betaHat p.key p.park c=p.y:= Print.rollback ..
    have hh : iced c.1 p.key d.betaHat p.park=p.y.1:=congr_arg Prod.fst hm
    dsimp only at hv ⊢; rw [hh,hm]; exact (v.issue_at (x:=d.betaHat) p j).symm
  rw [Dyed.issue,dif_neg ht,Voice.smoky,if_neg]
  rintro ⟨u,h⟩; exact ht (h ▸ ((Milk.stillActive ..).mpr u.property))
end YM.PhysicalNext.InteractingRank.Pump
