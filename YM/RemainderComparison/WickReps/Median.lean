import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Star
/-! # Adapts Trio.Star EXACT erosion. Does not require equivariance of separate germs on the arbitrary OUTSIDE extension in Arts! Needed for permissions upon kinetic seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open PhysicalNext PhysicalNext.Repeat Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F:Side} {j i m n W w r k l h:ℕ} {B : BudgetPoint} {Y:Stars→Side}
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val))
variable (B) (z:ℕ)(fa:∀ i:Stars,Offer G (Y i))(V:Config G c)
structure Sensible (B : BudgetPoint)(r:ℕ){c:Side}(f₀:Offer G c){Y:Stars→Side}(fa:∀ i:Stars,Offer G (Y i)):Prop where
   moves (i:Stars) (s : Signed)(b x:Site (Y i))(V:Config G (Y i)): flags B.threshold V=∅ → fa i x (pull s b V)= fa i (affine s b x) V
   pace i j : Trio.Compatible (fa i) (fa j) B r
   forks i : Trio.Compatible (fa i) f₀ B r
   visitL x : LocalOn (neighbors r x) (f₀ x)
variable (o:Site c) (hp:w+4≤z) (hr:2*r≤w) (hg:2*z≤ k) (hC:4*r+16≤c.val) (hU : Healthy B.threshold (neighbors k o) V)
local notation "C₀" => (charm w r)
include hp Q hU hg
variable (f₀ : Offer G c) (h₀:Sensible B r f₀ fa)
include hr h₀
lemma freeAnchor (i : Stars) (x: Site (Y i)) :
    let p:= emerge Q i x o; let W:=Slide.shape (pad Q i) p V
    unit Q fa i x p V=fa i (Slide.ascended (Q i) x) W ∧ flags B.threshold W=∅ ∧
       Agrees (Lattice.box r) (expandAt (Slide.ascended (Q i) x) W) (Slide.thing (Slide.charm (w+i.val) r x) o V):= by
  intro p W; refine ⟨?_, Trio.hint Q z V i hp p (hU.mono_left (Trio.patch Q z hp i x o hg)), Slide.wandered (Q i) (hr.trans (Nat.le_add_right ..)) x o V⟩ -- order
  obtain ⟨v,hv⟩:= Slide.snap (Q i) x; rw [← hv, ← add_zero ((Slide.slant v).act x), show (Slide.slant v).act x+0=Lattice.affine (Slide.slant v) 0 x from rfl, ← h₀.moves _ _ _ _ _ (Trio.hint Q z V i hp p (hU.mono_left (Trio.patch Q z hp i x o hg)))]
  rw [show pull (Slide.slant v) 0 W=W from Slide.traps (Q i) v V p]; rfl
include hC
lemma gazing (hm:0<r) : unearned B Q z fa o V=f₀ o V:= by
  choose x hx using Slide.presents (Q 0) (Z:=r) (hr.trans (Nat.le_add_right ..)) hm -- order edit
  let P (p: Petals r):= Trio.unit Q fa (0:Stars) (x p) (emerge Q 0 (x p) o) V
  have hk i y:= freeAnchor B Q z fa V o hp hr hg hU f₀ h₀ i y
  have hz (i:Stars) (x' : Site (Y i)): Trio.unit Q fa i x' (emerge Q i x' o) V=P (Slide.charm (w+i.val) r x'):= by
    let q:= charm (w+i.val) r x'; obtain ⟨hf,hQ,hJ⟩:= hk i x'; let y:=x q
    obtain ⟨ht,he,hh⟩:= hk 0 y; have hh' : charm (w+(0:Stars).val) r y=q:= hx q
    rw [hh'] at hh; change _=Trio.unit Q fa 0 y _ V; rw [hf,ht]; apply h₀.pace _ _ _ _ _ _ hQ he; exact fun i hi hj=>(hJ i hi hj).trans (hh i hi hj).symm
  change (∑ i:Stars,ray i*∑ y:Site (Y i),masked B.threshold _ _ V)= _
  simp_rw [cash B Q z fa V o hp hg hU,hz, Slide.collects _ hm hr Q P]
  let x' := x (Slide.rosy r); let p:=emerge Q 0 x' o; change Trio.unit Q fa 0 x' p V=_
  obtain ⟨hz,hk,he⟩:= hk 0 x'; rw [hz]; rw [show charm (w+(0:Stars).val) r x'=Slide.rosy r from hx _,Slide.self] at he
  obtain ⟨T,hT,hL⟩:= Slide.shifts V o r (by omega) B.threshold B.threshold_pos.le (hU.mono_left (show neighbors r o ⊆ neighbors k o from (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))))
  exact Eq.trans (h₀.forks 0 _ o _ T hk hT (fun i hi hj=> (he _ hi hj).trans (hL _ hi hj).symm)) (h₀.visitL o T V (readNear o (by omega) hL))

omit hC hg hp Q hr hU
lemma stratus : Sensible B r (fun i=>stillA (f₀ i)) (fun i j=>stillA (fa i j)):= by
  have ht {c:Side}:flags B.threshold (1:Config G c)=∅:= smoky (P:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using B.threshold_pos)
  refine ⟨fun i s b x V'=>?_, fun i j k l U V hg he ht'=> congr_arg₂ (·-·) (h₀.pace i j k l U V hg he ht') (h₀.pace i j k l 1 1 ht ht (fun _ _ _=>rfl)),fun i j k u v hu hv he=>?_ ,fun x U V hu=> congr_arg₂ (·-·) (h₀.visitL x U V hu) rfl⟩
  · intro hp'; have hk : pull s b (1:Config G (Y i))=1:=by funext i; simp [Lattice.pull,Lattice.Step.read];
    exact congr_arg₂ (·-·) (h₀.moves i s b x V' hp') ((congr_arg (fa i x) hk.symm).trans (h₀.moves i s b x 1 ht))
  exact congr_arg₂ (·-·) (h₀.forks i j k u v hu hv he) (h₀.forks i j k 1 1 ht ht (fun _ _ _=>rfl))
omit h₀
lemma ofOrig (h:CompatibleP B r f₀ fa): Sensible B r f₀ fa:=⟨fun i s b x V _=> h.moves i x s b V,h.pace,h.forks,h.visitL⟩
end YM.RemainderComparison.WickReps
