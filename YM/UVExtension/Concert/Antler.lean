import YM.UVExtension.Concert.Duet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick PhysicalNext.Repeat Lantern Marlin Song Animals Slide MeasureTheory Set Filter
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {x y W μ γ a b e: ℝ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
   {R:Rep G f}{H:Cash W x μ L Q o a T R} {Y D : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y}
    {p:BudgetPoint} (k:ℕ)

namespace Fly
variable {g : D→ Config G c→ℝ} (h:∀ i,p.Regular univ (g i)) (hp:∀ i: Fly G c p,Charm M b (fun d=> i.reel (g d)))
  (hv:0≤ b)
def star (G : Gauge)(p:BudgetPoint) (n : Side): Fly G n p :=
  ⟨1,Boulevard.smoky (P:=p) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using p.threshold_pos),[],by simp,by simp⟩
include h hp hv
lemma hems (i : Fly G c p): Charm M (b+b) (fun d=> i.reel (Boulevard.stillA (g d))):=by
  let x:RegularAddress c:= ⟨0,univ,mem_univ _⟩; let P:= p
  let Z d:= i.reel (fun U:Config G c=> g d 1)
  have he: (fun d => i.reel (Boulevard.stillA (g d)))=(fun d=> i.reel (g d)-Z d):= by
    funext j; exact VerifiedReset.left_sub (f:=g j) (g:=fun U:Config G c => g j 1) ((h j).smooth i.view (show Healthy p.threshold _ _ from (i.taps x).live)) contDiffAt_const i.lengthC
  rw [he]; apply Charm.apart (hp _); apply (show Charm M b Z from ?_)
  unfold Z reel; simp_rw [Work.G07.left_const]; split
  next hL => exact hp (star G p _)
  exact Charm.nil hv
lemma spurs {v w:ℕ} {C:Side} (X:v+1≤w) (o : Site C)(K:2*v ≤ c.val) (u:Tap p G o (neighbors w o)) :
    Charm M (2*Trio.tilt p w*(b+b)) (fun i=> u.read (Boulevard.stillA (g i) ∘ Slide.shape (Slide.cognac K) o)):= by
  let P:=Slide.cognac K; let U:=Slide.shape P o (K:=G.El)
  have hz j: separation o (Slide.sites P o j) ≤ w:= (Slide.village K o j).trans (by omega)
  let T i:= Boulevard.stillA (g i); have hT i : p.Regular Finset.univ (T i):= CouplingShape.reg_sub (h i) (CouplingShape.reg_const _)
  choose f ht hh hV using fun i : Fly G c p=> (hems h hp hv i).claim
  have hq : 0 ≤ b+b:= add_nonneg hv hv
  apply Charm.mk; refine Lamppost.bloom (M:=Trio.tilt p w) (b:=fun _=>b+b) M.within (f:=fun z i=> f i z) ht (fun j k=> hh k j) (fun i=> u.read (T i ∘ U)) ?_ (by unfold Trio.tilt; positivity) (fun z hz=> ⟨hq,⟨le_refl (b+b), hq⟩,fun i=> hV _ z hz⟩) hq
  intro S a m hm hΨ
  let g':= ∑ i∈S,a i • T i; have hP : p.Regular univ g':= brigade S a T (fun i _ => hT i); have hu : flags p.threshold (U u.view)=∅:= Slide.allFlag P o u.view _ (fun i=> (neighbors_mem ..).2 (hz i)) p.threshold p.threshold_pos.le u.live
  let A : RegularAddress c:=⟨0,univ,mem_univ _⟩
  rw [← Tap.staves S a (fun i=> T i ∘ U) u (fun i _=> Slide.regular P o (hT i) (fun i=> (neighbors_mem ..).2 (hz i)))]
  rw [show (∑ i∈S,a i • (T i ∘ U))=g'∘ U from funext fun i=> by simp only [Function.comp_apply,g',Finset.sum_apply,Pi.smul_apply]]
  apply Slide.stalled P o g' hz u.poll u.view u.card u.innerP (show Push.Local.Chart p.order g' (U u.view) from hP.smooth _ (by unfold Healthy; rw [show flags p.threshold _=_ from hu]; simp)) -- hUF
  intro l hl hi; let i:Fly G c p:= ⟨U u.view,hu,l,hl,hi⟩; change ‖(i.taps A).read (∑ i∈S,a i • T i)‖≤ m; rw [Tap.staves _ _ _ _ (fun i _=> hT i)]; exact hΨ i
end Fly

variable {Qp:Stars→Side} {v w t : ℕ} (hq : ∀ i:Stars,(Qp i).val=2*(v+i.val)) (o:Site c) (hk : v+5 ≤ w)
   (g: D→ ∀ i: Stars,Trio.Offer G (Qp i)) (f:Stars→ℝ)
   (h:∀ i j d,p.Regular univ (g d i j)) (hp:∀ i j (w: Fly G (Qp i) p), Charm M (f i) (fun d=> w.reel (g d i j))) (hv:∀ i,0≤f i)

include hk h hp hv
-- environments
lemma spired (z:Tap p G o (neighbors w o)): Charm M (∑ i:Stars, |ray i| *((Fintype.card (Site (Qp i)):ℝ)*(2*Trio.tilt p w*(f i+f i))))
   (fun d=> z.read (Trio.ornament hq (g d) o)):=by
  have he d i j: p.Regular (neighbors w o) (Trio.unit hq (Trio.rip (g d)) i j o):= Trio.unit_m (B:=p) hq w _ (fun i j=> h i j d) (by omega) o i j
  let f' i j d:= Trio.unit hq (Trio.rip (g d)) i j o; let u i d:= ∑ j, f' i j d
  have hK d: Trio.ornament hq (g d) o=∑ i:Stars,ray i • u i d:= by ext; simp [u,Trio.ornament,Trio.beacon,f']
  simp_rw [hK]; have hx d: z.read (∑ i:Stars,ray i • u i d)=∑ i:Stars,ray i*z.read (u i d):= Tap.staves Finset.univ ray (fun i=>u i d) z (fun i _=> Meadow.regularA Finset.univ (fun j _=> he d i j))
  simp_rw [hx]
  apply Charm.rack; intro i hi; apply Charm.multiplies
  have H d:z.read (u i d)= ∑ j,z.read (f' i j d):=Push.Local.left_sum _ _ _ _ (fun j _=> (he d i j).smooth z.view z.live) z.card
  simp_rw [H]
  have ht j: Charm M (2*Trio.tilt p w*(f i+f i)) (fun d=>z.read (f' i j d)):= Fly.spurs (h i j) (hp i j) (hv _) (by have :=i.isLt; omega) o (hq i).ge z
  simpa only [sum_const,nsmul_eq_mul,card_univ] using! Charm.rack Finset.univ (fun j d=> z.read (f' i j d)) _ (fun j _=> ht j)

lemma unearns (U:Config G c) : Charm M (∑ i:Stars, |ray i| *((Fintype.card (Site (Qp i)):ℝ)*(f i+f i))) (fun d=> Trio.unearned p hq w (Trio.rip (g d)) o U):=by
  apply Charm.rack; intro i hi; apply Charm.multiplies
  let a j:= Trio.emerge hq i j o; let Z j d:= masked p.threshold (neighbors w (a j)) (Trio.unit hq (Trio.rip (g d)) i j (a j)) U
  have hh j : Charm M (f i+f i) (Z j):= by
    unfold Z; by_cases hz: Healthy p.threshold (neighbors w (a j)) U
    · simp_rw [masked_eq _ _ _ _ hz]; let K:=Slide.shape (Trio.pad hq i) (a j) U; let z:Fly G (Qp i) p:= ⟨K,Trio.hint hq w U i (by omega) (a j) hz,[],by simp,by simp⟩
      exact Fly.hems (h i j) (hp i j) (hv i) z
    simp_rw [masked_ne _ _ _ _ hz]; exact Charm.nil (add_nonneg (hv _) (hv _))
  simpa only [sum_const,nsmul_eq_mul,card_univ] using! Charm.rack Finset.univ Z _ (fun i _ => hh i)
end YM.UVExtension.Concert
