import YM.UVExtension.Concert.Ladle
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
open Trio

section skyline
variable {C:Listing G c}(P:D→ Collection.Source G c)
    {α:ℝ} (h: ticketR M p C.reg α (fun d=> (P d).logRead) (fun _=> b)) (Y': D→ Collection.Source G c)(Z':ℕ→ Prop) [DecidablePred Z']
-- E subsigns pre-market.
include h
lemma blackout (he:∀ i k,(Y' i).logRead k=if Z' k then 0 else (P i).logRead k) (hh:∀ i,smoothP p C.reg (P i).logRead) :
    (∀ d,smoothP p C.reg (Y' d).logRead)∧ Nonempty (ticketR M p C.reg α (fun i=>(Y' i).logRead) (fun _=> b)) :=by
  let f (z:Y)(a:ℕ):= if Z' a then 0 else h.f z a
  have hf z i: p.Regular (C.reg i).support ((Y' z).logRead i):= by rw [he]; split; exact CouplingShape.reg_const _; exact hh z i
  refine ⟨hf,⟨⟨f,fun d i k=> ?_,fun i k=> ?_,fun z hz=>?_⟩⟩⟩
  · let k':= show Tap p G _ _ from k; change f (M.call d) i k=↑(Tap.read k' ((Y' d).logRead i)); rw [he]; unfold f; split; next =>
      change 0= (↑(leftDerivs (fun _:Config G c=> (0:ℝ)) k'.poll k'.view):ℂ)
      rw [show leftDerivs _ _ k'.view=_ from Work.G07.left_const 0 k'.poll k'.view]; split <;> rfl
    exact h.exacts ..
  · unfold f; split; exact bumps _ _ (differentiableOn_const _); exact h.pulse i k
  obtain ⟨w,hw,hb⟩:= (h.bounds z hz).afloat
  refine ⟨w,fun i=> ⟨(hw i).1,fun k=>?_⟩,hb⟩; unfold f; split; exact norm_zero.trans_le (hw i).1; exact (hw i).2 _
end skyline

section enrollment
variable {κ r z w : ℕ} (Φ:Site c) (U:D→ Trio.Offer G c) {f:D→ ∀ i:Stars,Trio.Offer G ((fun _=>c) i)}
lemma tribute (hp:∀ (o:Site c) (x:Tap p G o (neighbors z o)), Charm M b (fun d=> x.read (U d o))) (h:∀ i:Site c, (coverNumber p.B (neighbors z i):ℝ) ≤ W) (hv:0≤ b) : Nonempty (ticketR M p (leap z) (preExponent p) U (fun _=>Real.exp (preExponent p*W)*b)):=by
  choose g he hs ht using fun i w=> (hp i w).claim
  refine ⟨⟨fun z i k=> g i k z,fun d i k=> hs i k d,fun i k=> he i k,fun q hq=> ⟨fun _=> b,fun i=> ⟨hv,fun k=> ht i k q hq⟩,fun i=>?_⟩⟩⟩
  simp only [fork,ite_mul,zero_mul]; refine budget_finite (fun t=> ?_) ?_
  · split <;> positivity
  rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _)]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (h i) (headline p).exponent_pos.le)) hv
variable (C: Listing G c) (Y':D→ Collection.Source G c)
lemma rough (h:∀ i : Site c,(coverNumber p.B (neighbors w i):ℝ) ≤ W) (g: D → Trio.Offer G c) (hp:∀ (i:Site c) (x:Config G c),Charm M b (fun d=> U d i x)) (hv:0 ≤ b) (hx : tithe w b p W ≤ e) : Nonempty (Atlas
    (softer (lodge C z w) p.B (p.supportExponent+1+1)) M (fun d i x=> (bison (Y' d) (g d) (U d)).logarithm i x) (fun _=>e)) :=by
  let f(i) (x: Config G c) d:= (bison (Y' d) (g d) (U d)).logarithm i x
  have hf (i) (x:Config G c): Charm M (tract c b (leanU c i)) (f i x):= by
    unfold f bison Function.comp; dsimp only; rcases leanU c i with i|i; · exact Charm.nil le_rfl
    let z:= i.1; let t:=i.2; have hh:= ((hp t (z.view x)).multiplies (-Rim c)); rw [abs_neg, abs_of_nonneg (rim_nn _)] at hh; convert hh using 1; rfl
    funext j; change Rim c * (-(_ : ℝ)) = _; simp only [neg_mul,mul_neg]; rfl
  choose f' H he hm using fun i x=> (hf i x).claim
  refine ⟨⟨fun t' i x=> f' i x t',fun d i x=> he i x d,fun i x=> H i x,fun t' hz=>?_⟩⟩
  have hh := caps C z w p b hv h
  refine ⟨_,fun i=>⟨hh.1 i,fun x=>hm i x _ hz⟩,(soot ..).2 (fun i=> budget_loosen (show SumBudget _ (tithe w b p W) from hh.2 i) hx)⟩
lemma blastoff (Y' : D→ Collection.Source G c) (g t:D→ Trio.Offer G c)
    (hp:∀ d,smoothP p C.reg (Y' d).logRead)(hg:∀ d,smoothP p (leap z) (g d))
    (hP:ticketR M p C.reg (preExponent p) (fun d=> (Y' d).logRead) (fun _=>a)) (hG:ticketR M p (leap z) (preExponent p) g (fun _=>b))(hb:0≤b)(w:ℕ) :
    (∀ d,smoothP p (pluck p (lodge C z w)).reg (poursP p (lodge C z w) (bison (Y' d) (g d) (t d))).logRead) ∧
    Nonempty (ticketR M p (pluck p (lodge C z w)).reg (preExponent p) (fun d=> (poursP p (lodge C z w) (bison (Y' d) (g d) (t d))).logRead) (fun _=>a+4*turnFee p*b)):=by
  have hh d: smoothP p (revolve (leap z)) (choir (g d)):= fun i=> CouplingShape.reg_scale (Rim c) (Seat.regular i.1 (hg d i.2))
  obtain ⟨F⟩:= revolving _ _ hg hG (fun z _=> ⟨hb,le_refl b⟩) hb hh; obtain ⟨J⟩:= bundled _ _ _ _ hP F; refine ⟨fun d i=> ?_,relocated _ _ (leanU c) J⟩
  suffices he:∀ (i:Civ c), p.Regular ((Sum.elim C.reg (sea z) i).support) ((Sum.elim (Y' d).logRead (choir (g d)) i)) from he _
  rintro (i|i); exact hp _ _; exact hh _ i
end enrollment
end YM.UVExtension.Concert
