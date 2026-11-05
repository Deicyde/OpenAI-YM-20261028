import YM.UVExtension.Linden.Life
import YM.UVExtension.Copse.Stooks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
open March Greenbelt Ursell Trees Concert Daisy.Charity
-- schedule price.Total d reset. K output Mark up to δ multiplier only.
def budgetsP (M:Leaf R)(Q:ConnectedActivityE6.Target G P)(d:ℕ):= 12 * (coined Q d * prices M d)
-- purchases.Scout. generalization smoothness.Hχ canonical.
local notation "O"=> Chi.canonical
variable (d0:ℕ)
def WorthP (Q:ConnectedActivityE6.Target G P) (W μ a x :ℝ) (j k:ℕ) (o:Target.Order G W) (L:Side) (η β:ℝ) (d0:ℕ):Prop:=
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Stamp T→ ∀ (U:BudgetPoint), U.order ≤ j→ U.threshold=temp x → U.power ≤ k → U.B=radiusB x → U.supportExponent+2≤ β→
    ∀ (_R: Rep G f) (H:Cash W x μ L Q o a T _R) (ι: Type) [Fintype ι], Fintype.card ι=d0→∀ (V:ι→Juice G f) (w:ℝ) (hF:Festa Q L H V w η) (J:(z:Canvas (betaF G x L) w ι) → Cash W x μ L Q o a T (freshen z _R V)), ∀ M:Leaf _R,∀ K:Lines _R V w (betaF G x L) M,∀ y,y∈M.crest.image S.ratio.parent →
    let T':= Concert.aperture hF
    (∀ d,Nonempty (Copse.Scent (Willow.worthZ H (k:=d) (α:=β)) T' (fun i=> Willow.offers (H:=H) M K O J i) (fun _=> budgetsP M Q d)) ∧ Nonempty (Atlas (Copse.nose (G:=G) (locus M H y) d U.B β) T' (fun i=> moods M K J U y i) (fun _=> budgetsP M Q d))) ∧ Nonempty (Atlas (cardsP (G:=G) U y (locus M H y) β) T' (fun d i t=> t.read (matin (mantle M K d) (J d) ((fleet d J H).furrow i) Chi.canonical)) (fun _=> betaF G x L*prices M 0))
-- Scent raise
private lemma gabs (X Y V D:Type) [NormedAddCommGroup V][NormedSpace ℂ V](P:Meter X Y) (T:Opening D V)(F:D→ℝ→P.Slot){f g:V→ℝ}(hp:∀ x∈T.span,f x ≤ g x)(h:Copse.Scent P T F f) :Nonempty (Copse.Scent P T F g):=by
    obtain ⟨Q⟩:= Lamppost.raiseCredit _ _ h.toAtlas hp; exact ⟨⟨Q,h.bright⟩⟩

open Height
set_option quotPrecheck false
lemma lives (Q:ConnectedActivityE6.Target G P)(U:Q.Expense):∃ M,∀ L:Side,M≤L.val→∀ (W μ a:ℝ) (j k N:ℕ)(ξ e η:ℝ) (o:Target.Order G W),0<W→0<μ→0≤a→0≤ξ → ξ<Q.exp→0<e→Q.rate+e<η→η<0→∀ᶠ x in atTop,WorthP Q W μ a x j k o L (betaF G x L^e) ξ N := by
   obtain ⟨M,hM⟩:= canopy Q; obtain ⟨L,hL⟩:= Mallow.adopter Q U
   refine ⟨max M L,fun l hl W μ a j k N ξ e η o hW hm ha hξ hv he hη hq=>?_⟩
   let r:= (Q.exp-ξ)/4; have hr:0<r:= by unfold r; linarith
   have hy:Q.rate≤η:=by linarith
   let P':= Wick.stalk Q hy hq
   obtain ⟨A,hA,hF⟩:= Festa.lodges he hη hq a ha N hr W hm (L:=l)
   by_cases h:∃ D:Patch,D.Branches P.bind G ∧D.L=l ∧ D.J=P.j
   swap; · exact Eventually.of_forall fun x c f S T hS U hU ht hz hr hp R H=> (h ⟨S.patch,H.laws.data.funds.funds.kernel,H.laws.data.funds.length_eq,H.laws.data.funds.funds.atStep⟩).elim
   obtain ⟨D,hD,hd,h⟩:= h
   obtain ⟨Z,hZ,hS⟩:= March.oar G j; let t x := 2*Pressure.fiery G x l
   have he' : Rate G l (-(1/2)) t:= Rate.flame.mul_left 2
   let v x := ((j:ℝ)+1)*Z*t x
   have hh : Rate G l (-(1/2)) v:= he'.mul_left _
   have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G l).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
   obtain ⟨θ₁,θ₂,h₁,h₂,h₃⟩:= hM l ((le_max_left ..).trans hl) D Chi.canonical W μ o hD hW hm v hh (hp.mono fun x h=>by unfold v; positivity) N j η e r hr (by unfold r; linarith) he hη hq
   have hℓ1 : Rate G l 0 shiftG:= (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
   let g x:=2*collars G r x j k*((2:ℝ)^j*θ₂ x*(1-1/2)⁻¹); have hℓ2: Rate G l 0 g:=by
      have h:= ((hℓ1.pow (k*j)).mul_right (Reserves.polyPrice r (k*j))).mul_left 2; simpa only [zero_mul,zero_add] using! h.mul (((h₂.mul_left ((2:ℝ)^j)).mul_right (1-1/2)⁻¹))
   have heL : Rate G l 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul,add_zero] using! (Census.width_rate G l 1 0)
   have htW : Rate G l η (fun x=> degreePrice (radiusB x) ((2:ℝ)^j*θ₁ x) r):=by
      have h:= heL.mul (h₁.mul_left ((2:ℝ)^j)); rw [zero_add] at h; simpa only [degreePrice,Trees.stretch,div_eq_mul_inv] using! ((h.mul_right r⁻¹).mul_left 4)
   filter_upwards [mottled (G:=G) (L:=l) hr, hF,h₃,hℓ2 1 zero_lt_one, htW.below hq _ (by norm_num : (0:ℝ)<1/2),hp,P'.certify l hm 0 r r hr hr,hL l ((le_max_right ..).trans hl) W o μ j k hW hm] with x hP hF hK h₀ hx hS' hr' hX
   intro c f S T hσ p hp ht hyK hf h R H ι inst hN V Y hY J M K y hz T'
   let bC:= hF c f S T o R H ι V hN Y hY
   have heA:= chartH H hσ hX|>.2; have hc : ξ+r+r ≤ Q.exp-r:=by unfold r; linarith
   have ht0:0<betaF G x l:=altitude (H:=H)
   constructor
   · intro d
     have hz':= capitalSup d (H:=H) hX.1 heA M
     obtain ⟨P⟩:= ample hY M K bC hP d Chi.canonical J hξ hr hr hc hr'.2.2.2.1 hr'.2.2.2.2 hr'.2.2.1
     obtain ⟨E⟩:= travels hX hσ hY M K J p y ht bC hP hf hξ hr (by linarith only [hc,hr]) hr'.2.2.2.1 d
     have hk : 0 ≤ ceiling (H:=H) d M:= mul_nonneg M.profit (Real.exp_pos _).le; unfold budgetsP
     exact ⟨gabs _ _ _ _ _ _ _ (by intro i _; norm_num; linarith only [hz',hk]) P,Lamppost.raiseCredit _ _ E (by intro i _; norm_num; linarith only [hz',hk])⟩ -- add const.Monotonic
   obtain ⟨A,b,B,C,r',d,n,K',V₀,Z',c',M',k',hv,hq,hM,U0,hM'⟩:= hK
   have hx' : S.patch=D:= H.laws.data.funds.patch hd ‹D.J=P.j›
   let D':= hM' c f S T a R H hσ hx'.symm _ hN V Y hY
   have hc : 0 < Outliner.award G P' x V₀ Z' r' l μ j k':= by
      obtain ⟨i⟩:= canvas_nonempty (ι:=ι) ht0 hY.margin; let t:=(Concert.aperture hY).call i; have hv:= (Concert.aperture hY).within i; have hh:=(Outliner.dealP _ hY D' t hv).conduit.active
      have he:= D'.good; have ha:= D'.size; exact mul_pos (mul_pos (zero_lt_one.trans_le ha) (by positivity)) (P'.overture_pos x (k'+j) ht0)
   have hC1: Pressure.temp x ≤ t x:= by have he:= H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at he; exact he
   have hS: Sailor G p.threshold (Z*t x) j:= ⟨fun c A hA=> hS c _ hS'.le A (hA.trans (ht.trans_le hC1))⟩
   obtain ⟨X'⟩:= bray (A:=A) (hx'.symm ▸ U0) hσ hY M K hM D' J hξ hr hr ‹ξ+r+r≤_› hc (hv ▸ (show degreePrice _ _ _ ≤ _ from (le_abs_self _).trans hx)) y p ht hp hS (mul_nonneg hZ.le hS'.le) (by unfold v; nlinarith only [mul_nonneg hZ.le hS'.le]) (conscious hX hσ M K J p y hz hp ht) hz k hyK hf
   have he:= capitalsE M hM hY _ D' hX.1 heA
   refine Lamppost.raiseCredit _ _ X' (fun i hi=>?_) -- q ge
   have hh:0 ≤ 2*collars G r x j k:=by unfold collars Reserves.polyPrice shiftG; positivity
   let h':= le_abs_self (g x); have hz':g x≤ betaF G x l:= (h'.trans h₀).trans_eq (Real.rpow_one _); unfold g at hz'; rw [hq] at hz'
   refine ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (2:ℝ)^j)) (by norm_num : 0≤ (1-1/2:ℝ)⁻¹)) hh)).trans ?_; apply le_trans _ (mul_le_mul_of_nonneg_right hz' (show 0≤prices M 0 from mul_nonneg M.profit (Real.exp_pos _).le)); exact le_of_eq (by ring)
end YM.UVExtension.Linden
