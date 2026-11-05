import YM.FullVolume.Florid.PagesE
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
open Lyre Charity Blaze.March
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
set_option quotPrecheck false
local notation "τ"=> V.pole.turn.badge S
local notation "Q'" => Empire.stella Q
local notation "Φ"=> jewelDebt V.pole (Empire.stella Q) L x₀
local notation "B₀" => radiusB x₀
local notation "π"=> Lyre.spicesF G (r+fq) L' (V' x₀) K j
-- selected under stellar props. Keep Φ factors integrated outside tree.
local notation "hτ" => lushE M V α ν (π) p (k+j)
open Greenbelt
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Match
local notation "F'"=> M.payment (k+j) (spicesF G r L' (V' x₀) K j) ν α p
local notation "μ₁"=> fun i:H.ThinP=> 2* (F' i.val)+2*(hτ i)
def chargeM (Y B α ν:ℝ) (k:ℕ)(p:Signal j)(i:H.ThinP):= 2*(M.payment k Y ν α p i.val)+2*(lushE M V α ν B p k i)
local notation "g₁"=> V
local notation "ι"=> H.fragrances
abbrev hopes (Y B α ν:ℝ)(k:ℕ)(p:Signal j)(x:H.fragrances) := clusters H.seam (fun i=>(2:ℝ)^(j+2)*chargeM M V Y B α ν k p i) x.2
local notation "e₁"=> hopes M V (spicesF G r L' (V' x₀) K j) (π) α ν (k+j) p
abbrev signalAt (q:Chi)(t:sun)(p:H.fragrances) (x:Config G c):= matin (V.flies t) (U.beams t (U.lay t.property)) ((Jams.recital U t).furrow p) q x
lemma taxis (t:sun) (q:Chi) (Y:Cash W x₀ μ L Q o C T (U.notes t.val))(A: Alliance H Y 1 0) (he:A.units=Equiv.refl _)(p:H.fragrances) x: matin (V.flies t) Y (A.furrow p) q x=Ursell.coefficient H.seam p.snd / (p.1+1).factorial * ∑ i, (∏ b ∈ univ.erase i, Lyre.fruit (χ:=q) (U:=U) (p.2 b) (t:ℝ) x) * escort (V.flies t) q Q.table (p.2 i).val Q.halo T W x₀ o.K o.a x:=by
    rcases p with ⟨i,Vx⟩; unfold matin; have hp(s:H.ThinP):(A.bearing s).val=s.val:=by change A.units s.val=s.val; rw [he]; rfl
    rw [Match.weighs A.bearing A.sec (⟨i,Vx⟩:H.fragrances)];
    apply congr_arg; apply Finset.sum_congr rfl; intro j _; apply congr_arg₂ (·*·); · exact prod_congr rfl fun i _=> (Lyre.light Y A he _ x).symm
    unfold libs; change escort _ _ _ (A.bearing (Vx j)).val ..= _; rw [hp]
lemma charges (t:sun) (q:Chi) (p:H.fragrances) x: signalAt V q t p x=Ursell.coefficient H.seam p.snd / (p.1+1).factorial * ∑ i, (∏ b ∈ univ.erase i, Lyre.fruit (χ:=q) (U:=U) (p.2 b) (t:ℝ) x) * escort (V.flies t) q Q.table (p.2 i).val Q.halo T W x₀ o.K o.a x:= taxis V t q _ _ rfl p x
lemma reaches (t:sun)(p:H.fragrances) : (U.beams t (U.lay t.property)).bookFoot (.inr ((recital U t).furrow p))=H.bookFoot (.inr p):=by
   have hx:= (recital U t).alcove (.inr p); rw [show Lattice.affine 1 (0:Site c)=id from funext fun u=> by simp [Lattice.affine],image_id] at hx; exact hx
lemma soaks (t:sun){Y:Cash W x₀ μ L Q o C T (U.notes t.val)}(A:Alliance H Y 1 0)(he:A.units=Equiv.refl _)(p:H.fragrances): speaks V.pole H p ↔speaks (V.flies t) Y (A.furrow p):=by
   rcases p with ⟨i,p⟩; unfold speaks; have hp(s:H.ThinP):(A.bearing s).val=s.val:=by change A.units s.val=s.val; rw [he]; rfl
   rw [V.kind];change (∃ j, τ ∈ (p j).val ∧ troupe T R Q.halo B₀ _)↔ ∃ j, τ∈ (A.bearing (p j)).val ∧ troupe T (U.notes t) Q.halo B₀ (A.bearing (p j)).val; simp_rw [hp,U.troupe_hold t (U.lay t.property)]
lemma reached (t:sun)(p:H.fragrances): speaks V.pole H p ↔speaks (V.flies t) (U.beams t (U.lay t.property)) ((Jams.recital U t).furrow p):= soaks V t _ rfl p
lemma poleL(t:sun)(p:H.fragrances)(y:Site c): locus (V.flies t) (U.beams t (U.lay t.property)) y ((Jams.recital U t).furrow p)=locus V.pole H y p:=by
    unfold Charity.locus; rw [← reached,reaches]; -- ambiguity
-- local identity on ALL V not by assumed roster
lemma historic (R:Leaf R)(J:H.fragrances): LocalOn (H.bookFoot (.inr J)) (matin R H J χ):=by
   intro V V' hv; let f(i:Option (Fin J.fst)):= J.2 i; have hp(i): H.smallAt (f i)⊆H.bookFoot (.inr J):= Finset.subset_biUnion_of_mem (H.smallAt ∘ J.snd) (mem_univ i)
   unfold matin; apply congr_arg; apply sum_congr rfl; intro i _; apply congr_arg₂ (·*·) (prod_congr rfl fun j _=> (Captain.arrived (J.snd j)).2.1 _ _ (agrees_mono hv (coe_subset.mpr (hp j))))
   unfold Charity.libs escort; apply congr_arg likely; funext p
   let W:= Greenbelt.prism T x₀ χ o.K V (Greenbelt.allot p); exact (R.tailSpin W _ H.laws.intake H.laws.data.room H.laws.data.access Q.table_exists Q.buys).2.1 V V' (agrees_mono hv (coe_subset.mpr (hp i)))
variable (hp:foam Q L)(hb:R.p.B≤2*radiusB x₀)(hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))
variable (hv:2≤ v)
include hp hb hA hc D M hr W' Y' hv
lemma energy (x:H.fragrances):0 ≤ e₁ x:=by
    refine clusters_nonneg _ (fun i=> mul_nonneg (by positivity) (?_)) _; exact add_nonneg (mul_nonneg zero_le_two (M.paid_sky ..)) (mul_nonneg zero_le_two (prosp M V D hc hp hb hA _))
set_option maxHeartbeats 450000 in
lemma celia (P : ι) (V'':Config G c)(hz:Healthy (Pressure.temp x₀) (H.bookFoot (.inr P)) V'') (w:Rung)(η:ℝ)(hK:Stripe w (v/2) η):Ore V'' (fun x=> Jams.mix w (fun t=> signalAt V χ t P x)) u (FullVolume.Ray.Weigh.pattern j * η * (Φ* (e₁ P))) j:=by
    intro E _ _ _ U₀ y hy hU
    let A(v:H.ThinP):= μ₁ v
    let Hf j t x:= Lyre.fruit (U:=U) (χ:=χ) (P.2 j) t (U₀ x)
    let Hg j x (t:sun):= escort (V.flies t) χ Q.table (P.2 j).val Q.halo T W x₀ o.K o.a (U₀ x)
    let F j t x:= (∏ b∈univ.erase j,Hf b t x)* phraseS (Hg j x) t
    have hZ i: Healthy (Pressure.temp x₀) (H.smallAt (P.2 i)) (U₀ y):= by rw [hy]; exact Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ P.2) (mem_univ i)) hz
    have hF i: Weigh j y (v/2) (A (P.2 i)) 1 (Hf i):= (M.grill W' hc hr Y' hv (P.2 i) (hZ i) hU).loses (le_add_of_nonneg_right (mul_nonneg zero_le_two (prosp M V D hc hp hb hA _))) le_rfl
    have hG i: Weigh j y (v/2) (2*(Φ*hτ (P.2 i))) 1 (fun t x=>phraseS (Hg i x) t):= Mill.stations y _ _ hv (mul_nonneg (scentL V.pole H|>.2.1) (prosp M V D hc hp hb hA _)) fun w v hw=> ((rocketsL M V D hc hr W' Y' w v hw hp hb hA _ _ (hZ i)) E U₀ y rfl hU)
    let p':= (η*Φ)*(∏ i,A (P.2 i))*(1+((P.1+1:ℕ):ℝ))^j; let P₁:= FullVolume.Ray.Weigh.pattern j
    have ha(i):0≤A (P.2 i):=(hF i).nonneg -- edit
    have hx(i): Brush j (P₁ * p') 1 (fun x=> FullVolume.Ray.trace w (fun t=> F i t x)) y:=by
       have hh: 2*(Φ*hτ (P.2 i)) ≤ Φ*A (P.2 i):=by
         rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg zero_le_two (M.paid_sky ..))) (scentL V.pole H|>.2.1)
       apply (((FullVolume.Ray.Weigh.prod (univ.erase i) Hf (fun i=> A (P.2 i)) (fun _=>1) (by linarith) (fun i _=> hF i)|>.dual ((hG i).loses hh le_rfl)).timber w η hK).trim).climb ?_ le_rfl; simp only [p',sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel]
       rw [← Finset.mul_prod_erase _ _ (mem_univ i)]; push_cast; unfold P₁; apply le_of_eq; ring
    let s:=P.1+1; -- edit
    let b:= coefficient H.seam P.snd / (s.factorial:ℝ)
    have ht := (Brush.spree Finset.univ _ (fun _=>P₁ * p') zero_le_one (fun i _=>hx i)).smul b
    apply (ht.climb ?_ le_rfl).shimmy (Eventually.of_forall fun x=>?_) -- angle.LT
    · rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin]; unfold p'
      let a:=(∏ i,A (P.2 i)); have ha':0≤a:=prod_nonneg fun i _=> ha i; have hC: (s:ℝ)*(1+(s:ℝ))^j≤(2^(j+2):ℝ)^s:=by
          have hj:1+(s:ℝ)≤ (2:ℝ)^s:=by rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=s)
          calc
            _ ≤ 2^(2*s)*((2^s:ℝ)^j) := by gcongr; exact (le_add_of_nonneg_left zero_le_one).trans (hj.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
            _ = _ := by simp_rw [← pow_mul, ← pow_add]; ring_nf
      have he:0≤η:= stripe_pos hK; have hp:0≤P₁:= Finset.sum_nonneg fun i _=>zero_le_one.trans (Planned.AtomRegular.polar_one _)
      unfold hopes clusters; let x:=‖b‖*P₁*η*(a*Φ); refine le_trans (le_of_eq (show ‖b‖ * ((s:ℝ)*(P₁ * ((η*Φ)*a*(1+(s:ℝ))^j)))= x*((s:ℝ)*(1+(s:ℝ))^j) from (by unfold x; ring))) ((mul_le_mul_of_nonneg_left hC (show 0≤x from by unfold x; have hx:=scentL V.pole H|>.2.1; positivity)).trans_eq ?_);
      simp only [x,b,Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity:0≤(s.factorial:ℝ)),prod_mul_distrib,prod_const, card_univ,Fintype.card_option,Fintype.card_fin]
      unfold P₁ a; unfold s; change _= FullVolume.Ray.Weigh.pattern j * η * (Φ*( _ * (_*∏ i, A (P.snd i))/_ )); ring
    dsimp only; unfold mix; simp_rw [charges V,smul_eq_mul]; unfold FullVolume.Ray.trace F; simp_rw [phrased,smul_eq_mul]; rw [sum_comm (s:=univ),mul_sum]; refine sum_congr rfl fun t _=>?_ ; rw [mul_left_comm]; apply congr_arg (b*·); rw [Finset.mul_sum] <;> rfl
end Mill
end YM.ConnectedActivityE6.Empire.Imago
