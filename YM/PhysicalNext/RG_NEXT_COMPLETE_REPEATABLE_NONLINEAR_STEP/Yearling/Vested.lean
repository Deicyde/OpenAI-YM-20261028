import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Basin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Elixir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter
/-! # One family of k.Kinn across any new R. Exact reattachments, use stricter Seed
    definition retained at β'. Expenditure stable on H.C calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March
open Gas Ursell Trees Alabaster Match Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {x μ C v : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}
variable (Θ : Year H j v χ)
include Θ

lemma ovulation : ∃ K : ℝ,0 ≤ K ∧∃ ν' : ℝ,0<ν'∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ ν' →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→∀ (X:Match.Alliance H H' 1 0), X.units= Equiv.refl _→
   ∃ f:H.ThinP→ℝ, SumBudget f K ∧∀ p U,Healthy (Pressure.temp x) (H.smallAt p) U→ Ore U (fun V=>leaflet H' χ V (X.bearing p)-leaflet H χ V p) v (t*f p) j := by
  obtain ⟨M,hM,s,hs,h⟩:= rimfire Θ.year
  refine ⟨M,hM,s,hs,?_⟩; intro I a b t hp ht hv H' Hx X hX; obtain ⟨g,hg,hQ⟩:=h I a b t hp hv ht C H' Hx.year
  refine ⟨g ∘ Subtype.val,budget_pull Subtype.val Subtype.val_injective hg,?_⟩; intro p U h E _ _ _ V y hr hx
  letI:Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  let G' (i: Reserve S):= prism T x χ o.K U (Greenbelt.allot i)
  let F R q B t:= fringe (vary B (V t)) (F:=Greenbelt.allot q) (T:=T) W o.a p.val R Q.table Q.halo -- argument F not matching let dependent
  have hz (i:Reserve S):= hQ (Greenbelt.allot i) (G' i) rfl rfl rfl p.val p.2.2 h E V y hr hx
  have he (i:Reserve S):Brush j (t*g p.val) 1 (fun y=> F I i (G' i) y - F R i (G' i) y) y:=hz i
  apply (Captain.avgBrush (fun i y=> F I i (G' i) y - F R i (G' i) y) _ y he).shimmy
  refine Eventually.of_forall fun u=> ?_; unfold leaflet; dsimp only [Function.comp_apply]; rw [show (X.bearing p).val=p.val from congr_arg (fun e: Molecule S≃Molecule S=> e p.val) hX]
  unfold likely F; dsimp only; rw [← mul_sub, sum_sub_distrib]; rfl

lemma eventide : ∃ M : ℝ,0 ≤ M ∧∃ s : ℝ,0<s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→∀ (X:Match.Alliance H H' 1 0), X.units= Equiv.refl _→
   ∃ f:H.fragrances→ℝ, SumBudget f M ∧∀ p U,Healthy (Pressure.temp x) (Song.perf H p) U→ Ore U (fun V=> stream H' χ V (X.furrow p)-stream H χ V p) v (t*f p) j := by
  obtain ⟨K,hK,s,hs,h⟩:= ovulation Θ; let N:= Θ.net; have he : Armada Q L μ 0 x Θ.A Θ.h j Θ.r:= Θ.pay; have hk:= he.purchases N
  let r:= Θ.h; let z (p:H.ThinP):= r*N.conduit.meant p.val Θ.r; have hp p:0≤z p:= mul_nonneg N.balance (N.conduit.meant_nonneg Θ.r p.val)
  obtain ⟨k,hK',hE⟩:= comforts _ _ _ z hk hK; let X:= salary Q L μ Θ.h x j Θ.r; have hA:0<X:=hk.1
  let C':= ((c.val^4:ℕ):ℝ)*(X+X/2)*(1-3/4)⁻¹
  have hc:0 ≤ C':= by unfold C'; norm_num; positivity
  refine ⟨k⁻¹*C',mul_nonneg (inv_pos.mpr hK').le hc,min k s,lt_min hK' hs,?_⟩; intro I a b t hp' ht hu H' hV X' hx; obtain ⟨f',hf,hU⟩:=h I a b t hp' (ht.trans (min_le_right ..)) hu H' hV X' hx
  let w p:= (z p+k*f' p); have hw p: 0 ≤ w p:= add_nonneg (hp p) (mul_nonneg hK'.le (hf.1 p)); let Z p:=2^j*w p; have hZ i : 0 ≤ Z i:=mul_nonneg (by positivity) (hw _)
  let F(p:H.fragrances):=clusters H.seam Z p.snd; have hm := Gas.absolute H.seam Z _ _ H.testS (fun i => i.2.1) (add_nonneg he.gain he.delta.le) (show Ready H.smallAt _ (fun i=>‖Z i‖) _ _ _ _ from (by simp_rw [Real.norm_of_nonneg (hZ _)]; exact hE _ hf))
  have hx' p: ‖Gas.term H.seam Z p‖=F p:= by unfold F; rw [Gas.term_nonneg]; simp_rw [Real.norm_of_nonneg (hZ _)]
  have hF: SumBudget F C':= by simp_rw [hx'] at hm; exact hm
  refine ⟨fun i=> k⁻¹*F i,budget_scale (inv_pos.mpr hK').le hF,?_⟩; intro p U ht' E _ _ _ V y hy hv
  let v:= t*k⁻¹; have he: 0≤ v:=mul_nonneg hu.le (inv_pos.mpr hK').le
  have heq i: t*f' i=v*(k*f' i):= by unfold v; field_simp
  let f i y:= leaflet H χ (V y) (p.snd i); let g i y :=leaflet H' χ (V y) (X'.bearing (p.snd i)); let Y i:= z (p.snd i); let J i:= k*f' (p.snd i)
  have hJ i : Healthy (Pressure.temp x) (H.smallAt (p.snd i)) U:=Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ p.snd) (mem_univ _)) ht'
  obtain ⟨hx',hy'⟩:= lapride j univ f g Y J y he ((mul_le_mul_of_nonneg_right (ht.trans (min_le_left ..)) (inv_pos.mpr hK').le).trans_eq (mul_inv_cancel₀ hK'.ne')) (fun i _=> ((N.collective ..).2 (hJ i)) E V y hy hv) (fun i _=> by unfold J; rw [← heq]; exact hU _ U (hJ i) E V y hy hv) (fun i _=> mul_nonneg hK'.le (hf.1 _))
  let n:= p.fst+1; let A:=coefficient H.seam p.snd; let a':= A / p.fst.succ.factorial
  let v₁:= ∏ i,w (p.snd i)
  apply ((hy'.smul a').trim.climb _ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
  · have ha := mul_le_mul_of_nonneg_left (sub_le_self v₁ (show 0 ≤ ∏ i,z (p.snd i) from prod_nonneg fun i _=> hp (p.snd i))) he
    simp only [card_univ,Fintype.card_option,Fintype.card_fin]
    have hh : (1+(n:ℝ))^j≤(2^j:ℝ)^n:= by rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=n)
    refine ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show v* (v₁-∏ i,z (p.snd i))≤ v*v₁ from ?_) (norm_nonneg a')) (by positivity : 0 ≤ (1+(n:ℝ))^j)).trans (mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg _) (mul_nonneg he (prod_nonneg fun i _=> hw (p.snd i)))))).trans_eq ?_
    · exact ha
    unfold a' v₁ F clusters Z; rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin,Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ (p.fst.succ.factorial:ℝ))]; unfold v n A; ring
  · have hx := Match.sale X'.bearing (fun j=>leaflet H' χ (V i) (X'.bearing j)) (leaflet H' χ (V i)) X'.sec (fun _=>rfl) p
    change Gas.term H'.seam _ _-Gas.term H.seam _ _= a' *((∏ t,g t i)-∏ t,f t i)
    rw [← hx]; unfold g f a' A Gas.term; ring
end YM.PhysicalNext.Repeat.Yearling
