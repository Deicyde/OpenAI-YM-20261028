import YM.RG08.Yamen.Penny

/-! # Cost translations at a step from the quantified quadratic kfalt law and only pledged
 length/post entries. Use for both same & pairs.
-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason RG08.Supplies
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{c:Patch}{k:KernelChoices}{A A':Bed}{p:ℝ}
private lemma key_nn (c:Patch)(k:KernelChoices):0 ≤ Cell.key G c k:=by unfold Cell.key; have he:= k.penalty_pos; have hz:= (Cell.probes_on c k G).pos; positivity
private lemma delta_ice {θ D:ℝ}(h:Priced θ D (Line.warm c k G A-Line.warm c k G A')):Priced θ D (Prism.ice c k (G:=G) A- Prism.ice c k (G:=G) A'):=by
 convert priced_winter (U:=Loc G 1) (R:=Loc G 1) h using 1;funext (a : Market (Head c G)) b;obtain ⟨i,a|a⟩:=a <;> obtain ⟨i,b|b⟩:=b <;> simp [Prism.ice,winter]
private lemma delta_rain {θ η D g:ℝ}(h:Priced θ D (Line.warm c k G A-Line.warm c k G A'))(hi:Cell.Warm G k c A η g)(hq:Cell.Warm G k c A' η g)(he:0<θ)(hv:θ ≤ η)(hη:η ≤1): Priced θ (Cell.key G c k*D) (Prism.rains c k (G:=G) A-Prism.rains c k (G:=G) A'):=by
 convert priced_chill (U:=Loc G 1) (Cell.hot_gap hq hi he.le hv hη h) using 1
 funext (a: Market (Head c G)) b;obtain ⟨i,a|a⟩:=a <;> simp [Prism.rains,chill]

-- w ∈ Strip current. A,A' *fine* both. grade inputs arbitrary cutoff i=i horizon. telescope Ω under allowance.
private lemma ribbons {σ p ε θ δ W B :ℝ}{c:Patch}{k:KernelChoices}{u v:Clip}{Q:MapPrices}
   (h:Cell.Warm G k c A σ p)(h':Cell.Warm G k c A' σ p)(hp:σ ≤ 1)(hT:∀ n,Floor A u n (Q.η c.J) B)(hT':∀ n,Floor A' v n (Q.η c.J) B)(hr:A.metric.strip (Q.α c.J) B)(hr':A'.metric.strip (Q.α c.J) B)
   (hv:RowCost ε 1 (Cell.changeK A' A) δ)(he:0 ≤ δ)(hh:0<θ)(hθ:θ ≤ min σ (c.L.val*ε))(hk: 1 ≤ W)(h0:p ≤ W)(h1:Cell.key G c k ≤ W)(h2:Cell.allowance G c p ≤ W)(hB:0≤B):
   Priced θ W (Prism.ice (G:=G) c k A) ∧ Priced θ W (Prism.ice (G:=G) c k A') ∧ Priced θ (W*δ) (Prism.ice (G:=G) c k A-Prism.ice (G:=G) c k A') ∧
   Priced θ (2*W^2) (Prism.rains (G:=G) c k A) ∧ Priced θ (2*W^2) (Prism.rains (G:=G) c k A') ∧ Priced θ ((2*W^2)*δ) (Prism.rains (G:=G) c k A-Prism.rains (G:=G) c k A'):=by
 have hs:=hθ.trans (min_le_left ..);have hσ:=hh.trans_le hs
 obtain ⟨γ,a⟩:=ready_roads c k A h hσ hp
 obtain ⟨γ',a'⟩:= ready_roads c k A' h' hσ hp
 have hx := Cell.earn_grid G k c _ _ h' h hT' hT hv he hr' hr (Q.alpha_pos _).le hB hh.le hs (hs.trans hp) (hθ.trans (min_le_right ..))
 have ht: Priced θ (W*δ) (Line.warm c k G A-Line.warm c k G A'):= hx.mono le_rfl (mul_le_mul_of_nonneg_right h2 he)
 have hW:0≤W:=zero_le_one.trans hk
 have hl:0≤Cell.key G c k:=key_nn ..
 have H0:p* Cell.key G c k+1 ≤ 2*W^2:=by nlinarith [mul_le_mul h0 h1 hl hW]
 exact ⟨γ.toPriced.mono hs h0,γ'.toPriced.mono hs h0,delta_ice ht,a.toPriced.mono hs H0,a'.toPriced.mono hs H0,(delta_rain ht h h' hh hs hp).mono le_rfl (by nlinarith only [mul_le_mul_of_nonneg_right h1 (mul_nonneg hW he), mul_nonneg he (sq_nonneg W)])⟩

 lemma viable {σ p ε θ δ W B : ℝ}{c:Patch}{k:KernelChoices}{u v:Clip}{Q:MapPrices}
   (h:Cell.Warm G k c A σ p)(h':Cell.Warm G k c A' σ p)(hp:σ ≤ 1)(hT:∀ n,Floor A u n (Q.η c.J) B)(hT':∀ n,Floor A' v n (Q.η c.J) B)(hr:A.metric.strip (Q.α c.J) B)(hr':A'.metric.strip (Q.α c.J) B)
   (hv:RowCost ε 1 (Cell.changeK A' A) δ)(he:0 ≤ δ)(hh:0<θ)(hθ:θ ≤ min σ (c.L.val*ε))(hk: 1 ≤ W)(h0:p ≤ W)(h1:Cell.key G c k ≤ W)(h2:Cell.allowance G c p ≤ W)(hB:0≤B):
   Priced θ W (Prism.ice (G:=G) c k A) ∧ Priced θ W (Prism.ice (G:=G) c k A') ∧ Priced θ (W*δ) (Prism.ice (G:=G) c k A-Prism.ice (G:=G) c k A') ∧
   Priced θ (2*W^2) (Prism.rains (G:=G) c k A) ∧ Priced θ (2*W^2) (Prism.rains (G:=G) c k A') ∧ Priced θ ((2*W^2)*δ) (Prism.rains (G:=G) c k A-Prism.rains (G:=G) c k A'):= ribbons (Q:=Q) h h' hp hT hT' hr hr' hv he hh hθ hk h0 h1 h2 hB

variable {O:Type}{Γ:O→Patch}(Z:ChartRatio G){P Q:MapPrices}{D:Exchange O}{w p δ:O→ℝ}{F B:O→Bed}
lemma arms (hV:D.Good p)(hU:∀ i,Posts G P Q k Z (Γ i).J (Γ i) (p i))
    (ha:∀ i,Cell.Warm G k (Γ i) (F i) (PlanCurve G k P (Γ i).J) (planSupply G k P (Γ i).J (Γ i).L)) (ha':∀ i, Cell.Warm G k (Γ i) (B i) (PlanCurve G k P (Γ i).J) (planSupply G k P (Γ i).J (Γ i).L))
    (hs:∀ i,∃ v:Clip,∀ n,Floor (F i) v n (P.η (Γ i).J) (P.Ω (Γ i).J))(hs':∀ i,∃ v:Clip,∀ n,Floor (B i) v n (P.η (Γ i).J) (P.Ω (Γ i).J))
    (hr:∀ i,(F i).metric.strip (P.α (Γ i).J) (P.Ω (Γ i).J))(hr':∀ i,(B i).metric.strip (P.α (Γ i).J) (P.Ω (Γ i).J))(hΩ:∀ i,0≤ P.Ω (Γ i).J)
    (hw:∀ i,0 < w i)(hh:∀ i,w i ≤ RG08.Supplies.Strip G P Q k (Γ i).J)(hd:∀ i,0≤δ i)
    (hX:∀ i,RowCost (Flat.curve Q (Γ i).J) 1 (Cell.changeK (B i) (F i)) (δ i)): FairT (Γ:=Γ) (D:=D) (K:=k) (G:=G) F B w δ:=by
 let X(i):=Tack.Head (Γ i) G; let N:= (Fintype.card (Loc G 1):ℝ)
 have Hq:D.Good (fun x=> (Fintype.card (X x):ℝ)):=D.hale p _ hV (fun _=>Nat.cast_nonneg _) fun i=>(hU i).head
 let π(i):=2*p i^2
 have hp:D.Good π:=D.moreover _ _ (D.steady _ zero_le_two) (stairs D hV _)
 have H i:= hh i
 unfold RG08.Supplies.Strip at hh
 have hs1 (i):_:= (plan_hr G k P (Γ i).J).2.1
 have hA(i):1 ≤ ((Γ i).L.val:ℝ) := Nat.one_le_cast.mpr (Γ i).L.property
 choose t ht using hs -- shadow hs
 choose m hm using hs'
 have hE(i):=ribbons (Q:=P) (A:=F i) (A':=B i) (ha i) (ha' i) (hs1 i) (ht i) (hm i) (hr i) (hr' i) (hX i) (hd i) (hw i) (show w i ≤ min _ _ from le_min ((hh i).trans (min_le_left ..)) (((hh i).trans (min_le_right ..)).trans (le_mul_of_one_le_left (Flat.curve_pos ..).le (hA i)))) (hU i).pos (hU i).plant (hU i).key (hU i).allowance (hΩ i)
 exact ⟨⟨⟨π,hp,fun i=> (hE i).2.2.2⟩, D.hear _ _ Hq (D.steady _ (Nat.cast_nonneg _))⟩,⟨⟨p,hV,fun i=>⟨(hE i).1,(hE i).2.1,(hE i).2.2.1⟩⟩, D.hear _ _ Hq Hq⟩⟩
end YM.RG08.Yamen
