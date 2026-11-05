import YM.UVExtension.Willow.Hast
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
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
open PhysicalNext.Repeat
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S) (M:Lotus.Leaf R) (hl:Lines R V b (betaF G x L) M) -- using PhysicalNext.Repeat to open
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => grains X R W o.a Q.table Q.halo V M p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
open Daisy Daisy.Charity March Ursell Trees Greenbelt Concert Refrain
variable {q' : Q.rate≤γ} {h':γ<0} {l t r d:ℝ}
variable (Y:Pavilion H V B γ v l q' h') (hY : Pouch G L x l)(hR:0 ≤ Q.exp-l)
local notation "ι'"=> radiusB x
local notation "Yt"=> ((stalk Q q' h').costs L μ)
local notation "m'"=> M.turn.badge S
variable (k:ℕ)
-- all addresses agree across origin H.Frame. cols.
variable (χ:Chi) (J : (d:Canvas (betaF G x L) b ι)→ Cash W x μ L Q o a T (freshen d R V)) (U:Config G c)
local notation "Tπ"=> aperture K
local notation "tD"=> Canvas (betaF G x L) b ι
open Match Multiple Letter OmitClusters Ovens Progress.DirectedRecipe
-- array rack from book.M without moving atoms
variable (z:Vines ι)(hz:z∈parade (betaF G x L) B)
noncomputable def pear (f g:H.Chapter → ℂ)(p:H.Chainbook):=∑ i:p.fst,∏ b:p.fst,if b=i then f b.val^(p.2 b)*g b.val/(p.2 b).factorial else f b.val^(p.2 b+1)/(p.2 b+1).factorial
noncomputable def echoS (z:Vines ι)(p:H.Chainbook):=if H.Fresh p ∧ Ac.Spark H.bookFoot p.1 ∧ H.statesPool U p then pear (juiceK U χ H V z) (ethers (V:=V) M χ U z) p else 0
include K
lemma wakeP (d:tD) (p:H.Chainbook): echoS (V:=V) M χ U ((Tπ).call d) p= ↑(cope M hl χ J U p d):=by
   unfold echoS cope; split; swap; · exact Complex.ofReal_zero.symm
   unfold Copse.dusk Copse.duskVal pear; push_cast; simp_rw [fun i=>(vox K M hl χ J U d i).1, fun i=> (vox K M hl χ J U d i).2]; apply sum_congr rfl; intro i _; refine Finset.prod_congr rfl fun j _=> ?_ ; split_ifs <;> push_cast <;> rfl
include hY Y hl hR
lemma radiance (p:H.Chainbook):Bumps (Tπ).span (fun z=> echoS (V:=V) M χ U z p):=by
   have ht (i:H.Chapter): Bumps (Tπ).span (fun z=> ethers (V:=V) M χ U z i):=by
       rcases i with i|i; · exact falls K M hl Y hY hR χ U _
       exact fun s f hs hv hf=> (pipes K M hl Y hY hR χ U i s f hs hv hf).neg
   intro s f hs hv hf; unfold echoS; split; swap; · exact differentiableOn_const _
   refine DifferentiableOn.fun_sum (fun i (_:i∈Finset.univ)=> DifferentiableOn.fun_finsetProd (fun j (_:j∈Finset.univ)=>?_)); split; next=> exact (((drinkH K Y hR U χ _ s f hs hv hf).pow _).mul (ht _ s f hs hv hf)).div_const _
   exact ((drinkH K Y hR U χ _ s f hs hv hf).pow _).div_const _
omit hY Y hl K hR
variable {z}
lemma mopey {f g: H.Chapter→ℂ}{u v:H.Chapter→ℝ}(hu:∀ i, ‖f i‖ ≤ u i)(hv:∀ i, ‖g i‖≤ v i)(p:H.Chainbook): ‖pear f g p‖≤ Copse.dusk u v p:=by
    apply (norm_sum_le ..).trans; refine sum_le_sum (fun i _=>?_); unfold Copse.duskVal; rw [norm_prod]; refine prod_le_prod (fun i _=>norm_nonneg _) (fun j _=>?_); split_ifs
    all_goals first
    | rw [norm_div,norm_mul,norm_pow,Complex.norm_natCast]; exact div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hu _) _) (hv _) (norm_nonneg _) (pow_nonneg ((norm_nonneg _).trans (hu _)) _)) (by positivity)
    | rw [norm_div,norm_pow,Complex.norm_natCast]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hu _) _) (by positivity)
variable {α e₀ e₁ : ℝ} (hA:0≤α)(he:0<e₀)(hh:0<e₁) (hp:α+e₀+e₁≤Q.exp-l)
    (hs: degreePrice (radiusB x) ((stalk Q q' h').overture L μ x 0) e₀ ≤ 1/2) (hv : degreePrice (radiusB x) ((stalk Q q' h').mergeScale L μ x 0) e₁≤1/2) (hq: (stalk Q q' h').mergeScale L μ x 0 ≤ 1/2)
local notation "Jp"=> (stalk Q q' h')
include hz Y hY hp hs hq hv K hl hA hh he
-- Marked letters.Reps, full root. no K seed discount.Crude
lemma chroma :
    let X:= (Copse.nose (G:=G) H.library k (radiusB x) α)
    X.MeasureP (fun p U=> echoS (V:=V) M χ U z p) ((1-1/2)⁻¹*(ceiling (H:=H) k M+ceiling (H:=H) k M*(1-1/2)⁻¹)):=by
   intro X; apply (Copse.rests k _).2
   obtain ⟨f,g,h,hg,hy,hkF,hf⟩:= grip K Y χ z hz (show α+e₁+e₀ ≤ Q.exp-l by linarith)
   let t:=(stalk Q q' h').mark L μ x; let m:= (stalk Q q' h').mergeScale L μ x 0; let c₀:= (stalk Q q' h').overture L μ x 0; let d':= (stalk Q q' h').quantum L μ x 0 0 1 0; let B:= radiusB x
   have hm : 0≤t:= H.laws.acquired.marked
   have hi : 0<c₀:= (stalk Q q' h').overture_pos x 0 (Festa.altitude (H:=H))
   have ht': d'=c₀ * Real.exp (-t):= by unfold d' c₀ t; rw [(stalk Q q' h').quantum_form (r:=1)]; push_cast; rw [mul_one]; rfl
   have hZ : d' ≤ c₀:=ht'.trans_le (mul_le_of_le_one_right hi.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hm)))
   have hα: 0≤ α+e₁:=by linarith only [hA,hh]
   have hfA: Ready H.smallAt B f (α+e₁) c₀ e₀ (1/2):= ⟨hi,he,hs,by norm_num,hy,h⟩
   have hg': Ac.Hit H.largeAt B g (α+e₁) c₀:=by
      intro x; apply budget_loosen _ hZ; refine budget_mono (hg x) (fun i=> ?_) (fun i=>?_)
      · split; next=> exact mul_nonneg (hkF _) (Real.exp_pos _).le
        exact le_rfl
      split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right he.le) (Nat.cast_nonneg _))) (hkF i)
      exact le_rfl
   have hp' : Ac.Hit (fun i:H.fragrances=> H.bookFoot (.inr i)) B (fun i=> clusters H.seam f i.2) (α+e₁) (c₀*(1-1/2)⁻¹):=by
      intro x; simpa! only [currency,Nat.zero_le,true_and,pow_zero,mul_one] using! log_hit_tail _ _ _ H.testS hfA hα 0 x
   let W:= OmitClusters.grade H.seam f g; let w i:= W i*(1-1/2)⁻¹
   have hw(i): 0≤ W i:=by rcases i with i|i; exact hkF i; exact clusters_nonneg _ hy _
   have hU (x:Config G c)(i): ‖Concert.juiceK x χ H V z i‖≤ W i:=by
      rcases i with i|i; · exact (hf x).2 _
      change ‖-((coefficient H.seam i.2:ℂ)*_ / ((i.1+1).factorial:ℂ))‖ ≤ clusters H.seam f i.2; rw [norm_neg,norm_div,norm_mul,norm_prod,Complex.norm_real,Complex.norm_natCast,Real.norm_eq_abs]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun n _=> (hf x).1 (i.2 n))) (abs_nonneg _)) (by positivity)
   have hv': Ready H.bookFoot B w α m e₁ (1/2) :=by
      refine ⟨mul_pos (show (0:ℝ)<20 by norm_num) hi,hh,hv,by norm_num,fun i=>mul_nonneg (hw i) (by norm_num),fun x=>?_⟩
      have h₃: Ac.Hit H.bookFoot B W (α+e₁) (c₀+c₀*(1-1/2)⁻¹):= fun x=> Extra.Iteration.Cost.sum (hg' x) (hp' x)
      refine budget_loosen (budget_mono (budget_scale (show 0 ≤ (1-1/2:ℝ)⁻¹ by norm_num) (h₃ x)) (fun i=> ?_) (fun i=>?_)) ?_
      · split; next=> exact mul_nonneg (mul_nonneg (hw i) (by norm_num)) (Real.exp_pos _).le
        exact le_rfl
      · split; next h=> unfold w; apply le_of_eq; ring
        simp
      change _≤20*c₀; norm_num; linarith only [hi]
   obtain ⟨u,hu,hU'⟩:= stay K M hl Y hY k χ z hz
   obtain ⟨v₁,hv₁,hV₁⟩:= (Copse.rests k B).1 (blush K M hl Y hY k χ hα he (by linarith) hs z hz)
   let f':= Sum.elim (fun r:H.ThickP=> u r.val) v₁; have hF' (x:Config G c)(i): ‖ethers M χ x z (V:=V) i‖≤ f' i:=by
      rcases i with i|i; exact hU' _ _; exact (norm_neg _).trans_le (hV₁ _ _)
   have hM:= rentsTre _ _ hv'; have hπ:SumBudget (fun i=> f' i*Copse.worth k B (α+e₁) (H.bookFoot i)) (ceiling (H:=H) k M+ceiling (H:=H) k M*(1-1/2)⁻¹):=by
       apply Extra.Iteration.Cost.sum _ hv₁; refine budget_mono (budget_pull (fun i:H.ThickP=> Subtype.val i) Subtype.val_injective hu) ?_ ?_
       · exact fun i=>mul_nonneg ((norm_nonneg _).trans (hF' 1 (.inl i))) (Real.exp_pos _).le
       exact fun i=>mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (show α+e₁ ≤ Q.exp-l from by linarith only [hp,he]) (Nat.cast_nonneg _))) ((norm_nonneg _).trans (hF' 1 (.inl i)))
   have hy'(i):0≤ f' i:=(norm_nonneg _).trans (hF' 1 i)
   refine ⟨_,Copse.blinks H.bookFoot B k hw hy' (by norm_num : (0:ℝ)≤1/2) (by norm_num : 1/2<(1:ℝ)) ?_ hv'.2.2.2.2.2 hA hM hv'.1.le hπ,?_⟩
   · intro i; have hi:(H.bookFoot i).Nonempty:=by
        rcases i with i|i; · exact i.2.1
        obtain ⟨x,hx⟩:= (i.2 none).2.1; exact ⟨x,mem_biUnion.mpr ⟨none,mem_univ _,hx⟩⟩
     obtain ⟨x,hx⟩:=hi; have h:= budget_single (test_hit _ _ hv' x) i; rw [Trees.hit,if_pos hx] at h; refine le_trans ?_ (h.trans hq); exact (le_mul_of_one_le_right (hw i) (by norm_num : 1 ≤ (1-1/2:ℝ)⁻¹)).trans (le_mul_of_one_le_right (hv'.2.2.2.2.1 i) (Real.one_le_exp (mul_nonneg hα (Nat.cast_nonneg _))))
   intro i U; unfold echoS; split; next h=> rw [Copse.syrup, if_pos h.2.1]; exact mopey (H:=H) (hU U) (hF' U) _
   next h=>
     rw [norm_zero,Copse.syrup]; split; next ht=> exact sum_nonneg fun i _=> Copse.signed hw hy' ..
     exact le_rfl
end YM.UVExtension.Willow
