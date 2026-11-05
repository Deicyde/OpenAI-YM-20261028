import YM.FullVolume.Sym.Stage
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
variable {v δ e b γ B η:ℝ} {n d:ℕ} {C:Tune H v δ}
/-! Support.Cap from linearity of sewn payments. Use precise unforced/issued logits after BaronM. Assumes phase tracks, may pick price late. -/
variable {w:Rung}
lemma mix_sum {E ι:Type*} [AddCommMonoid E] [Module ℝ E] (J:Finset ι) (f:sun→ι→E): mix w (fun i=>∑ j∈J,f i j)=∑ j∈J,mix w (fun i=> f i j):=by unfold mix; simp_rw [Finset.smul_sum]; rw [sum_comm]
lemma mix_sub {E:Type*}[AddCommGroup E][Module ℝ E](f g:sun→E): mix w (fun x=> f x - g x)=mix w f-mix w g:=by unfold mix; simp_rw [smul_sub,Finset.sum_sub_distrib]
lemma mix_scale {E:Type*} [AddCommMonoid E] [Module ℝ E] (c:ℝ) (f:sun→E): mix w (fun i=> c • f i)=c • mix w f:=by unfold mix; rw [smul_sum]; apply sum_congr rfl; exact fun j _=> smul_comm ..
lemma mix_times (c:ℝ) (f:sun→ℝ): mix w (fun i=> c * f i)=c * mix w f:= mix_scale c f
lemma mix_guard (P:BudgetPoint)(s:Support c)(f:sun→ Config G c→ℝ) (V):mix w (fun i=>masked P.threshold s (f i) V) = masked P.threshold s (mix w f) V:=by
  by_cases he:Healthy P.threshold s V
  · simp_rw [masked_eq _ _ _ _ he]; rw [mix_eval]
  simp_rw [masked_ne _ _ _ _ he]; simp [mix]

-- Ties lift; not on Δ. Cost employ arbitrary site constrained portfolio.
local notation "O" => Chi.canonical
local notation "M" => Beam.marquee H P
local notation "L" => Meadow.studio X.halo (radiusB p)
section senses
variable (h:sanction P (Beam.marquee H P).reg (fun i=> (plays C Chi.canonical γ i).logRead) (v/2) B) (x:Site c) (V:Config G c)
    (ht:P.B=radiusB p) (hs: Stripe w (v/2) η) (d:ℕ)
def flowerD (A:Tune H v δ) (d:ℕ) (γ:ℝ)(i:sun):= Meadow.barony (A.beams i (A.lay i.property)) Chi.canonical d γ
local notation "F"=> flowerD C d γ
include ht
lemma signed (i:sun):flowerD C d γ i x=∑ j∈Meadow.panel H d, Meadow.garnerAt H P x j • ((plays C O γ i).logRead j) := by
  -- P.B unused; .aster uses apparently omitted hB due def same? pass
  have hf:= C.seats i (C.lay i.property); exact Meadow.aster O P (recital C i) hf.3 (Match.same_area hf.3 hf.reg hf.forced) rfl γ d x
lemma prints : mix w (fun i=> flowerD C d γ i x)=∑ j∈Meadow.panel H d, Meadow.garnerAt H P x j • (mix w (fun i=> (plays C O γ i).logRead j)) := by
  simp_rw [signed _ ht]; exact (mix_sum _ _).trans (sum_congr rfl fun i hi=> mix_scale _ _)
lemma forecast : Trio.froth (mix w (flowerD C d γ)) = ∑ j∈Meadow.panel H d,mix w (fun i=> (plays C O γ i).logRead j):=by
  let f j:= mix w (fun i=> (plays C O γ i).logRead j)
  rw [show Trio.froth (mix w (flowerD C d γ))=∑ i: Site c,mix w (flowerD C d γ) i from funext fun x=> by rw [Finset.sum_apply] ]; simp_rw [mix_eval,prints _ ht]; rw [sum_comm]; exact sum_congr rfl (fun i _=>by rw [← sum_smul,Meadow.paysOne, one_smul])
include h hs
lemma sparkle : ‖mix w (fun i=> Trio.earned P (recital C i) γ d x V)‖ ≤ ballCost L * (η*B):=by
  obtain ⟨f,hf,hX⟩:= h w η hs; let P':=M
  let q i:= Meadow.garnerAt H P x i; let W : ℕ→ Config G c→ℝ:= mix w (fun i=> (plays C O γ i).logRead)
  have hx: mix w (fun i=> Trio.earned P (recital C i) γ d x V)=∑ j∈Meadow.panel H d,q j* masked P.threshold ((P').reg j).support (W j) V:=by
    unfold Trio.earned; rw [mix_sum]; refine sum_congr rfl (fun i _=>?_); rw [mix_times]; unfold W; rw [mix_eval (fun i=> (plays C O γ i).logRead)]; exact congr_arg (q i * ·) (mix_guard _ ((P').reg i).support (fun j=>(plays C O γ j).logRead i) _)
  rw [hx]; apply le_trans (norm_sum_le ..)
  let s:= neighbors L x; let E i z:= if ((P').reg i).site=z then f i*Real.exp (preExponent P * coverNumber P.B ((P').reg i).support) else 0
  calc _ ≤ ∑ i∈Meadow.panel H d, ∑ z∈ s,E i z:= by
            apply sum_le_sum; intro i hi; have hk : 0≤ ∑ z∈ s, E i z:= sum_nonneg fun z _=> (hf z).1 i
            change ‖q i*_‖≤_; by_cases he : q i=0; · rw [he,zero_mul,norm_zero]; exact hk
            have hx:= Meadow.assigned H P x i hi ht he
            rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg _) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (hX i|>.2) V).trans; unfold E; rw [sum_ite_eq,if_pos (hx.2 (P'.reg i).anchor)]
            exact le_mul_of_one_le_right (hX i|>.2.1) (Real.one_le_exp (mul_nonneg (headline P).exponent_pos.le (Nat.cast_nonneg _)))
       _ ≤ _ := by rw [sum_comm]; refine le_trans (sum_le_sum (fun i _=> budget_sum (hf i) (Meadow.panel H d))) ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (budget_nonneg (hf x))
lemma frozen_layer (hV:flags P.threshold V=∅): ‖mix w F x V‖ ≤ (ballCost L:ℝ)*(η*B):=by
  rw [mix_eval,mix_eval]; have he :∀ i, flowerD C d γ i x V=Trio.earned P (recital C i) γ d x V:=by
    intro i; rw [signed x ht,Finset.sum_apply]; unfold Trio.earned; refine sum_congr rfl (fun j hj=>Eq.symm ?_)
    exact congr_arg (Meadow.garnerAt H P x j * ·) (masked_eq _ _ _ V (by unfold Healthy; rw [hV]; simp))
  simp_rw [he]; exact sparkle h x V ht hs d
set_option maxHeartbeats 800000 in
lemma flowF (hV:flags P.threshold V=∅)(l:List (Directions G c))(hl:l.length ≤ P.order)(hx:∀ i∈l,‖i‖≤P.threshold) : ‖leftDerivs (Boulevard.stillA (Trio.froth (mix w F))) l V‖ ≤ 2 *((Fintype.card (Site c):ℝ)* (η*B)):=by
  let f:= (Trio.froth (mix w F)); let A:= (Fintype.card (Site c):ℝ)*(η*B); obtain ⟨k,hk,hL⟩:= h w η hs
  let a (i):= (mix w (fun i=> (plays C O γ i).logRead)) i
  have hA := Boulevard.planetary hk (fun i=> (hL i).2.1)
  have ht : f = ∑ i∈ Meadow.panel H d, a i:= by unfold f; rw [forecast ht]; exact sum_congr rfl fun i _=> (mix_eval (fun t=> (plays C O γ t).logRead) i).symm
  have hh U (hu:flags P.threshold U=∅) i:Push.Local.Chart P.order (a i) U:= (hL i).1.smooth U (by unfold Healthy; rw [hu]; simp)
  have hf:P.Regular univ f:= by rw [ht]; exact Meadow.regularA _ (fun i _=>CouplingShape.reg_extend (hL i|>.1) (Finset.subset_univ _))
  let g (_:Config G c):= f 1
  have hh' (V:Config G c)(hV:flags P.threshold V=∅) (l:List (Directions G c))(hl:l.length ≤ P.order)(he:∀ i∈l,‖i‖≤P.threshold): ‖leftDerivs f l V‖ ≤ A:=by
    rw [ht,Push.Local.left_sum (Meadow.panel H d) a V l (fun i _=> hh V hV i) hl]; exact (norm_sum_le ..).trans ((sum_le_sum fun i _=> (hL i).2.2 V (by unfold Healthy; rw [hV]; simp) l hl (fun i hi=> Boulevard.tiny (he i hi) _)).trans (budget_sum hA _))
  change ‖leftDerivs (f-g) l V‖ ≤ 2*A; rw [VerifiedReset.left_sub (hf.smooth V (by unfold Healthy; rw [hV]; simp)) (show Push.Local.Chart P.order g V from contDiffAt_const) hl]
  apply (norm_sub_le ..).trans; rw [two_mul]; refine add_le_add (hh' V hV _ hl hx) ?_
  have hx : flags P.threshold (1:Config G c)=∅:= Boulevard.smoky (P:=P) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos)
  have hG : ‖leftDerivs g l V‖ ≤ ‖f 1‖ := by cases l; exact le_rfl; simp [g,Work.G07.left_const]
  exact hG.trans (hh' 1 hx [] (Nat.zero_le _) (by simp))
lemma polling (x:Site c):P.Regular univ (mix w F x):=by
  rw [mix_eval, prints x ht]; obtain ⟨k,hk,hL⟩:= h w η hs; exact Meadow.regularA _ (fun i _=> CouplingShape.reg_scale _ ((mix_eval (fun t=> (plays C O γ t).logRead) i (w:=w)) ▸ CouplingShape.reg_extend (hL i|>.1) (Finset.subset_univ _))) -- edit
end senses
section berth
variable {Y:Stars→Side} {r:ℕ} (H₀:∀ i:Stars,(Y i).val=2*(r+i.val)) {z k:ℕ} {K: Stars→ℝ} {χ:Chi} (v x:ℝ)
    (V:sun→∀ i:Stars,Trio.Offer G (Y i))
def mulch (B:BudgetPoint) (s:ℝ)(V:sun→Trio.Offer G c) (t q:ℝ):=∀ w a,Stripe w s a→
   (∀ i,B.Regular univ (mix w V i)) ∧ (∀ U:Config G c,flags B.threshold U=∅→∀ l:List (Directions G c),l.length ≤ B.order→ (∀ i∈l, ‖i‖ ≤ B.threshold)→ ‖leftDerivs (Boulevard.stillA (Trio.froth (mix w V))) l U‖ ≤ a*t) ∧ ∀ U:Config G c,flags B.threshold U=∅→∀ i,‖mix w V i U‖ ≤ a*q
abbrev rag (V:sun→∀ i:Stars,Trio.Offer G (Y i)) (w:Rung):= fun i:Stars=> mix w (fun t=>V t i)
variable {v} {P:BudgetPoint}
lemma unspool (u: Site c) (x:Config G c): mix w (fun i=> Trio.unearned P H₀ z (Trio.rip (V i)) u x)=Trio.unearned P H₀ z (Trio.rip (rag V w)) u x:=by
  unfold Trio.unearned; rw [mix_sum]; refine sum_congr rfl (fun i _=> ?_); rw [mix_times]; congr 1; rw [mix_sum]; refine sum_congr rfl (fun j _=> ?_)
  dsimp only; let y:= Trio.emerge H₀ i j u; rw [mix_guard]; apply congr_arg (fun f=>masked P.threshold (neighbors z y) f x); ext r
  unfold Trio.unit Trio.rip rag; rw [mix_eval]; dsimp only [Boulevard.stillA]; simp_rw [mix_sub,mix_eval] -- ambiguous
lemma ornamentP (u:Site c) : mix w (fun i=> Trio.ornament H₀ (V i) u)= Trio.ornament H₀ (rag V w) u:=by
  ext x; rw [mix_eval]; unfold Trio.ornament Trio.beacon; rw [mix_sum]; refine sum_congr rfl (fun i _=>?_); rw [mix_times]; congr 1; rw [mix_sum]; refine sum_congr rfl (fun j _=>?_); unfold Trio.unit Trio.rip rag; dsimp only [Boulevard.stillA]; simp_rw [mix_sub,mix_eval]
variable {b:ℝ} {t q:Stars→ℝ} (he:z≥r+4) (hs: ∀ i:Stars,mulch P v (fun s=>V s i) (t i) (q i)) (h:Stripe w v b)
include H₀ h he hs
lemma wired (o:Site c): P.Regular (neighbors z o) (mix w (fun i=> Trio.ornament H₀ (V i) o))∧ P.supBounds o (neighbors z o) (mix w (fun i=> Trio.ornament H₀ (V i) o)) (b*Trio.oroW P z t):= by
  rw [ornamentP]; simp_rw [Trio.orchard]; let P' i := Boulevard.stillA (Trio.froth (rag V w i)); let F(i:Stars):= P' i ∘ Slide.shape (Trio.pad H₀ i) o
  have hv i (j:Site (Y i)): separation o (Slide.sites (Trio.pad H₀ i) o j)≤ z:= (Slide.village (C:=Y i) (w:=r+i.val) (H₀ i).ge _ _).trans (by have hx:=i.isLt; omega)
  have hr i:P.Regular univ (P' i):=by
    have hp: P.Regular univ (Trio.froth (rag V w i)):= by rw [show Trio.froth (rag V w i)=∑ j,rag V w i j from funext fun _=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ (fun j _=> (hs i w b h).1 j)
    exact CouplingShape.reg_sub hp (CouplingShape.reg_const _)
  have ht i:= Slide.regular (Trio.pad H₀ i) o (hr i) (fun j=>(neighbors_mem ..).2 (hv i j))
  let d i:= b*(Trio.tilt P z*t i)
  have hp i : P.supBounds o (neighbors z o) (F i) (d i):=by
    have hH:= hs i w b h; refine ⟨?_,fun V hh l hl hd=>?_⟩
    · have hh:= hH.2.1 (1:Config G (Y i)) (Boulevard.smoky (P:=P) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos)) [] (Nat.zero_le _) (by simp)
      have he:0≤ b*t i:= (norm_nonneg _).trans hh
      rw [show d i=(Trio.tilt P z)*(b*t i) from (by unfold d; ring)]; exact mul_nonneg (by unfold Trio.tilt; positivity) he
    let f:= Trio.pad H₀ i
    have hV:= Slide.allFlag f o V _ (fun j=>(neighbors_mem ..).2 (hv i j)) _ P.threshold_pos.le hh
    exact (Slide.stalled f o (P' i) (hv i) l V hl hd ((hr i).smooth _ (by unfold Healthy; rw [hV]; simp)) (hH.2.1 _ hV)).trans_eq (by unfold d Trio.tilt; ring)
  refine ⟨Meadow.regularA _ (fun i _=> CouplingShape.reg_scale _ (ht i)),?_⟩
  have hZ : P.supBounds o (neighbors z o) (∑ i:Stars, Slide.ray i • F i) (∑ i:Stars, |Slide.ray i| *(d i)):= Trio.sup_S P (fun i=> Slide.ray i • F i) _ _ _ _ (fun i _=>CouplingShape.reg_scale _ (ht i)) (fun i _=>CouplingShape.sup_scale _ (hp i))
  rw [show b*Trio.oroW P z t=∑ i:Stars, |Slide.ray i| *(d i) from (by unfold Trio.oroW; rw [mul_sum]; exact sum_congr rfl (fun i _=> by unfold d; ring))]; exact hZ
omit h hs
local notation "M" => Beam.marquee H P
-- Scout() shrinks radius just once. δ belongs C.
variable (d:ℕ) (W:ℝ) {v':ℝ}{C': Tune H v' δ}
    (hr: ∀ i:Stars,mulch P (v'/2) (fun s=> V s i) (t i) (q i)) (hk: P.B=radiusB p) (hy:sanction P (Beam.marquee H P).reg (fun i=> (plays C' O γ i).logRead) (v'/2) B)
def lightTax (Y: Stars→Side)(f:Stars→ℝ) := ∑ i:Stars, |ray i| * ((Fintype.card (Site (Y i)):ℝ)*(f i+f i))
include hr hk hy
lemma lightP (hv: 4≤v') (x : Site c) (U:Config G c) : Scout (v'/4) (phraseS (fun i=>Trio.insight P (recital C' i) γ d H₀ z (V i) x U)) (2*(2*((ballCost (Meadow.studio X.halo (radiusB p)):ℝ)*B)+lightTax Y q)):= by
  let f:= phraseS fun i=> Trio.insight P (recital C' i) γ d H₀ z (V i) x U; let Lj:= Meadow.studio X.halo (radiusB p); let D:ℝ:=2*((ballCost Lj:ℝ)*B)+lightTax Y q
  have hx w b (hp:Stripe w (v'/2) b): ‖FullVolume.Ray.trace w f‖ ≤ b*D:= by
    unfold f; rw [mix_made]; unfold Trio.insight
    rw [mix_sub,mix_sub,unspool]; apply (norm_sub_le ..).trans
    have hh' := Trio.stipends P U H₀ z (rag V w) (fun i=> b*q i) (fun i V hv x=> (hr i w b hp).2.2 _ hv x) he x
    have he : ‖mix w (fun i=> flowerD C' d γ i x 1)‖ ≤ (ballCost Lj:ℝ)*(b*B) := by rw [← mix_eval, ← mix_eval]; exact frozen_layer hy x (1:Config G c) hk hp d (Boulevard.smoky (P:=P) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos)) -- expects x mismatch no
    refine (add_le_add ((norm_sub_le ..).trans (add_le_add (sparkle hy x U hk hp d) he)) hh').trans_eq ?_; unfold D lightTax; rw [mul_add b, mul_sum]; congr 1
    · unfold Lj; ring
    exact sum_congr rfl (fun i _=>by ring)
  have hu : Stripe 0 (v'/2) 1:= fun _=>by simp [FullVolume.Ray.trace]
  have ht:Rebar (v'/2) f D:= ⟨by linarith,le_trans (norm_nonneg _) ((hx 0 1 hu).trans_eq (one_mul D)) ,hx⟩
  have he:= Rebar.recovery ht (a:=v'/4) (by linarith) (by linarith); have hE : v'/4 / (v'/2)= 1/2:=by field_simp; ring_nf
  rw [hE,show ((1:ℝ)-1/2)⁻¹=2 from (by norm_num)] at he; exact he
end berth
end YM.PhysicalNext.Repeat.Jams
