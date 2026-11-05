import YM.FullVolume.Sector.Ruins
import YM.FullVolume.C.Ribbon
/-!
# Combination budgeting for the Archive
 Actual real labels. Respect sun tests or affine changes supplied by Tune.
 Doesn't lift V into any complex group. Pivotal for analytic of Hessian/reset.
 -/
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
-- REBAR on portfolios, ℝ germs
noncomputable abbrev tip : sun:= ⟨0,by unfold sun; simp⟩
def pinch (i:ℝ):sun:=if h:i∈ sun then ⟨i,h⟩ else tip
lemma pinch_eq (s:sun):pinch s=s:= by simp [pinch,s.property]
def phraseS {X:Type*} (f:sun→X):ℝ→X:=fun x=>f (pinch x)
lemma phrased {X:Type*} (f:sun→X) (s:sun):phraseS f s=f s:= congr_arg _ (pinch_eq s)
variable {w:Rung}
def Stripe (w:Rung)(v b:ℝ):= ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ b
def mix {E:Type*} [AddCommMonoid E] [Module ℝ E] (w:Rung)(f:sun→E) := ∑ i∈w.support,w i • f i
lemma mix_id {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f:ℝ→E}:mix w (fun x=>f x)=FullVolume.Ray.trace w f:=rfl -- annotate
lemma mix_made {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:sun→E): FullVolume.Ray.trace w (phraseS f)=mix w f:=by unfold FullVolume.Ray.trace; simp_rw [phrased]; rfl
lemma mix_eval {X:Type*} {E:Type*} [AddCommMonoid E] [Module ℝ E] (g:sun→X→E) (x:X) : mix w g x=mix w (fun i=>g i x):= by unfold mix; rw [Finset.sum_apply]; rfl
lemma mix_d {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:sun→E) (h:Stripe w v b) (hs:Scout v (phraseS f) B): ‖mix w f‖ ≤ b*B:= by rw [← mix_made f]; exact hs.beam w b h
-- sun projection uses sum signs, later transporting Ham
lemma stripe_pos (h:Stripe w v b):0≤b:= (norm_nonneg _).trans (h 0)
def sanction {ι:Type} (P:BudgetPoint) (X:ι→RegularAddress c) (f:sun→ι→ Config G c→ℝ) (v b:ℝ):=∀ w η,Stripe w v η→ Meadow.Budget P X (mix w f) (η*b)
def league {ι:Type} (A:ι→Support c) (s:ℕ) (V:sun→ι→ Config G c→ℝ) (e v b:ℝ):=∃ f:ι→ℝ, Ac.Hit A s f e b ∧ ∀ i U, Scout v (phraseS fun t=> V t i U) (f i)
lemma reg_mix {s:Support c} (f:sun→ Config G c→ℝ) (h:∀ i,P.Regular s (f i)):P.Regular s (mix w f):=by
  suffices hb:∀ t:Finset sun,P.Regular s (∑ i ∈t,w i • f i) from hb _
  intro t; induction t using Finset.induction_on with
  | empty => simp only [sum_empty]; exact VerifiedReset.reg_const _
  | insert i s hi hv =>
    rw [sum_insert hi]
    rw [show w i • f i+_=w i • f i- (-1:ℝ) • (∑ j∈s,w j • f j) from (by simp)]
    exact VerifiedReset.reg_sub (CouplingShape.reg_scale _ (h _)) (CouplingShape.reg_scale _ hv)
lemma sanctioned_mono {ι:Type} {X:ι→RegularAddress c} {f:sun→ι→ Config G c→ℝ} (h:sanction P X f v b) (hp:b≤B):sanction P X f v B:=by
  intro w u hu; obtain ⟨k,hk,hX⟩:= h w u hu; exact ⟨k,fun i=> budget_loosen (hk i) (mul_le_mul_of_nonneg_left hp (stripe_pos hu)),hX⟩

-- same actual primitive J.Storm but independent of choosing a house with analytic dependence
variable (C:Tune H v δ)
abbrev recital (i:sun) := Match.staple (H:=H) (J:=C.beams i (C.lay i.property)) (C.seats _ (C.lay i.property)).3 (C.seats _ (C.lay i.property)).reg (C.seats _ (C.lay i.property)).forced
def plays (χ:Chi)(γ:ℝ)(i:sun):= Song.plusone H (recital C i) χ γ
def rates (χ:Chi)(γ:ℝ)(d:ℕ)(i:sun):= Meadow.timbres (recital C i) (χ:=χ) γ d
-- measures not changed off line, any.
section currents
variable {W₀ : ℝ}
variable {C} (h:Candy C χ (preExponent P) B P) (hB:P.B=radiusB p)
lemma thes (i:Songbook c)(s:ℝ) : sounding T.down T.low (R.beta*s) γ i=(Sum.elim (fun _=> (1:ℝ)) (Sum.elim (fun _=>s) (Sum.elim (fun _=>s) (fun _=>1))) i) • sounding T.down T.low R.beta γ i:= by
  ext x; unfold sounding; rcases i with i|i|i|i <;> dsimp only [tuneAtom,tuneLow,Pi.smul_apply, smul_eq_mul, Sum.elim] <;> ring
variable {σ τ ℓ :ℝ} (hv : T.down.Bounds T.low σ τ ℓ) (he:WilsonStartup.Decent T.low P) (hp: preExponent P/P.B ≤ σ/2) (hr : ∀ i z,P.Regular (Song.locate H z).support (Song.sequence H (recital C i) χ z))
include h hp hv he
local notation "Z"=> octaveNeed G P T.low σ τ ℓ R.beta γ
lemma soars (w:Rung) (hs:Stripe w (v/2) η) : Meadow.Budget P (strings T.down P (n:=c)) (mix w fun i:sun=>sounding T.down T.low (C.notes i).beta γ) ((η*4)*Z):=by
  obtain ⟨f,hf,hX⟩:= stanzaReady (n:=c) T.down T.low P R.beta γ hv he hp
  -- project factor via beta-Fold
  have hy:1≤v/2:=by linarith [h.high]
  have hd:= C.pole.active
  refine ⟨fun i:Songbook c=>η*4*f i,fun i=>?_,fun i=>?_⟩
  · convert (Cost.scale (hf i) (η*4) (mul_nonneg (stripe_pos hs) (by norm_num))) using 2 with i
    split <;> ring
  let F(x:ℝ):ℝ:= Sum.elim (fun _=>1) (Sum.elim (fun _=>C.pole.flow x^2) (Sum.elim (fun _=> C.pole.flow x^2) (fun _=>1))) i
  let f':= fun (i:Songbook c)=>sounding T.down T.low R.beta γ i
  have hY:mix w (fun t:sun=> sounding T.down T.low (C.notes t).beta γ) i=(mix w fun t:sun=>F t) • f' i:=by
    rw [mix_eval]; unfold mix; rw [Finset.sum_smul]; refine sum_congr rfl (fun j hj=>?_)
    dsimp only; rw [C.plot_rel _ (C.lay j.property),thes]; rw [smul_smul]; rfl -- infer thes
  rw [hY]
  have ht: Scout (v/2) F 4:= by
    have hf: Scout (v/2) (fun t=>C.pole.flow t^2) 4:= ((C.pole.pulse.power 2).lessen hy (by linarith)).enlarged (by have hh:= C.pole.full; nlinarith only [hh.2.2,hd, mul_nonneg (show 0≤1-δ by linarith) (show 0≤3+δ by linarith [hh.2.2])])
    have hp: Scout (v/2) (fun _=> (1:ℝ)) 4:= (Scout.still hy (1:ℝ)).enlarged (by norm_num)
    unfold F; rcases i with i|i|i|i
    · exact hp
    · exact hf
    · exact hf
    exact hp
  exact ⟨CouplingShape.reg_scale _ (hX i|>.1), sup_le (CouplingShape.sup_scale _ (hX i|>.2)) (mul_le_mul_of_nonneg_right (ht.beam _ _ hs) (hX i|>.2.1))⟩
include hr hB
lemma rising (V:H.fragrances→RegularAddress c) (hV : ∀ i,(V i).support=Captain.reachability i) (w:Rung)(hs:Stripe w (v/2) η): Meadow.Budget P (Sum.elim V (strings T.down P)) (mix w (fun i=> opus H (recital C i) χ γ)) (η*(B+4*Z)):=by
  obtain ⟨f,hf,hX⟩:= soars h hv he hp w hs (γ:=γ)
  obtain ⟨k,hK,hL⟩:= h.phases
  rw [mul_add, ← mul_assoc]; refine ⟨Sum.elim (fun i=>k i*η) f,fun i=> Cost.sum ?_ (hf i),fun i=>?_⟩
  · have hz:= Cost.scale (hK i) η (stripe_pos hs)
    apply budget_mono hz
    · intro j; split
      · exact mul_nonneg (hL _ _ (hV j ▸ (V j).anchor) w η hs|>.1) (Real.exp_nonneg _)
      rfl
    intro j; dsimp only [Sum.elim]; split
    next hZ => rw [if_pos (show i∈Captain.reachability j from hZ ▸ (show (V j).site ∈ Captain.reachability j from hV j ▸ (V j|>.anchor))),hB,hV]; exact le_of_eq (by ring) -- supports def
    exact hz.1 j
  rcases i with i|i
  · rw [mix_eval]; let g t:=Song.sequence H (recital C t) χ i
    let F V:= FullVolume.Ray.trace w (fun x=> Lyre.stamina (χ:=χ) (U:=C) i x V)
    have hz: mix w g=(-1:ℝ) • F:=by
      ext x; rw [mix_eval]; change _= (-1:ℝ)* _; unfold mix F FullVolume.Ray.trace; rw [mul_sum]; refine sum_congr rfl (fun i' hi=> ?_)
      dsimp only; rw [Lyre.octopus (χ:=χ) (U:=C) i x _ (recital C i') rfl]
      let r:= March.stream (C.beams i' (C.lay i'.property)) χ x ((recital C i').furrow i)
      change w i'*((-1:ℝ)*r)=(-1:ℝ)*(w i'*r); ring
    change P.Regular (V i).support _ ∧ P.supBounds (V i).site (V i).support _ _; rw [hV]
    refine ⟨reg_mix g fun i=> hr i _, ?_⟩
    change P.supBounds _ _ (mix w g) _; rw [hz]; have hP:= CouplingShape.sup_scale (-1) (hL i _ (show _∈ Captain.reachability i from hV i ▸ (V i).anchor) w η hs)
    rw [abs_neg,abs_one,one_mul] at hP; exact hP
  have hz:= hX i; rw [mix_eval] at hz; rw [mix_eval]; exact hz
lemma trunk (V:H.fragrances→RegularAddress c) (hV : ∀ i,(V i).support=Captain.reachability i) : sanction P (Yearling.booth H P V).reg (fun i=> (plays C χ γ i).logRead) (v/2) (turnFee P*(B+4*Z)) := by
  intro w η hs; obtain ⟨f,hf,hX⟩:= rising h hB hv he hp hr V hV w hs (γ:=γ)
  obtain ⟨hi,hH⟩:= spiral _ _ f (fun i=> (hX i).1) (fun i=>(hX i).2) hf
  rw [show η*(turnFee P*(B+4*Z))=turnFee P*(η*(B+4* Z)) from (by ring)]
  refine ⟨(fun i:Seat c × Magazine H=> Song.Rim c*(turnFee P*f i.2)) ∘ pennant H,fun i=> Cost.equiv (pennant H) (hH i),fun i=>?_⟩
  let F(s):= opus H (recital C s) χ γ
  have ht: mix w (fun i=> (plays C χ γ i).logRead) i=(choir (mix w F)) (pennant H i):=by
    ext x; rw [mix_eval,mix_eval]; change _=Song.Rim c*(mix w F _ _); rw [mix_eval,mix_eval]; unfold mix; rw [mul_sum]; refine sum_congr rfl (fun j hj=>?_);
    let y := pennant H i; let x₀ := F j y.2 (y.1.view x)
    change w j* (Song.Rim c*x₀)=Song.Rim c*(w j*x₀); ring
  rw [ht]; exact hi (pennant H i)
lemma foreship : sanction P (Beam.marquee H P).reg (fun i=> (rates C χ γ d i).logRead) (v/2) (turnFee P*(B+4*Z)) :=by
  intro w η hw
  obtain ⟨k,hk,hL⟩:= trunk h hB hv he hp hr (Beam.dashboard H) (Beam.see H) (γ:=γ) w η hw
  let X:= Meadow.bouquet H d; let Y i:=(plays C χ γ i).logRead
  refine ⟨k,hk,fun i=>?_⟩
  rw [mix_eval]; by_cases hp:(pennant H i).2∈X
  · rw [show (fun t:sun=> (rates C χ γ d t).logRead i)=fun _ : sun => (0:Config G c→ℝ) from funext fun x=> by rw [rates,Meadow.compass,if_pos hp], show mix w (fun _ : sun=> (0:Config G c→ℝ))=0 from by simp [mix] ]
    exact ⟨VerifiedReset.reg_const 0,sup_le (VerifiedReset.sup_const 0) (by rw [abs_zero]; exact (hL i).2.1)⟩
  rw [show (fun t:sun=> (rates C χ γ d t).logRead i)=fun x => Y x i from funext fun x=> by rw [rates,Meadow.compass,if_neg hp]; rfl, ← mix_eval]; exact hL i
omit hr hp hv he
lemma postage {e:ℝ} (he:e ≤ preExponent P): league (fun i=> ((posting P H).hard i).support) P.B (fun i=> (plays C χ γ i).hardRead) e (v/2) (Tune.softW X L₀ a p):= by
  obtain ⟨k,hk,hX⟩:= h.loans
  let f:Refrain.Annual H→ℝ:= Sum.elim (fun i=>k i.val) fun _=>0
  have hv i V:Scout (v/2) (phraseS (fun t=> Refrain.fuse H (recital C t) χ i V)) (f i):=by
    rcases i with i|i
    · apply (hX i.val V).replace; intro i' hi; let v':sun:=⟨i',hi⟩
      rw [show phraseS _ i'=_ from phrased (fun t=> Refrain.fuse H (recital C t) χ _ V) v']; exact Tune.purse C χ V (C.beams i' (C.lay hi)) (recital C v') rfl _
    exact (Scout.still (by linarith [h.high]) (0:ℝ)).enlarged (by simp [f])
  refine ⟨f ∘ Refrain.badge H, fun i=>?_,fun i V=> hv (Refrain.badge H i) V⟩
  let D := Tune.softW X L₀ a p
  let f' j:= if i∈ (Refrain.reserve H j).support then f j * Real.exp (e*coverNumber P.B (Refrain.reserve H j).support) else 0
  refine Cost.equiv (Refrain.badge H) (show SumBudget f' D from ?_); rw [← add_zero D]
  refine Cost.sum ?_ (show SumBudget (fun i=> f' (.inr i)) 0 from by simp [f',f,SumBudget]) -- shadow locals
  have hk:= budget_pull (fun i:Refrain.Leaf H=>i.val) Subtype.val_injective (hk i)
  refine budget_mono hk (fun i=>?_) fun i=>?_
  · unfold f'; split
    · exact mul_nonneg (hv _ (1:Config G c)|>.nonneg) (Real.exp_nonneg _)
    rfl
  change (f' (.inl i)) ≤ if _ then _ else _
  unfold f'; split
  next hx=> rw [if_pos (show _∈H.library i.val from hx),hB]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (hv _ (1:Config G c)|>.nonneg)
  exact hk.1 i
end currents
end YM.PhysicalNext.Repeat.Jams
