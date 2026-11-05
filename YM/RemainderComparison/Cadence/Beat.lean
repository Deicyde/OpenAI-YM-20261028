import YM.RemainderComparison.Cadence.Vigor
/-! # Purchase AUTH discrepancy on all x. Polynomial window V.M. Uses raw polynomial insertion.
   Here '* analytic station up' already solved by classical interpretation on core from Φ. No β powers in thermal reservation before Epoch. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Herbal
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
section polar
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
    (f : ℝ×E→F) (x:E){i k n:ℕ}
lemma ringing (h:ContDiffAt ℝ i f ((0:ℝ),x)): Trace.coefficient f i x = (i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i (fun t:ℝ=> f (t,x)) 0 (fun _=>1):=by
     let L:=ContinuousLinearMap.inl ℝ ℝ E
     have hx (t:ℝ): (t,x)=(0,x)+L t:=by simp [L]
     rw [show (fun t:ℝ=> f (t,x))=fun y:ℝ=> f ((0,x)+L y) from funext fun y=> congr_arg f (hx y),Lantern.shift_affine _ _ _ _ ((hx 0) ▸ h),← hx,ContinuousMultilinearMap.compContinuousLinearMap_apply]; unfold Trace.coefficient Trace.plain; rfl -- L 1
variable {u:E→ℝ} (h:ContDiffAt ℝ ω u 0)
include h
lemma windward : Trace.coefficient (fun i:ℝ×E=>u (i.1 • i.2)) k x = (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k u 0 (fun _=>x):= by
    let L:= (ContinuousLinearMap.id ℝ ℝ).smulRight x; have hx : L (1:ℝ)=x:=by simp [L]
    rw [ringing _ x (by
       have he:(((0,x):ℝ×E).1 • ((0,x):ℝ×E).2)=0:=by simp
       exact ((he.symm ▸ h).of_le le_top).comp (f:=fun i:ℝ×E=>i.1 • i.2) _ (contDiffAt_fst.smul contDiffAt_snd))]
    change _ • iteratedFDeriv ℝ k (u ∘ L) 0 _ = _
    rw [linear_pull L (by rw [map_zero]; exact h.of_le le_top),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp only [hx]
variable {q R:ℝ}
def quota (R q:ℝ)(j:ℕ) := q*((1+R)*(1+R))*3^j
lemma paidP (hp:u 0=0) (he:iteratedFDeriv ℝ 1 u 0=0) (hq: normJ 2 u 0 ≤ q) (hx: ‖x‖ ≤ R) (hi:i≤2): Brush n (quota R q n) 1 (Trace.coefficient (fun i:ℝ×E=>u (i.1 • i.2)) i) x:=by
    rw [show Trace.coefficient _ i=fun x=> ((i.factorial:ℝ))⁻¹ • iteratedFDeriv ℝ i u 0 (fun _=> x) from funext fun x=> windward x h]
    have hq':0≤q:= (norm_nonneg _).trans hq; have hx':0≤R:= (norm_nonneg _).trans hx; have hW:0≤ quota R q n:=by unfold quota; positivity
    interval_cases i
    · simp_rw [iteratedFDeriv_zero_apply,hp,smul_zero]; exact (Brush.certified zero_le_one (x:=x) (0:ℝ)).climb (norm_zero.trans_le hW) le_rfl
    · simp_rw [he,_root_.zero_apply,smul_zero]; exact (Brush.certified zero_le_one (x:=x) (0:ℝ)).climb (norm_zero.trans_le hW) le_rfl
    let L:= fderiv ℝ (fderiv ℝ u) 0
    have hv:‖L‖≤q:=by unfold L; rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]; exact hq
    have hT : Brush n (1+R) 1 id x:= Brush.linearB (ContinuousLinearMap.id ℝ E) (hx.trans (le_add_of_nonneg_left zero_le_one)) (by rw [mul_one]; exact ContinuousLinearMap.norm_id_le.trans (le_add_of_nonneg_right hx')) zero_le_one
    have hm : Brush n (quota R q n) 1 (fun x=> iteratedFDeriv ℝ 2 u 0 (fun _=>x)) x:=by
        apply ((hT.twins hT L).trim.climb ?_ le_rfl).shimmy (Eventually.of_forall fun x=>by rw [iteratedFDeriv_two_apply]; rfl)
        unfold quota; rw [show (1:ℝ)+(1+1)=3 by norm_num]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (by positivity)) (by positivity)
    exact (hm.smul _).climb (mul_le_of_le_one_left hW (Trace.normalized_fact _)) le_rfl
end polar
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D σ' C' D' W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
variable {x:Positions (Uniform.Primary c G)}
variable (α₁ :ℝ)
local notation "f₀"=> Lapis.table F k' T.up T.high
local notation "F'"=> f₀ ∘ nod F ρ
local notation "H₁"=> (fun i:ℝ×Xs=> mainTerm T.low T.down (Herbal.sail F (Aux.nod F ρ i)))
local notation "H₂"=> (fun i:ℝ×Xs=> edict T.down T.low α₁ (Herbal.sail F (Aux.nod F ρ i)))
local notation "h₁"=> Shellac.hum F T Θ ρ k'
local notation "w"=> (show Xs→ℝ from h₁-(fun _=>h₁ 0))
local notation "iP"=> (fun x: Xs=> edict T.down T.low α₁ (represent (tint G _ x))-w x)
set_option quotPrecheck false
local notation "s"=> fun y:ℝ×Xs=>y.1 • y.2
variable (hP:T.up.Bounds T.high σ C D)(hQ:T.down.Bounds T.low σ' C' D')
    (hc:Critical F T.high T.up ρ) (hG:G.Simple) (hO:LocalRatio Θ)
    (he:S.patch.Branches S.kernel G) (h₀:0<a)(hgap:PriceGap F T.high T.up a)
    (hp:ClassicalMatch F T.high T.low T.up T.down ρ)
variable (G': Golf (Lapis.table F k' T.up T.high) (mist F Θ T.up) (Lapis.orbit F ρ)
    (Lapis.gram F T.up T.high ρ k') n W u u Z)
open Stationary WilsonStartup.Change
variable {T' M γ κ :ℝ}(hM:1≤ M)(hX:(Fintype.card (Uniform.Primary c G):ℝ) ≤ M) (hs:(Fintype.card (Site c):ℝ)≤ M)
   (H':FiniteBound F T.up T.down T.high T.low α₁ Θ ρ T' γ κ) (hg:0<T')(hK: 0≤κ)
include hp hP hQ hc hG hO hM hX hs G' he h₀ hgap H' hg hK
local notation "q" => tollS M 2 (Shellac.sailAmt M G*(T'*κ*Real.exp (-γ*c.val)))
local notation "V'"=> sprigs T.down T.low α₁
local notation "Vt"=> drafting T F Θ k' ρ
lemma visibility (u':ℝ)(ℓ:ℝ×Xs→ℝ) (hℓ:∀ p:Xs, ContDiffAt ℝ (2:ℕ) ℓ (0,p) ∧ ∀ i≤2,Trace.coefficient ℓ i p=Trace.coefficient (fun x:ℝ×Xs=> x.1^2*u') i p) (x:Xs) (hx:‖x‖ ≤ v): Portal.JMatch (ℓ-Vt) (aria F ρ (V' u')) x 2 j (quota v (q) j):=by
   let S':Xs→ℝ:=iP; obtain ⟨hA,h₁',h₂,h₃⟩:= rainy T F Θ k' ρ α₁ hP hQ hc hG hO he h₀ hgap G' hM hX hs H' hg hK
   let W:=w; let D:= fun x:Xs=> edict T.down T.low α₁ (represent (tint G _ x)); let ψ:= s
   have h : drafting T F Θ k' ρ= Trace.pending F' 1 + (W ∘ ψ):=by
      funext x; change _= Trace.pending F' 1 x+(h₁ (x.1 • x.2)-h₁ (0:Xs)); unfold Aux.drafting Aux.nod Shellac.hum Function.comp Germ.usage Germ.kite Lantern.visit; simp only [Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero]; abel
   rw [peaceful,h]; constructor; intro i hi
   refine (paidP (u:=iP) x hA h₁' h₂ h₃ hx hi).shimmy (Eventually.of_forall fun p=>?_)
   let k:= violet T F k' ρ hp p; let P:= (Trace.pending F' 1); let Q:= (Trace.pending H₁ 1); let L':=fun x:ℝ×Xs=> x.1^2*u'
   have hf : ContDiffAt ℝ (↑(2:ℕ)) P (0,p):= Trace.pContDiffAt (k.left.of_le le_top)
   have hg : ContDiffAt ℝ (↑(2:ℕ)) Q (0,p):= Trace.pContDiffAt (k.right.of_le le_top)
   have hy : ContDiffAt ℝ ω D 0:= pledge T α₁ hQ |>.1.left
   have ht : ContDiffAt ℝ ω ψ ((0:ℝ),p):= contDiffAt_fst.smul contDiffAt_snd
   have hk:ψ (0,p)=0:= zero_smul ℝ p
   have hr : W=D-S':=funext fun i=> (sub_sub_cancel ..).symm
   have hV : ContDiffAt ℝ (↑(2:ℕ)) (W ∘ ψ) (0,p):= by rw [hr]; exact ((hk.symm ▸ (hy.sub (show ContDiffAt ℝ ω S' 0 from hA))).comp (f:=ψ) _ ht).of_le le_top
   have hv : ContDiffAt ℝ (↑(2:ℕ)) H₂ (0,p):= ((hk.symm ▸ hy).comp (f:=ψ) _ ht).of_le le_top
   have hh : Trace.coefficient P i p= Trace.coefficient Q i p:= Trace.balances (k:=2) k hi
   let e z:=Trace.coefficient (F:=ℝ) z i p; have H y : S' (ψ y)=H₂ y-W (ψ y):= rfl
   change e (ℓ - (P+W ∘ ψ)) - e ((-Q-H₂) +L')=Trace.coefficient (S' ∘ ψ) i p -- comp ambiguity
   unfold e; rw [Trace.extracts_sub (g:=P+W ∘ ψ) (hℓ p).1 (hf.add hV) hi, (hℓ p).2 i hi,
       Trace.extracts_add (g:=W ∘ ψ) hf hV hi,Trace.extracts_add (f:= -Q-H₂) (hg.neg.sub hv) (g:=L') (contDiffAt_fst.pow 2|>.mul contDiffAt_const) hi,
       Trace.extracts_sub (f:=-Q) hg.neg hv hi,Trace.extracts_neg, hh, show S' ∘ ψ= H₂-(W ∘ ψ) from funext H, Trace.extracts_sub hv hV hi]; change _ - (_ - Trace.coefficient H₂ i p + Trace.coefficient L' i p)= _; abel
end YM.RemainderComparison.Cadence
